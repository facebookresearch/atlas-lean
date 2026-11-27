/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported from TauCetiProject/TauCeti (https://github.com/TauCetiProject/TauCeti) at revision
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean,
its complete initial projection section;
TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image.lean,
the complete image/composition API.
The copyright and license notice above are the source's.
Modification notice: retain the complete geometric projection consequences
without the first-order formula package; use the isolated MathlibExt
set/map ports. Closure under projection stays the hypothesis
`HasSemialgebraicProjections`; the source's proof of it over the reals (by cylindrical
algebraic decomposition) is not ported, and the real instance is a wanted statement in
`WantedExt/AlgebraicGeometry/SemialgebraicTrivialityWanted.lean`.
-/
module

public import MathlibExt.AlgebraicGeometry.SemialgebraicMaps
public import Mathlib.Data.Finset.Option
public import Mathlib.Basic.Finite.Sum

/-!
# General projection, image and composition contracts for semialgebraic maps

All operations concern actual finite Boolean polynomial sets and graphs.
The standing `HasSemialgebraicProjections R` is precisely coordinate
projection closure, not an arbitrary image operator. Tau's completed
CAD/Existence supplies it over the reals. Its transitive provider port is
tracked separately; no full real-theory proof is required to state a task.
-/

@[expose] public section

open Set MvPolynomial TauCeti

section Projection

variable {R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

namespace TauCeti

/-- **Projection in arbitrary dimension.** If semialgebraic subsets of `R ^ (n + 1)` have
semialgebraic projections to `R ^ n`, then for every index type `σ` the projection of a
semialgebraic subset of `Option σ → R`, forgetting the coordinate `none`, is semialgebraic. -/
theorem IsSemialgebraic.image_comp_some
    {σ : Type*} {s : Set (Option σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun x : Option σ → R => x ∘ some) '' s) := by
  classical
  -- `s` only depends on the coordinate `none` and the coordinates in a finite set `F`.
  obtain ⟨G, hG⟩ := hs.exists_finset_mem_iff_of_eqOn
  set F := G.eraseNone
  set e := F.equivFin
  -- Read off a point of `Option σ → R` from its coordinates `none` and `F`, listed in
  -- `Fin (F.card + 1)`; the other coordinates are set to zero.
  let g : Option σ → MvPolynomial (Fin (F.card + 1)) R := fun o =>
    o.elim (X 0) fun i => if h : i ∈ F then X (e ⟨i, h⟩).succ else 0
  set t := (fun y i => eval y (g i)) ⁻¹' s
  have hg (x : Option σ → R) (y : Fin (F.card + 1) → R) (h0 : y 0 = x none)
      (hF : ∀ i : F, y (e i).succ = x (some i)) : (fun i => eval y (g i)) ∈ s ↔ x ∈ s := by
    refine hG _ _ fun o ho => ?_
    cases o with
    | none => simpa [g] using h0
    | some i =>
      have hi : i ∈ F := Finset.mem_eraseNone.2 ho
      simpa [g, hi] using hF ⟨i, hi⟩
  convert (HasSemialgebraicProjections.isSemialgebraic_image_tail
    (hs.preimage_eval g)).preimage_comp fun j => (e.symm j : σ) using 1
  ext x
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Fin.cons (z none) (z ∘ some ∘ fun j => (e.symm j : σ)),
      (hg z _ rfl fun i => by simp).2 hz, Fin.tail_cons _ _⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨fun o => o.elim (y 0) x, (hg _ y rfl fun i => ?_).1 hy, rfl⟩
    simpa [Fin.tail] using congrFun hyx (e i)

end TauCeti

/-- The existential quantifier over the last of `n + 1` bound variables preserves
semialgebraicity, given projection closure. -/
private theorem TauCeti.IsSemialgebraic.setOf_exists_sumElim_snoc
    {α : Type*} {n : ℕ} {S : Set (α ⊕ Fin (n + 1) → R)} (hS : IsSemialgebraic S) :
    IsSemialgebraic
      {x : α ⊕ Fin n → R | ∃ a, Sum.elim (x ∘ Sum.inl) (Fin.snoc (x ∘ Sum.inr) a) ∈ S} := by
  -- Single out the last bound variable as the coordinate `none` of `Option (α ⊕ Fin n)`.
  let g : α ⊕ Fin (n + 1) → Option (α ⊕ Fin n) :=
    Sum.elim (some ∘ Sum.inl) (Fin.snoc (some ∘ Sum.inr) none)
  have hg (z : Option (α ⊕ Fin n) → R) :
      z ∘ g = Sum.elim (z ∘ some ∘ Sum.inl) (Fin.snoc (z ∘ some ∘ Sum.inr) (z none)) := by
    simp [g, Sum.comp_elim, Fin.comp_snoc]
  convert (hS.preimage_comp g).image_comp_some using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, mem_preimage, hg]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨fun o => o.elim a x, ha, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z none, hz⟩

end Projection


open MvPolynomial Set

namespace TauCeti

variable {σ τ υ R : Type*} [CommRing R] [LinearOrder R] [HasSemialgebraicProjections R]

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `σ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inr [Finite σ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s) := by
  revert τ
  refine Finite.induction_empty_option
    (P := fun σ => ∀ {τ : Type _} {s : Set (σ ⊕ τ → R)}, IsSemialgebraic s →
      IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inr) '' s))
    (fun {α β} e ih {τ} {s} hs => ?_) (fun {τ} {s} hs => ?_)
    (fun {α} _ ih {τ} {s} hs => ?_) σ
  · -- Transport along `e : α ≃ β` in the coordinates to be forgotten.
    convert ih (hs.preimage_comp (Equiv.sumCongr e.symm (Equiv.refl τ))) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z ∘ Equiv.sumCongr e (Equiv.refl τ), ?_, rfl⟩
      convert hz using 1
      ext (b | c) <;> simp
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, hz, rfl⟩
  · -- With no coordinates to forget, the projection is the bijection `Sum.inr`.
    convert hs.preimage_comp (Equiv.emptySum PEmpty τ) using 1
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      convert hz using 1
      ext (b | c)
      · exact b.elim
      · rfl
    · intro hy
      exact ⟨_, hy, rfl⟩
  · -- Forget the coordinate `none` with `IsSemialgebraic.image_comp_some`, then the coordinates
    -- `α` by induction.
    let k : Option α ⊕ τ → Option (α ⊕ τ) :=
      Sum.elim (Option.elim · none (some ∘ Sum.inl)) (some ∘ Sum.inr)
    convert ih (hs.preimage_comp k).image_comp_some using 1
    ext y
    simp only [mem_image, mem_preimage, exists_exists_and_eq_and]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(Option.elim · (z (.inl none)) (z ∘ Sum.elim (Sum.inl ∘ some) Sum.inr)), ?_, rfl⟩
      convert hz using 1
      ext ((_ | a) | c) <;> rfl
    · rintro ⟨w, hw, rfl⟩
      exact ⟨_, hw, rfl⟩

/-- Given projection closure, the projection of a semialgebraic subset of `σ ⊕ τ → R` that forgets
the finitely many coordinates `τ` is semialgebraic. -/
theorem IsSemialgebraic.image_comp_inl [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic ((fun z : σ ⊕ τ → R => z ∘ Sum.inl) '' s) := by
  convert (hs.preimage_comp (Equiv.sumComm σ τ)).image_comp_inr using 1
  ext y
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z ∘ Equiv.sumComm τ σ, ?_, rfl⟩
    convert hz using 1
    ext (a | b) <;> rfl
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, rfl⟩

/-- Existential quantification over finitely many coordinates preserves semialgebraicity. -/
theorem IsSemialgebraic.setOf_exists_sumElim [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic {x : σ → R | ∃ y : τ → R, Sum.elim x y ∈ s} := by
  convert hs.image_comp_inl using 1
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ∘ Sum.inr, by simpa using hz⟩

/-- Universal quantification over finitely many coordinates preserves semialgebraicity. -/
theorem IsSemialgebraic.setOf_forall_sumElim [Finite τ] {s : Set (σ ⊕ τ → R)}
    (hs : IsSemialgebraic s) :
    IsSemialgebraic {x : σ → R | ∀ y : τ → R, Sum.elim x y ∈ s} := by
  simpa only [compl_ofPred, mem_compl_iff, not_exists, not_not] using
    hs.compl.setOf_exists_sumElim.compl

/-- Given projection closure, the image of the domain of a semialgebraic function with finitely
many input coordinates is semialgebraic. -/
theorem IsSemialgebraicOn.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) : IsSemialgebraic (f '' s) := by
  convert hf.graph.image_comp_inr using 1
  ext y
  simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hfz⟩, rfl⟩
    exact ⟨_, hz, hfz⟩

/-- Given projection closure, the image of a semialgebraic set under a semialgebraic map with
finitely many input coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_image [Finite σ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (f '' s) :=
  (hf.isSemialgebraicOn hs).isSemialgebraic_image

/-- Given projection closure, the image of a semialgebraic set under a polynomial map with finitely
many input coordinates and finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraic.image_eval [Finite σ] [Finite τ] {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (p : τ → MvPolynomial σ R) :
    IsSemialgebraic ((fun x i => eval x (p i)) '' s) :=
  (isSemialgebraicOn_eval p hs).isSemialgebraic_image

/-- Given projection closure, the image of a semialgebraic set under a change of coordinates
`x ↦ x ∘ f`, such as a coordinate projection, is semialgebraic. -/
theorem IsSemialgebraic.image_comp [Finite σ] [Finite τ] {s : Set (σ → R)}
    (hs : IsSemialgebraic s) (f : τ → σ) :
    IsSemialgebraic ((fun x : σ → R => x ∘ f) '' s) := by
  simpa [Function.comp_def] using hs.image_eval fun i => X (f i)

/-- Given projection closure, the points of the domain of a semialgebraic function with finitely
many output coordinates at which it takes values in a semialgebraic set form a semialgebraic
set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} (hf : IsSemialgebraicOn f s) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (s ∩ f ⁻¹' t) := by
  convert (hf.graph.inter (ht.preimage_comp Sum.inr)).image_comp_inl using 1
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · rintro ⟨hx, hfx⟩
    exact ⟨Sum.elim x (f x), ⟨⟨hx, rfl⟩, hfx⟩, rfl⟩
  · rintro ⟨z, ⟨⟨hz, hfz⟩, hzt⟩, rfl⟩
    exact ⟨hz, by rw [mem_preimage, hfz]; exact hzt⟩

/-- Given projection closure, the inverse image of a semialgebraic set under a semialgebraic map
with finitely many output coordinates is semialgebraic. -/
theorem IsSemialgebraicMap.isSemialgebraic_preimage [Finite τ] {f : (σ → R) → (τ → R)}
    (hf : IsSemialgebraicMap f) {t : Set (τ → R)} (ht : IsSemialgebraic t) :
    IsSemialgebraic (f ⁻¹' t) := by
  simpa using (isSemialgebraicOn_univ.2 hf).isSemialgebraic_inter_preimage ht

/-- Given projection closure, a function with finitely many output coordinates is semialgebraic on
`s` if and only if its graph over `s` is semialgebraic: the domain `s` is the projection of the
graph. -/
theorem isSemialgebraicOn_iff_graph [Finite τ] {f : (σ → R) → (τ → R)} {s : Set (σ → R)} :
    IsSemialgebraicOn f s ↔
      IsSemialgebraic (Equiv.sumArrowEquivProdArrow σ τ R ⁻¹' s.graphOn f) := by
  refine ⟨IsSemialgebraicOn.graph, fun h => isSemialgebraicOn_def.2 ⟨?_, h⟩⟩
  convert h.image_comp_inl using 1
  ext x
  simp only [mem_image, mem_preimage_sumArrowEquivProdArrow_graphOn]
  constructor
  · intro hx
    exact ⟨Sum.elim x (f x), ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩
    exact hz

/-- Given projection closure, the composition of semialgebraic functions is semialgebraic: if `f`
is semialgebraic on `s` and maps it into `t`, and `g` is semialgebraic on `t`, then `g ∘ f` is
semialgebraic on `s`. The intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicOn.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    {s : Set (σ → R)} {t : Set (τ → R)} (hg : IsSemialgebraicOn g t)
    (hf : IsSemialgebraicOn f s) (hst : MapsTo f s t) : IsSemialgebraicOn (g ∘ f) s := by
  refine isSemialgebraicOn_def.2 ⟨hf.isSemialgebraic, ?_⟩
  -- In the coordinates `τ ⊕ (σ ⊕ υ)`, cut out the points `(f x, x, g (f x))` with `x ∈ s` and
  -- forget the intermediate coordinates `τ`.
  convert ((hf.graph.preimage_comp (Sum.elim (Sum.inr ∘ Sum.inl) Sum.inl)).inter
    (hg.graph.preimage_comp (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))).image_comp_inr using 1
  ext z
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn, mem_image]
  constructor
  · rintro ⟨hz, hgz⟩
    exact ⟨Sum.elim (f (z ∘ Sum.inl)) z,
      ⟨mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hz, rfl⟩,
        mem_preimage_sumArrowEquivProdArrow_graphOn.2 ⟨hst hz, hgz⟩⟩, rfl⟩
  · rintro ⟨w, ⟨hwf, hwg⟩, rfl⟩
    obtain ⟨hw, hfw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwf
    obtain ⟨-, hgw⟩ := mem_preimage_sumArrowEquivProdArrow_graphOn.1 hwg
    exact ⟨hw, (congrArg g hfw).trans hgw⟩

/-- Given projection closure, the composition of semialgebraic maps is semialgebraic when the
intermediate space has finitely many coordinates. -/
theorem IsSemialgebraicMap.comp [Finite τ] {g : (τ → R) → (υ → R)} {f : (σ → R) → (τ → R)}
    (hg : IsSemialgebraicMap g) (hf : IsSemialgebraicMap f) : IsSemialgebraicMap (g ∘ f) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hg).comp
    (isSemialgebraicOn_univ.2 hf) (mapsTo_univ f univ)

/-! ### Polynomial operations on semialgebraic functions -/

section Operations

variable {τ' : Type*} {f : (σ → R) → (τ → R)} {s : Set (σ → R)}

/-- Given projection closure, applying a polynomial map to the values of a semialgebraic function
with finitely many output coordinates gives a semialgebraic function. -/
theorem IsSemialgebraicOn.eval_comp [Finite τ] [Finite υ] (hf : IsSemialgebraicOn f s)
    (p : υ → MvPolynomial τ R) :
    IsSemialgebraicOn (fun x i => eval (f x) (p i)) s :=
  (isSemialgebraicOn_eval p isSemialgebraic_univ).comp hf (mapsTo_univ f s)

/-- Given projection closure, a pair of functions with finitely many output coordinates is
semialgebraic exactly when both of its components are. -/
@[simp]
theorem isSemialgebraicOn_sumElim_iff [Finite τ] [Finite τ'] {g : (σ → R) → (τ' → R)} :
    IsSemialgebraicOn (fun x => Sum.elim (f x) (g x)) s ↔
      IsSemialgebraicOn f s ∧ IsSemialgebraicOn g s := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => h.1.sumElim h.2⟩
  · simpa using h.eval_comp fun i : τ => X (Sum.inl i)
  · simpa using h.eval_comp fun i : τ' => X (Sum.inr i)

/-- Given projection closure, a function with finitely many output coordinates is semialgebraic on
`s` exactly when `s` is semialgebraic and each coordinate of the function is semialgebraic on
`s`. -/
theorem isSemialgebraicOn_pi_iff [Finite τ] :
    IsSemialgebraicOn f s ↔
      IsSemialgebraic s ∧ ∀ i, IsSemialgebraicOn (fun x (_ : Unit) => f x i) s := by
  refine ⟨fun h => ⟨h.isSemialgebraic, fun i => ?_⟩, fun h => .pi h.1 h.2⟩
  simpa using h.eval_comp fun _ : Unit => X i

variable [Finite τ] {g : (σ → R) → (τ → R)}

/-- Given projection closure, the pointwise sum of semialgebraic functions is semialgebraic. -/
theorem IsSemialgebraicOn.add (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f + g) s := by
  convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) + X (Sum.inr i) using 1
  funext x i
  simp

/-- Given projection closure, the pointwise product of semialgebraic functions is
semialgebraic. -/
theorem IsSemialgebraicOn.mul (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f * g) s := by
  convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) * X (Sum.inr i) using 1
  funext x i
  simp

/-- Given projection closure, the pointwise difference of semialgebraic functions is
semialgebraic. -/
theorem IsSemialgebraicOn.sub (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraicOn (f - g) s := by
  convert (hf.sumElim hg).eval_comp fun i : τ => X (Sum.inl i) - X (Sum.inr i) using 1
  funext x i
  simp

/-- Given projection closure, the pointwise sum of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.add (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f + g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).add (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the pointwise product of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.mul (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f * g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).mul (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the pointwise difference of semialgebraic maps is semialgebraic. -/
theorem IsSemialgebraicMap.sub (hf : IsSemialgebraicMap f) (hg : IsSemialgebraicMap g) :
    IsSemialgebraicMap (f - g) :=
  isSemialgebraicOn_univ.1 <| (isSemialgebraicOn_univ.2 hf).sub (isSemialgebraicOn_univ.2 hg)

/-- Given projection closure, the points of the common domain at which two semialgebraic
functions agree form a semialgebraic set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_eq (hf : IsSemialgebraicOn f s)
    (hg : IsSemialgebraicOn g s) : IsSemialgebraic (s ∩ {x | f x = g x}) := by
  convert (hf.sumElim hg).isSemialgebraic_inter_preimage
    (.iInter fun i : τ => isSemialgebraic_eval_eq (X (Sum.inl i)) (X (Sum.inr i))) using 2
  ext x
  simp [funext_iff]

/-- Given projection closure, the points of the common domain at which one semialgebraic function
is bounded above by another, coordinatewise, form a semialgebraic set. -/
theorem IsSemialgebraicOn.isSemialgebraic_inter_setOf_le [IsOrderedAddMonoid R]
    (hf : IsSemialgebraicOn f s) (hg : IsSemialgebraicOn g s) :
    IsSemialgebraic (s ∩ {x | f x ≤ g x}) := by
  convert (hf.sumElim hg).isSemialgebraic_inter_preimage
    (.iInter fun i : τ => isSemialgebraic_eval_le (X (Sum.inl i)) (X (Sum.inr i))) using 2
  ext x
  simp [Pi.le_def]

end Operations

end TauCeti
