/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Recognition from original good-path-object fibres

The converse recognition theorem keeps the original good path objects and
both pullback legs while deriving every positive homotopy-group bijection.
Connecting maps, their naturality, and the full Kan weak criterion are reused.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

attribute [local instance] SSet.modelCategoryQuillen.modelCategory

namespace SSet

private abbrev firstFibre {X : SSet.{u}} (P : PathObject X) (x : X _⦋0⦌) : SSet.{u} :=
  Subcomplex.fiber P.p₀ x

private def secondProjection {X : SSet.{u}} (P : PathObject X) (x : X _⦋0⦌) :
    firstFibre P x ⟶ X := (Subcomplex.fiber P.p₀ x).ι ≫ P.p₁

private theorem firstFibre_square {X : SSet.{u}} (P : PathObject X)
    (x : X _⦋0⦌) :
    IsPullback (Subcomplex.fiber P.p₀ x).ι (secondProjection P x)
      P.p (prod.lift (const (X := X) x) (𝟙 X)) := by
  have hw : (Subcomplex.fiber P.p₀ x).ι ≫ P.p =
      secondProjection P x ≫ prod.lift (const (X := X) x) (𝟙 X) := by
    apply prod.hom_ext
    · simp only [Category.assoc, PrepathObject.p_fst, prod.lift_fst,
        Subcomplex.fiber_ι_comp, comp_const]
    · simp only [Category.assoc, PrepathObject.p_snd, prod.lift_snd,
        Category.comp_id, secondProjection]
  have hrange (s : PullbackCone P.p (prod.lift (const (X := X) x) (𝟙 X))) :
      Subcomplex.range s.fst ≤ Subcomplex.fiber P.p₀ x := by
    apply (Subcomplex.range_le_fiber_iff P.p₀ x s.fst).mpr
    have h := s.condition =≫ (prod.fst : X ⨯ X ⟶ X)
    simpa only [Category.assoc, PrepathObject.p_fst, prod.lift_fst,
      comp_const] using h
  refine { w := hw, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk hw
    (fun s => Subcomplex.lift s.fst (hrange s))
    (fun s => Subcomplex.lift_ι _ _)
    (fun s => ?_) (fun s m hm _ => ?_)⟩
  · change Subcomplex.lift s.fst (hrange s) ≫
        (Subcomplex.fiber P.p₀ x).ι ≫ P.p₁ = s.snd
    rw [← Category.assoc, Subcomplex.lift_ι]
    have h := s.condition =≫ (prod.snd : X ⨯ X ⟶ X)
    simpa only [Category.assoc, PrepathObject.p_snd, prod.lift_snd,
      Category.comp_id] using h
  · apply (cancel_mono (Subcomplex.fiber P.p₀ x).ι).mp
    rw [hm, Subcomplex.lift_ι]

private abbrev basedSequence {X : SSet.{u}} [KanComplex X]
    (P : PathObject X) [P.IsGood] (x : X _⦋0⦌) : FibrationSequence.{u} := by
  let : Fibration (secondProjection P x) := by
    rw [modelCategoryQuillen.fibration_iff]
    exact (modelCategoryQuillen.J.rlp).of_isPullback (firstFibre_square P x)
      ((modelCategoryQuillen.fibration_iff P.p).mp inferInstance)
  let e : firstFibre P x _⦋0⦌ := Subcomplex.fiber.basePoint (P.ι.app _ x) (by
    exact ConcreteCategory.congr_hom (congr_app P.ι_p₀ (op ⦋0⦌)) x)
  refine
    { E := firstFibre P x
      B := X
      p := secondProjection P x
      fibration_p := inferInstance
      fibrant_B := inferInstance
      e := e
      b := x
      hb := ?_ }
  change P.p₁.app (op ⦋0⦌) (P.ι.app (op ⦋0⦌) x) = x
  exact ConcreteCategory.congr_hom (congr_app P.ι_p₁ (op ⦋0⦌)) x

private theorem iteratedFibre_square {X : SSet.{u}} [KanComplex X]
    (P : PathObject X) [P.IsGood] (x y : X _⦋0⦌) :
    IsPullback ((Subcomplex.fiber (basedSequence P x).p y).ι ≫
      (Subcomplex.fiber P.p₀ x).ι)
      (stdSimplex.isTerminalObj₀.from (Subcomplex.fiber (basedSequence P x).p y : SSet.{u}))
      P.p (prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)) := by
  have h := (Subcomplex.fiber_isPullback (basedSequence P x).p y).paste_horiz
    (firstFibre_square P x)
  have he : const (X := Δ[0]) y ≫ prod.lift (const (X := X) x) (𝟙 X) =
      prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, comp_const, yonedaEquiv_symm_zero]
    · simp only [Category.assoc, prod.lift_snd, Category.comp_id, yonedaEquiv_symm_zero]
  convert h using 1
  exact he.symm

private def iteratedFibreIso {X : SSet.{u}} [KanComplex X]
    (P : PathObject X) [P.IsGood] (x y : X _⦋0⦌) :
    (Subcomplex.fiber (basedSequence P x).p y : SSet.{u}) ≅
      pullback P.p (prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)) :=
  (iteratedFibre_square P x y).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

private theorem iteratedFibreIso_legs {X : SSet.{u}} [KanComplex X]
    (P : PathObject X) [P.IsGood] (x y : X _⦋0⦌) :
    let e := iteratedFibreIso P x y
    e.hom ≫ pullback.fst _ _ = (Subcomplex.fiber (basedSequence P x).p y).ι ≫
        (Subcomplex.fiber P.p₀ x).ι ∧
    e.hom ≫ pullback.snd _ _ = stdSimplex.isTerminalObj₀.from _ ∧
    e.inv ≫ (Subcomplex.fiber (basedSequence P x).p y).ι ≫
        (Subcomplex.fiber P.p₀ x).ι = pullback.fst _ _ ∧
    e.inv ≫ stdSimplex.isTerminalObj₀.from _ = pullback.snd _ _ := by
  exact ⟨(iteratedFibre_square P x y).isoIsPullback_hom_fst _ _ _,
    (iteratedFibre_square P x y).isoIsPullback_hom_snd _ _ _,
    (iteratedFibre_square P x y).isoIsPullback_inv_fst _ _ _,
    (iteratedFibre_square P x y).isoIsPullback_inv_snd _ _ _⟩

private abbrev basedSequenceMap {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (P : PathObject X) (Q : PathObject Y) [P.IsGood] [Q.IsGood]
    (a : P.P ⟶ Q.P) (hi : P.ι ≫ a = f ≫ Q.ι)
    (h0 : a ≫ Q.p₀ = P.p₀ ≫ f) (h1 : a ≫ Q.p₁ = P.p₁ ≫ f)
    (x : X _⦋0⦌) : FibrationSequenceHom (basedSequence P x)
      (basedSequence Q (f.app _ x)) := by
  let m := Subcomplex.mapFiber (f := P.p₀) (f' := Q.p₀) a f h0 (y := x) rfl
  refine { totalMap := m, baseMap := f, comm := ?_, total_pt := ?_, base_pt := rfl }
  · change m ≫ (Subcomplex.fiber Q.p₀ (f.app _ x)).ι ≫ Q.p₁ =
        (Subcomplex.fiber P.p₀ x).ι ≫ P.p₁ ≫ f
    rw [← Category.assoc, Subcomplex.mapFiber_ι, Category.assoc, h1]
  · apply Subtype.ext
    exact ConcreteCategory.congr_hom (congr_app hi (op ⦋0⦌)) x

private theorem iteratedFibreIso_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (P : PathObject X) (Q : PathObject Y) [P.IsGood] [Q.IsGood]
    (a : P.P ⟶ Q.P) (hi : P.ι ≫ a = f ≫ Q.ι)
    (h0 : a ≫ Q.p₀ = P.p₀ ≫ f) (h1 : a ≫ Q.p₁ = P.p₁ ≫ f)
    (x y : X _⦋0⦌) :
    let F := basedSequenceMap f P Q a hi h0 h1 x
    let m := Subcomplex.mapFiber F.totalMap f F.comm (y := y) rfl
    let c := pullback.map P.p (prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))
      Q.p (prod.lift (yonedaEquiv.symm (f.app _ x)) (yonedaEquiv.symm (f.app _ y)))
      a (𝟙 (Δ[0] : SSet.{u})) (prod.map f f)
      (by apply prod.hom_ext <;> simp only [Category.assoc,
        PrepathObject.p_fst, PrepathObject.p_snd, PrepathObject.p_fst_assoc,
          PrepathObject.p_snd_assoc, prod.map_fst, prod.map_snd, h0, h1])
      (by apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst,
        prod.lift_snd, prod.lift_fst_assoc, prod.lift_snd_assoc,
          prod.map_fst, prod.map_snd, yonedaEquiv_symm_comp,
        Category.id_comp])
    m ≫ (iteratedFibreIso Q (f.app _ x) (f.app _ y)).hom =
      (iteratedFibreIso P x y).hom ≫ c := by
  dsimp only
  apply pullback.hom_ext
  · simpa only [Category.assoc, (iteratedFibreIso_legs Q _ _).1,
      Subcomplex.mapFiber_ι_assoc, Subcomplex.mapFiber_ι, pullback.map, pullback.lift_fst] using
      congrArg (fun k => k ≫ a) (iteratedFibreIso_legs P x y).1.symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem terminal_pi_subsingleton (n : ℕ)
    (z : (Δ[0] : SSet.{u}) _⦋0⦌) :
    Subsingleton (KanComplex.π n (Δ[0] : SSet.{u}) z) := by
  constructor
  intro a b
  induction a using KanComplex.π.rec with
  | mk p =>
    induction b using KanComplex.π.rec with
    | mk q =>
      have hpq : p = q := RelativeMorphism.ext (stdSimplex.isTerminalObj₀.hom_ext _ _)
      rw [hpq]

private theorem basedSequence_pi_subsingleton
    {X : SSet.{u}} [KanComplex X] (P : PathObject X) [P.IsGood]
    (x : X _⦋0⦌) (n : ℕ) :
    Subsingleton (KanComplex.π n (basedSequence P x).E (basedSequence P x).e) := by
  let t := stdSimplex.isTerminalObj₀.from (firstFibre P x)
  let : Fibration t := by
    rw [modelCategoryQuillen.fibration_iff]
    exact (modelCategoryQuillen.J.rlp).of_isPullback (Subcomplex.fiber_isPullback P.p₀ x)
      ((modelCategoryQuillen.fibration_iff P.p₀).mp inferInstance)
  let : KanComplex (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 _) stdSimplex.isTerminalObj₀).2 (by infer_instance)
  let : KanComplex (firstFibre P x) := isFibrant_of_fibration t
  have hP : realizationWeakEquivalences P.p₀ :=
    (weakEquivalence_iff P.p₀).mp inferInstance
  have htI : modelCategoryQuillen.I.rlp t :=
    (modelCategoryQuillen.I.rlp).of_isPullback (Subcomplex.fiber_isPullback P.p₀ x)
      ((modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration P.p₀).mpr hP)
  have ht : KanComplex.W t := (KanComplex.W_iff_realizationWeakEquivalence t).mpr
    ((modelCategoryQuillen.I_rlp_iff_realizationWeakEquivalence_of_fibration t).mp htI)
  constructor
  intro a b
  apply (ht.bijective_piMap n (basedSequence P x).e).1
  exact (terminal_pi_subsingleton n (t.app _ (basedSequence P x).e)).elim _ _

private theorem weak_pi_bijective_at {A B : SSet.{u}} {g : A ⟶ B}
    (hg : KanComplex.W g) {x : A _⦋0⦌} {y : B _⦋0⦌}
    (hy : g.app _ x = y) (n : ℕ) :
    Function.Bijective (KanComplex.π.map g hy n) := by
  subst y
  exact hg.bijective_piMap n x

@[expose] public section

/-- An original map of Kan complexes is realization-weak if it is bijective
on components and weak on the diagonal fibres of actual good path objects.
The path-object map need not be weak, and the original map need not be a
fibration. The same diagonal fibres detect all positive homotopy groups. -/
theorem realizationWeakEquivalence_of_goodPathObjectDiagonalFibres
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    (P : PathObject X) (Q : PathObject Y) [P.IsGood] [Q.IsGood]
    (a : P.P ⟶ Q.P) (hi : P.ι ≫ a = f ≫ Q.ι)
    (h0 : a ≫ Q.p₀ = P.p₀ ≫ f) (h1 : a ≫ Q.p₁ = P.p₁ ≫ f)
    (hc : Function.Bijective (mapπ₀ f))
    (hf : ∀ x : X _⦋0⦌, realizationWeakEquivalences
      (pullback.map P.p (prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm x))
        Q.p (prod.lift (yonedaEquiv.symm (f.app _ x)) (yonedaEquiv.symm (f.app _ x)))
        a (𝟙 (Δ[0] : SSet.{u})) (prod.map f f)
        (by apply prod.hom_ext <;> simp only [Category.assoc,
          PrepathObject.p_fst, PrepathObject.p_snd, PrepathObject.p_fst_assoc,
          PrepathObject.p_snd_assoc, prod.map_fst, prod.map_snd, h0, h1])
        (by apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst,
          prod.lift_snd, prod.lift_fst_assoc, prod.lift_snd_assoc,
          prod.map_fst, prod.map_snd, yonedaEquiv_symm_comp,
          Category.id_comp]))) :
    realizationWeakEquivalences f := by
  apply (KanComplex.W_iff_realizationWeakEquivalence f).mp
  apply (KanComplex.W_iff f).mpr
  refine ⟨hc, ?_⟩
  intro n x
  let S := basedSequence P x
  let T := basedSequence Q (f.app _ x)
  let F := basedSequenceMap f P Q a hi h0 h1 x
  let _ : KanComplex S.fiber := FibrationSequence.isFibrant_fiber S
  let _ : KanComplex T.fiber := FibrationSequence.isFibrant_fiber T
  have hF : KanComplex.W F.fiberMap := by
    apply (KanComplex.W_iff_realizationWeakEquivalence F.fiberMap).mpr
    let e : Arrow.mk F.fiberMap ≅ Arrow.mk _ :=
      Arrow.isoMk (iteratedFibreIso P x x)
      (iteratedFibreIso Q (f.app _ x) (f.app _ x))
      (iteratedFibreIso_naturality f P Q a hi h0 h1 x x).symm
    exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mpr (hf x)
  have hs := S.connectingMap_bijective_of_subsingleton_total
    (fun k => basedSequence_pi_subsingleton P x k) n
  have ht := T.connectingMap_bijective_of_subsingleton_total
    (fun k => basedSequence_pi_subsingleton Q (f.app _ x) k) n
  have hloop := weak_pi_bijective_at hF F.fiberMap_app_basePoint n
  have hn (p : KanComplex.π (n + 1) X x) :
      KanComplex.π.map F.fiberMap F.fiberMap_app_basePoint n (S.connectingMap n p) =
        T.connectingMap n (KanComplex.π.map f rfl (n + 1) p) :=
    FibrationSequence.connectingMap_naturality F p
  constructor
  · intro p q hpq
    apply hs.1
    apply hloop.1
    rw [hn, hn, hpq]
  · intro q
    obtain ⟨b, hb⟩ := hloop.2 (T.connectingMap n q)
    obtain ⟨p, hp⟩ := hs.2 b
    refine ⟨p, ht.1 ?_⟩
    rw [← hn, hp, hb]

/-- Convenience form of the diagonal-fibre detector with weak equivalences
on every original path-object fibre. Only its diagonal specializations are
needed to detect realization weakness. -/
theorem realizationWeakEquivalence_of_goodPathObjectFibres
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    (P : PathObject X) (Q : PathObject Y) [P.IsGood] [Q.IsGood]
    (a : P.P ⟶ Q.P) (hi : P.ι ≫ a = f ≫ Q.ι)
    (h0 : a ≫ Q.p₀ = P.p₀ ≫ f) (h1 : a ≫ Q.p₁ = P.p₁ ≫ f)
    (hc : Function.Bijective (mapπ₀ f))
    (hf : ∀ x y : X _⦋0⦌, realizationWeakEquivalences
      (pullback.map P.p (prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))
        Q.p (prod.lift (yonedaEquiv.symm (f.app _ x)) (yonedaEquiv.symm (f.app _ y)))
        a (𝟙 (Δ[0] : SSet.{u})) (prod.map f f)
        (by apply prod.hom_ext <;> simp only [Category.assoc,
          PrepathObject.p_fst, PrepathObject.p_snd, PrepathObject.p_fst_assoc,
          PrepathObject.p_snd_assoc, prod.map_fst, prod.map_snd, h0, h1])
        (by apply prod.hom_ext <;> simp only [Category.assoc, prod.lift_fst,
          prod.lift_snd, prod.lift_fst_assoc, prod.lift_snd_assoc,
          prod.map_fst, prod.map_snd, yonedaEquiv_symm_comp,
          Category.id_comp]))) :
    realizationWeakEquivalences f :=
  realizationWeakEquivalence_of_goodPathObjectDiagonalFibres f P Q a hi h0 h1 hc
    (fun x => hf x x)

end

end SSet
