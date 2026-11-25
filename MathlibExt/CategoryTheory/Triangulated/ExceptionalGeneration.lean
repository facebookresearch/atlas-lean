/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/CategoryTheory/Triangulated/ExceptionalCollectionFiniteness.lean`
(AxiomMath/Stacks at commit c496df0d9beea9deaeabcea8492605f9a0a2313b,
https://github.com/AxiomMath/Stacks). The whole file is copied from that source, which has no
individual copyright or author notice:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modification notice: moved to MathlibExt without any Stacks dependency, with the original names;
`postComp` is an alias of Mathlib's `Linear.rightComp`, and the documentation of `totalDim`,
of orthogonality and of the hypotheses of the main theorem is corrected.
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Objects with finite total `Hom` from a full exceptional sequence

Let `k` be a field and let `C` be a `k`-linear pretriangulated category whose shift functors
are `k`-linear. Let `G₀, …, G_{r-1}` be objects of `C` such that

* every endomorphism of each `G_a` is a scalar multiple of the identity, and
  `Hom(G_a, G_a⟦n⟧) = 0` for `n ≠ 0` (this holds for exceptional objects);
* the sequence is *semi-orthogonal*: `Hom(G_b, G_a⟦n⟧) = 0` for `a < b` and every `n`;
* the sequence *generates* `C`: an object `M` with `Hom(G_a, M⟦n⟧) = 0` for all `a` and `n` is
  zero;
* `∑_n dim_k Hom(G_a, G_b⟦n⟧) < ∞` for `a < b`.

Then every object `M` with `∑_n dim_k Hom(G_a, M⟦n⟧) < ∞` for every `a` lies in every
triangulated subcategory (closed under isomorphisms) which contains the `G_a`. This is the
standard argument with a full exceptional sequence: map a finite sum of shifts of the last
object `G_{r-1}` onto `M` by a basis of the `Hom`-spaces, so that the cone is right orthogonal
to `G_{r-1}`, and induct on the length of the sequence.

It is the abstract part of the projective-space case of [Stacks, Tag 0FYB] (with the sequence
`𝒪(-n), …, 𝒪` on `ℙⁿ_k`).

## Main definitions

* `CategoryTheory.Pretriangulated.HasFiniteTotalHom`: `∑_n dim_k Hom(A, X⟦n⟧) < ∞`, spelled as:
  every `Hom(A, X⟦n⟧)` is a finite `k`-module and only finitely many are nonzero.

## Main results

* `CategoryTheory.Pretriangulated.prop_of_hasFiniteTotalHom_of_exceptional`: the statement
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

universe w v u

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [Linear k C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

/-- `∑_{n ∈ ℤ} dim_k Hom(A, X⟦n⟧) < ∞`: every `Hom(A, X⟦n⟧)` is a finite `k`-module and only
finitely many of them are nonzero. -/
def HasFiniteTotalHom (A X : C) : Prop :=
  (∀ n : ℤ, Module.Finite k (A ⟶ X⟦n⟧)) ∧ {n : ℤ | Nontrivial (A ⟶ X⟦n⟧)}.Finite

namespace ExceptionalAux

/-- Moving a shift from the target to the source of a morphism is `k`-linear. -/
def homShiftLinearEquiv (A X : C) (n : ℤ) : (A⟦-n⟧ ⟶ X) ≃ₗ[k] (A ⟶ X⟦n⟧) where
  toFun f := (shiftFunctorCompIsoId C (-n) n (by omega)).inv.app A ≫ f⟦n⟧'
  invFun g :=
    (shiftFunctor C n).preimage ((shiftFunctorCompIsoId C (-n) n (by omega)).hom.app A ≫ g)
  left_inv f := by
    apply (shiftFunctor C n).map_injective
    simp
  right_inv g := by simp
  map_add' f g := by simp
  map_smul' c f := by simp

variable {k}

/-- `X` is right orthogonal to all shifts of `A`: `Hom(A⟦n⟧, X) = 0` for every `n`. -/
def Orth (A X : C) : Prop := ∀ n : ℤ, Subsingleton (A⟦n⟧ ⟶ X)

variable (k) in
/-- `HasFiniteTotalHom` with the shift on the source. -/
def FinTot (A X : C) : Prop :=
  (∀ n : ℤ, Module.Finite k (A⟦n⟧ ⟶ X)) ∧ {n : ℤ | Nontrivial (A⟦n⟧ ⟶ X)}.Finite

/-- The linear identification `Hom(A⟦n⟧, X) ≃ Hom(A, X⟦-n⟧)`. -/
private def homShiftNegLinearEquiv (A X : C) (n : ℤ) : (A⟦n⟧ ⟶ X) ≃ₗ[k] (A ⟶ X⟦-n⟧) := by
  have e := homShiftLinearEquiv k A X (-n)
  rw [neg_neg] at e
  exact e

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A `Hom` group all of whose elements are zero is a subsingleton. -/
lemma subsingleton_of_forall_eq_zero {A X : C} (h : ∀ f : A ⟶ X, f = 0) :
    Subsingleton (A ⟶ X) := ⟨fun f g => by rw [h f, h g]⟩

omit [HasZeroObject C] [Pretriangulated C] in
/-- The source-shift and target-shift forms of finite total `Hom` agree. -/
lemma finTot_iff (A X : C) : FinTot k A X ↔ HasFiniteTotalHom k A X := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun n => Module.Finite.equiv (homShiftLinearEquiv k A X n), ?_⟩
    refine (h2.image (fun n => -n)).subset fun n hn => ⟨-n, ?_, by simp⟩
    have : Nontrivial (A ⟶ X⟦n⟧) := hn
    exact (homShiftLinearEquiv k A X n).toEquiv.nontrivial
  · rintro ⟨h1, h2⟩
    refine ⟨fun n => ?_, ?_⟩
    · have := h1 (-n)
      exact Module.Finite.equiv (homShiftNegLinearEquiv (k := k) A X n).symm
    · refine (h2.image (fun n => -n)).subset fun n hn => ⟨-n, ?_, by simp⟩
      have : Nontrivial (A⟦n⟧ ⟶ X) := hn
      exact (homShiftNegLinearEquiv (k := k) A X n).symm.toEquiv.nontrivial

omit [HasZeroObject C] [Pretriangulated C] in
variable (k) in
include k in
/-- `X` is right orthogonal to all shifts of `A` if and only if `Hom(A, X⟦n⟧)` is trivial for
every `n`. -/
lemma orth_iff (A X : C) : Orth A X ↔ ∀ n : ℤ, Subsingleton (A ⟶ X⟦n⟧) := by
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · have := h (-n)
    exact (homShiftLinearEquiv k A X n).symm.toEquiv.subsingleton
  · have := h (-n)
    exact (homShiftNegLinearEquiv (k := k) A X n).toEquiv.subsingleton

/-- The linear identification `Hom(A⟦n⟧, X⟦m⟧) ≃ Hom(A⟦n - m⟧, X)`. -/
def homShiftShiftLinearEquiv (A X : C) (n m : ℤ) :
    (A⟦n⟧ ⟶ X⟦m⟧) ≃ₗ[k] (A⟦n - m⟧ ⟶ X) :=
  (homShiftLinearEquiv k (A⟦n⟧) X m).symm ≪≫ₗ
    Linear.homCongr k ((shiftFunctorAdd' C n (-m) (n - m) (by omega)).app A).symm (Iso.refl X)

omit [HasZeroObject C] [Pretriangulated C] in
variable (k) in
include k in
/-- Right orthogonality to all shifts of `A` is preserved by shifting the target. -/
lemma orth_shift {A X : C} (h : Orth A X) (m : ℤ) : Orth A (X⟦m⟧) := fun n =>
  have := h (n - m)
  (homShiftShiftLinearEquiv (k := k) A X n m).toEquiv.subsingleton

omit [HasZeroObject C] [Pretriangulated C] in
/-- Finite total `Hom` from `A` is preserved by shifting the target. -/
lemma finTot_shift {A X : C} (h : FinTot k A X) (m : ℤ) : FinTot k A (X⟦m⟧) := by
  refine ⟨fun n => ?_, ?_⟩
  · have := h.1 (n - m)
    exact Module.Finite.equiv (homShiftShiftLinearEquiv (k := k) A X n m).symm
  · refine (h.2.image (fun n => n + m)).subset fun n hn => ⟨n - m, ?_, by simp⟩
    have : Nontrivial (A⟦n⟧ ⟶ X⟦m⟧) := hn
    exact (homShiftShiftLinearEquiv (k := k) A X n m).symm.toEquiv.nontrivial

/-- In a distinguished triangle, a `Hom` group into the third object is trivial if the ones into
the second object and the shifted first object are. -/
private lemma subsingleton_obj₃ (T : Triangle C) (hT : T ∈ distTriang C) {B : C}
    (h₂ : Subsingleton (B ⟶ T.obj₂)) (h₁ : Subsingleton (B ⟶ T.obj₁⟦(1 : ℤ)⟧)) :
    Subsingleton (B ⟶ T.obj₃) :=
  subsingleton_of_forall_eq_zero fun f => by
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ T hT f (h₁.elim _ _)
    rw [h₂.elim g 0, zero_comp]

/-- In a distinguished triangle, orthogonality passes to the third object from the second one
and the shifted first one. -/
lemma orth_obj₃ (T : Triangle C) (hT : T ∈ distTriang C) {A : C} (h₂ : Orth A T.obj₂)
    (h₁ : Orth A (T.obj₁⟦(1 : ℤ)⟧)) : Orth A T.obj₃ := fun n =>
  subsingleton_obj₃ T hT (h₂ n) (h₁ n)

/-- Post-composition with a fixed morphism, as a `k`-linear map: Mathlib's
`Linear.rightComp`. -/
abbrev postComp {X Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →ₗ[k] (X ⟶ Z) :=
  Linear.rightComp k X g

omit [∀ n : ℤ, (shiftFunctor C n).Linear k] in
variable (k) in
/-- In a distinguished triangle, finite total `Hom` passes to the third object from the second
one and the shifted first one. -/
lemma finTot_obj₃ (T : Triangle C) (hT : T ∈ distTriang C) {A : C} (h₂ : FinTot k A T.obj₂)
    (h₁ : FinTot k A (T.obj₁⟦(1 : ℤ)⟧)) : FinTot k A T.obj₃ := by
  refine ⟨fun n => ?_, ?_⟩
  · have := h₁.1 n
    have := h₂.1 n
    let ψ := postComp (k := k) (X := A⟦n⟧) T.mor₃
    let χ := postComp (k := k) (X := A⟦n⟧) T.mor₂
    refine Module.Finite.of_exact (f := χ) (g := ψ.rangeRestrict) (fun y => ⟨fun hy => ?_, ?_⟩)
      ψ.surjective_rangeRestrict
    · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT y (congrArg Subtype.val hy)
      exact ⟨g, hg.symm⟩
    · rintro ⟨g, rfl⟩
      apply Subtype.ext
      change (g ≫ T.mor₂) ≫ T.mor₃ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]
  · refine (h₂.2.union h₁.2).subset fun n hn => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨hs₂, hs₁⟩ := hnot
    exact (not_nontrivial_iff_subsingleton.mpr (subsingleton_obj₃ T hT hs₂ hs₁)) hn

/-! ### Killing one exceptional object -/

section Kill

variable (k) in
/-- The sum `∑ᶠ n, dim_k Hom(G⟦n⟧, X)`. It is the total dimension of the graded `Hom` when
`FinTot k G X` holds, and it is only used under that hypothesis: otherwise `Module.finrank`
of an infinite-dimensional piece and the `finsum` of an infinite support are `0`. -/
def totalDim (G X : C) : ℕ := ∑ᶠ n : ℤ, Module.finrank k (G⟦n⟧ ⟶ X)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- `dim_k Hom(G⟦n⟧, X)` is nonzero only where `Hom(G⟦n⟧, X)` is nontrivial. -/
lemma support_finrank_subset (G X : C) :
    Function.support (fun n : ℤ => Module.finrank k (G⟦n⟧ ⟶ X)) ⊆
      {n : ℤ | Nontrivial (G⟦n⟧ ⟶ X)} := by
  intro n hn
  by_contra h
  rw [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton] at h
  exact hn Module.finrank_zero_of_subsingleton

variable {G : C} (hG0 : ∀ e : G ⟶ G, ∃ c : k, e = c • 𝟙 G)
  (hG1 : ∀ n : ℤ, n ≠ 0 → Subsingleton (G⟦n⟧ ⟶ G))

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
include hG0 in
/-- Every endomorphism of a shift `G⟦m⟧` of `G` is a scalar multiple of the identity. -/
lemma exists_smul_id_shift (m : ℤ) (e : G⟦m⟧ ⟶ G⟦m⟧) : ∃ c : k, e = c • 𝟙 _ := by
  obtain ⟨c, hc⟩ := hG0 ((shiftFunctor C m).preimage e)
  refine ⟨c, ?_⟩
  rw [← (shiftFunctor C m).map_preimage e, hc, Functor.map_smul, Functor.map_id]

omit [HasZeroObject C] [Pretriangulated C] in
variable (k) in
include k hG1 in
/-- `Hom(G⟦n⟧, G⟦m⟧)` is trivial for `n ≠ m`. -/
lemma subsingleton_shift_shift (n m : ℤ) (h : n ≠ m) : Subsingleton (G⟦n⟧ ⟶ G⟦m⟧) :=
  have := hG1 (n - m) (by omega)
  (homShiftShiftLinearEquiv (k := k) G G n m).toEquiv.subsingleton

include hG0 hG1 in
/-- **The cone of a nonzero map from a shift of `G` has strictly smaller total `Hom` from `G`.**
For a distinguished triangle `G⟦a⟧ ⟶ M ⟶ Z ⟶ G⟦a⟧⟦1⟧` whose first map is nonzero, every
morphism `G⟦n⟧ ⟶ Z` lifts to `M`, and the first map itself dies in `Z`. -/
lemma finTot_and_totalDim_lt {a : ℤ} {M Z : C} (f : G⟦a⟧ ⟶ M) (g : M ⟶ Z)
    (h : Z ⟶ (G⟦a⟧)⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ distTriang C) (hf : f ≠ 0)
    (hM : FinTot k G M) : FinTot k G Z ∧ totalDim k G Z < totalDim k G M := by
  let ι : G⟦a + 1⟧ ≅ (G⟦a⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd' C a 1 (a + 1) rfl).app G
  have hlift : ∀ (n : ℤ) (u : G⟦n⟧ ⟶ Z), ∃ v : G⟦n⟧ ⟶ M, u = v ≫ g := by
    intro n u
    have hu : u ≫ h = 0 := by
      by_cases hn : n = a + 1
      · subst hn
        obtain ⟨c, hc⟩ := exists_smul_id_shift hG0 (a + 1) (u ≫ h ≫ ι.inv)
        have hc' : u ≫ h = c • ι.hom := by
          rw [← Category.comp_id (u ≫ h), ← ι.inv_hom_id, ← Category.assoc, Category.assoc u,
            hc, Linear.smul_comp, Category.id_comp]
        have hz : (u ≫ h) ≫ f⟦(1 : ℤ)⟧' = 0 := by
          rw [Category.assoc]
          have := comp_distTriang_mor_zero₃₁ _ hT
          simp only [Triangle.mk_mor₃, Triangle.mk_mor₁] at this
          rw [this, comp_zero]
        rw [hc', Linear.smul_comp] at hz
        by_cases hc0 : c = 0
        · rw [hc', hc0, zero_smul]
        · exfalso
          have h1 : ι.hom ≫ f⟦(1 : ℤ)⟧' = 0 := by
            simpa [smul_smul, inv_mul_cancel₀ hc0] using congrArg (fun x => c⁻¹ • x) hz
          have h2 : f⟦(1 : ℤ)⟧' = 0 := by
            rw [← cancel_epi ι.hom, h1, comp_zero]
          exact hf ((shiftFunctor C (1 : ℤ)).map_injective (by rw [h2, Functor.map_zero]))
      · have := subsingleton_shift_shift k hG1 n (a + 1) hn
        rw [← cancel_mono ι.inv, Category.assoc, zero_comp]
        exact Subsingleton.elim _ _
    exact Triangle.coyoneda_exact₃ _ hT u hu
  have hsurj : ∀ n : ℤ, Function.Surjective (postComp (k := k) (X := G⟦n⟧) g) := by
    intro n u
    obtain ⟨v, hv⟩ := hlift n u
    exact ⟨v, hv.symm⟩
  have hfinZ : ∀ n : ℤ, Module.Finite k (G⟦n⟧ ⟶ Z) := fun n =>
    have := hM.1 n
    Module.Finite.of_surjective _ (hsurj n)
  have hsuppZ : {n : ℤ | Nontrivial (G⟦n⟧ ⟶ Z)} ⊆ {n : ℤ | Nontrivial (G⟦n⟧ ⟶ M)} :=
    fun n hn => have : Nontrivial (G⟦n⟧ ⟶ Z) := hn; (hsurj n).nontrivial
  refine ⟨⟨hfinZ, hM.2.subset hsuppZ⟩, ?_⟩
  have hle : ∀ n : ℤ, Module.finrank k (G⟦n⟧ ⟶ Z) ≤ Module.finrank k (G⟦n⟧ ⟶ M) := fun n =>
    have := hM.1 n
    LinearMap.finrank_le_finrank_of_surjective (hsurj n)
  have hlt : Module.finrank k (G⟦a⟧ ⟶ Z) < Module.finrank k (G⟦a⟧ ⟶ M) := by
    have := hM.1 a
    let φ := postComp (k := k) (X := G⟦a⟧) g
    have hrank := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr (hsurj a), finrank_top] at hrank
    have hker : LinearMap.ker φ ≠ ⊥ := by
      intro hbot
      have hmem : f ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr (comp_distTriang_mor_zero₁₂ _ hT)
      rw [hbot, Submodule.mem_bot] at hmem
      exact hf hmem
    have hpos : 0 < Module.finrank k (LinearMap.ker φ) :=
      Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.mp h0)
    omega
  let S := hM.2.toFinset
  have hsM : Function.support (fun n : ℤ => Module.finrank k (G⟦n⟧ ⟶ M)) ⊆ S := fun n hn =>
    hM.2.mem_toFinset.mpr (support_finrank_subset G M hn)
  have hsZ : Function.support (fun n : ℤ => Module.finrank k (G⟦n⟧ ⟶ Z)) ⊆ S := fun n hn =>
    hM.2.mem_toFinset.mpr (hsuppZ (support_finrank_subset G Z hn))
  have haS : a ∈ S := hM.2.mem_toFinset.mpr ⟨⟨f, 0, hf⟩⟩
  unfold totalDim
  rw [finsum_eq_sum_of_support_subset _ hsZ, finsum_eq_sum_of_support_subset _ hsM]
  exact Finset.sum_lt_sum (fun n _ => hle n) ⟨a, haS, hlt⟩

variable (P Q : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]

include hG0 hG1 in
/-- **Killing one exceptional object.** An object `M` with finite total `Hom` from the
exceptional object `G` is related, through finitely many distinguished triangles whose first
terms are shifts of `G`, to an object `X` right orthogonal to all shifts of `G`. Every
triangulated subcategory containing `G` and `X` contains `M`; right orthogonality to objects
orthogonal to `G`, and finite total `Hom` from objects with finite total `Hom` into `G`, pass
from `M` to `X`. -/
lemma exists_orth_of_finTot (hPG : P G) (hQG : Q G) {ι κ : Type*} (H : ι → C)
    (hH : ∀ i, Orth (H i) G)
    (F : κ → C) (hF : ∀ j, FinTot k (F j) G) :
    ∀ (N : ℕ) (M : C), totalDim k G M = N → FinTot k G M →
      ∃ X : C, Orth G X ∧ (P X → P M) ∧ (Q M → Q X) ∧ (∀ i, Orth (H i) M → Orth (H i) X) ∧
        (∀ j, FinTot k (F j) M → FinTot k (F j) X) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro M hN hM
    by_cases h0 : Orth G M
    · exact ⟨M, h0, id, id, fun _ => id, fun _ => id⟩
    · obtain ⟨a, ha⟩ : ∃ a : ℤ, Nontrivial (G⟦a⟧ ⟶ M) := by
        by_contra hne
        push Not at hne
        exact h0 hne
      obtain ⟨f, hf⟩ := exists_ne (0 : G⟦a⟧ ⟶ M)
      obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
      obtain ⟨hZ, hlt⟩ := finTot_and_totalDim_lt hG0 hG1 f g h hT hf hM
      obtain ⟨X, hX, hPX, hQX, hHX, hFX⟩ := ih _ (hN ▸ hlt) Z rfl hZ
      refine ⟨X, hX, fun hP => ?_, fun hQ => hQX ?_, fun i hi => hHX i ?_, fun j hj => hFX j ?_⟩
      · exact P.ext_of_isTriangulatedClosed₂ _ hT (P.le_shift a G hPG) (hPX hP)
      · exact Q.ext_of_isTriangulatedClosed₃ _ hT (Q.le_shift a G hQG) hQ
      · exact orth_obj₃ _ hT hi (orth_shift k (orth_shift k (hH i) a) 1)
      · exact finTot_obj₃ k _ hT hj (finTot_shift (finTot_shift (hF j) a) 1)

end Kill

/-! ### The full exceptional sequence -/

omit [HasZeroObject C] [Pretriangulated C] in
variable (k) in
include k in
/-- If `Hom(A, X⟦n⟧)` is trivial for every `n ≠ 0`, then so is `Hom(A⟦n⟧, X)`. -/
lemma orth_of_subsingleton_shift {A X : C} (h : ∀ n : ℤ, n ≠ 0 → Subsingleton (A ⟶ X⟦n⟧)) :
    ∀ n : ℤ, n ≠ 0 → Subsingleton (A⟦n⟧ ⟶ X) := by
  intro n hn
  have := h (-n) (by omega)
  exact (homShiftNegLinearEquiv (k := k) A X n).toEquiv.subsingleton

end ExceptionalAux

open ExceptionalAux in
/-- **An object with finite total `Hom` from a full exceptional sequence lies in every
triangulated subcategory containing the sequence.** Let `k` be a field, `C` a `k`-linear
pretriangulated category with `k`-linear shifts, and `G₀, …, G_{r-1}` objects of `C` with

* `hexc₀`, `hexc₁`: every endomorphism of each `G_a` is a scalar multiple of the identity and
  `Hom(G_a, G_a⟦n⟧) = 0` for `n ≠ 0`; this holds in particular for exceptional objects;
* `hsemi`: `Hom(G_b, G_a⟦n⟧) = 0` for `a < b` and all `n`;
* `hfin`: `∑_n dim_k Hom(G_a, G_b⟦n⟧) < ∞` for `a < b`;
* `hgen`: inside a triangulated subcategory `Q` (closed under isomorphisms) containing every
  `G_a`, an object `M` with `Hom(G_a, M⟦n⟧) = 0` for all `a` and `n` is zero.

If `M` lies in `Q` and `∑_n dim_k Hom(G_a, M⟦n⟧) < ∞` for every `a`, then `M` lies in every
triangulated subcategory `P`, closed under isomorphisms, containing every `G_a`. -/
theorem prop_of_hasFiniteTotalHom_of_exceptional {r : ℕ} (G : Fin r → C)
    (hexc₀ : ∀ a (e : G a ⟶ G a), ∃ c : k, e = c • 𝟙 (G a))
    (hexc₁ : ∀ a (n : ℤ), n ≠ 0 → Subsingleton (G a ⟶ (G a)⟦n⟧))
    (hsemi : ∀ a b : Fin r, a < b → ∀ n : ℤ, Subsingleton (G b ⟶ (G a)⟦n⟧))
    (hfin : ∀ a b : Fin r, a < b → HasFiniteTotalHom k (G a) (G b))
    (Q : ObjectProperty C) [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms] (hQ : ∀ a, Q (G a))
    (hgen : ∀ M : C, Q M → (∀ a (n : ℤ), Subsingleton (G a ⟶ M⟦n⟧)) → IsZero M)
    (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] (hP : ∀ a, P (G a))
    (M : C) (hQM : Q M) (hM : ∀ a, HasFiniteTotalHom k (G a) M) : P M := by
  have aux : ∀ t : ℕ, t ≤ r → ∃ X : C, (P X → P M) ∧ Q X ∧
      (∀ b : Fin r, r - t ≤ (b : ℕ) → Orth (G b) X) ∧
      (∀ a : Fin r, (a : ℕ) < r - t → FinTot k (G a) X) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨M, id, hQM, fun b hb => absurd b.2 (by omega),
        fun a _ => (finTot_iff _ _).2 (hM a)⟩
    | succ t ih =>
      intro ht
      obtain ⟨X, hPX, hQX, hOX, hFX⟩ := ih (by omega)
      let s : Fin r := ⟨r - (t + 1), by omega⟩
      have hs : (s : ℕ) = r - (t + 1) := rfl
      obtain ⟨X', hX', hPX', hQX', hHX', hFX'⟩ :=
        exists_orth_of_finTot (hexc₀ s) (orth_of_subsingleton_shift k (hexc₁ s)) P Q (hP s) (hQ s)
          (fun b : {b : Fin r // r - t ≤ (b : ℕ)} => G b.1)
          (fun b => (orth_iff k _ _).2 (hsemi s b.1 (Fin.lt_def.2 (lt_of_lt_of_le (by omega) b.2))))
          (fun a : {a : Fin r // (a : ℕ) < r - (t + 1)} => G a.1)
          (fun a => (finTot_iff _ _).2 (hfin a.1 s (Fin.lt_def.2 (lt_of_lt_of_le a.2 (by omega)))))
          _ X rfl (hFX s (by omega))
      refine ⟨X', fun h => hPX (hPX' h), hQX' hQX, fun b hb => ?_, fun a ha => ?_⟩
      · by_cases hbs : (b : ℕ) = r - (t + 1)
        · obtain rfl : b = s := Fin.ext hbs
          exact hX'
        · exact hHX' ⟨b, by omega⟩ (hOX b (by omega))
      · exact hFX' ⟨a, ha⟩ (hFX a (by omega))
  obtain ⟨X, hPX, hQX, hOX, -⟩ := aux r le_rfl
  exact hPX (P.prop_of_isZero (hgen X hQX fun a n => (orth_iff k _ _).1 (hOX a (by omega)) n))

end CategoryTheory.Pretriangulated
