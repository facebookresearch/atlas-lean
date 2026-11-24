/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormula
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihIndexRecursion

/-!
# Recursive form of the explicit Shih formula

This file identifies the gap-greater-than-one summands in degree `n+1` with
the derived degree-`n` summands.  Their signs are opposite, exactly as in the
Eilenberg--Mac Lane recursion `H_(n+1) = -H'_n + F'_n s_0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

/-- Add an initial fixed vertex to a monotone simplex map. -/
def derivedSimplexHom {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) : ⦋a + 1⦌ ⟶ ⦋b + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.cases 0 fun k => (f.toOrderHom k).succ
    monotone' := by
      intro i j hij
      by_cases hi : i = 0
      · subst hi
        exact Fin.zero_le _
      · have hj : j ≠ 0 := by
          rintro rfl
          exact hi (le_antisymm hij (Fin.zero_le _))
        obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
        simpa only [Fin.cases_succ, Fin.succ_le_succ_iff] using
          f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij) }

/-- A positive face before a derived operator is the derived preceding face. -/
theorem δ_succ_comp_derivedSimplexHom {a b : ℕ}
    (f : ⦋a + 1⦌ ⟶ ⦋b⦌) (k : Fin (a + 2)) :
    SimplexCategory.δ k.succ ≫ derivedSimplexHom f =
      derivedSimplexHom (SimplexCategory.δ k ≫ f) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    rfl
  · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero hx
    simp [derivedSimplexHom, SimplexCategory.δ, Fin.succAbove]
    split_ifs <;> rfl

/-- A positive face after a derived operator is the derived preceding face. -/
theorem derivedSimplexHom_comp_δ_succ {a b : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) (k : Fin (b + 2)) :
    derivedSimplexHom f ≫ SimplexCategory.δ k.succ =
      derivedSimplexHom (f ≫ SimplexCategory.δ k) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    rfl
  · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero hx
    simp [derivedSimplexHom, SimplexCategory.δ, Fin.succAbove]
    split_ifs <;> rfl

/-- The front face commutes with derivation, after moving it to the target. -/
theorem δ_zero_comp_derivedSimplexHom {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) :
    SimplexCategory.δ (0 : Fin (a + 2)) ≫ derivedSimplexHom f =
      f ≫ SimplexCategory.δ (0 : Fin (b + 2)) := by
  ext x
  simp [derivedSimplexHom, SimplexCategory.δ]

/-- The cone of a simplex map: derive it and then collapse the first edge. -/
def coneSimplexHom {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) : ⦋a + 1⦌ ⟶ ⦋b⦌ :=
  derivedSimplexHom f ≫ SimplexCategory.σ (0 : Fin (b + 1))

@[simp]
theorem δ_zero_comp_coneSimplexHom {a b : ℕ} (f : ⦋a⦌ ⟶ ⦋b⦌) :
    SimplexCategory.δ (0 : Fin (a + 2)) ≫ coneSimplexHom f = f := by
  have hzero : (0 : Fin (b + 2)) = Fin.castSucc (0 : Fin (b + 1)) := rfl
  rw [coneSimplexHom, ← Category.assoc, δ_zero_comp_derivedSimplexHom,
    Category.assoc, hzero, SimplexCategory.δ_comp_σ_self]
  simp

/-- Positive faces commute with coning, shifting their index down by one. -/
theorem δ_succ_comp_coneSimplexHom {a b : ℕ} (f : ⦋a + 1⦌ ⟶ ⦋b⦌)
    (k : Fin (a + 2)) :
    SimplexCategory.δ k.succ ≫ coneSimplexHom f =
      coneSimplexHom (SimplexCategory.δ k ≫ f) := by
  rw [coneSimplexHom, coneSimplexHom, ← Category.assoc,
    δ_succ_comp_derivedSimplexHom]

variable {C : Type u} [Category.{v} C]

/-- Applying a positive face after a derived simplicial operator derives the
corresponding lower-degree composite. -/
theorem map_derivedSimplexHom_comp_δ_succ (X : SimplicialObject C) {a b : ℕ}
    (f : ⦋a + 1⦌ ⟶ ⦋b⦌) (k : Fin (a + 2)) :
    X.map (derivedSimplexHom f).op ≫ X.δ k.succ =
      X.map (derivedSimplexHom (SimplexCategory.δ k ≫ f)).op := by
  rw [X.δ_def, ← X.map_comp]
  congr 1
  exact congrArg Opposite.op (δ_succ_comp_derivedSimplexHom f k)

/-- Applying a positive face before a derived simplicial operator derives the
corresponding lower-degree composite. -/
theorem δ_succ_comp_map_derivedSimplexHom (X : SimplicialObject C) {a b : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) (k : Fin (b + 2)) :
    X.δ k.succ ≫ X.map (derivedSimplexHom f).op =
      X.map (derivedSimplexHom (f ≫ SimplexCategory.δ k)).op := by
  rw [X.δ_def, ← X.map_comp]
  congr 1
  exact congrArg Opposite.op (derivedSimplexHom_comp_δ_succ f k)

/-- The map of a derived operator followed by the front face is the front face
followed by the original operator. -/
theorem map_derivedSimplexHom_comp_δ_zero (X : SimplicialObject C) {a b : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) :
    X.map (derivedSimplexHom f).op ≫ X.δ (0 : Fin (a + 2)) =
      X.δ (0 : Fin (b + 2)) ≫ X.map f.op := by
  rw [X.δ_def, X.δ_def, ← X.map_comp, ← X.map_comp]
  congr 1

namespace ShihIndex

@[simp]
theorem succ_leftHom {n : ℕ} (i : ShihIndex n) :
    i.succ.leftHom = derivedSimplexHom i.leftHom := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [leftHom, derivedSimplexHom, succ_gap]
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
    by_cases hkm : (k : ℕ) < i.gap
    · simp [leftHom, derivedSimplexHom, succ_gap, hkm]
    · have hgap := succ_gap i
      simp [leftHom, derivedSimplexHom, hkm, hgap, suffixInput]
      have hm := i.gap_pos
      omega

@[simp]
theorem succ_rightHom {n : ℕ} (i : ShihIndex n) :
    i.succ.rightHom = derivedSimplexHom i.rightHom := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [rightHom, derivedSimplexHom, succ_gap]
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
    by_cases hkm : (k : ℕ) < i.gap
    · simp [rightHom, derivedSimplexHom, succ_gap, hkm]
    · have hgap := succ_gap i
      simp [rightHom, derivedSimplexHom, hkm, hgap, suffixInput]
      omega

end ShihIndex

variable [Preadditive C] [MonoidalCategory C]

/-- The derived version of one degree-`n` Shih summand. -/
def derivedShihSummand (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n) :
    X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) ⟶
      X.obj (Opposite.op ⦋n + 2⦌) ⊗ Y.obj (Opposite.op ⦋n + 2⦌) :=
  i.sign •
    (X.map (derivedSimplexHom i.leftHom).op ⊗ₘ
      Y.map (derivedSimplexHom i.rightHom).op)

theorem shihSummand_succ (X Y : SimplicialObject C) {n : ℕ}
    (i : ShihIndex n) :
    shihSummand X Y i.succ = -derivedShihSummand X Y i := by
  simp [shihSummand, derivedShihSummand]

/-- The gap-one part of the Shih formula in degree `n+1`. -/
def gapOneShihComponent (X Y : SimplicialObject C) (n : ℕ) :
    X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) ⟶
      X.obj (Opposite.op ⦋n + 2⦌) ⊗ Y.obj (Opposite.op ⦋n + 2⦌) :=
  ∑ i : {i : ShihIndex (n + 1) // i.gap = 1}, shihSummand X Y i.1

/-- Reindexing the gap-greater-than-one part of the degree-`n+1` formula
produces the negative derived degree-`n` formula. -/
theorem sum_shihSummand_gap_gt_one (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap}, shihSummand X Y i.1 =
      -∑ i : ShihIndex n, derivedShihSummand X Y i := by
  rw [ShihIndex.sum_gap_gt_one]
  simp only [shihSummand_succ, Finset.sum_neg_distrib]

/-- Recursive decomposition of the explicit Shih formula into its gap-one
front family and the negative derived lower-degree formula. -/
theorem shihComponent_succ (X Y : SimplicialObject C) (n : ℕ) :
    shihComponent X Y (n + 1) =
      gapOneShihComponent X Y n -
        ∑ i : ShihIndex n, derivedShihSummand X Y i := by
  change (∑ i : ShihIndex (n + 1), shihSummand X Y i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun i : ShihIndex (n + 1) => i.gap = 1)
    (fun i => shihSummand X Y i)]
  let e : {i : ShihIndex (n + 1) // ¬i.gap = 1} ≃
      {i : ShihIndex (n + 1) // 1 < i.gap} :=
    Equiv.subtypeEquivProp (by
      funext i
      apply propext
      have hi := i.gap_pos
      omega)
  have hcomplement :
      (∑ i : {i : ShihIndex (n + 1) // ¬i.gap = 1}, shihSummand X Y i.1) =
        ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap}, shihSummand X Y i.1 := by
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  rw [hcomplement, sum_shihSummand_gap_gt_one]
  simp only [gapOneShihComponent, sub_eq_add_neg]

end AlgebraicTopology.EilenbergZilber
