/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormulaRecursion

/-!
# Positive boundary faces of derived Shih summands

This file rewrites the positive-face boundary terms of the gap-greater-than-one
part of the Shih formula as derived lower-degree terms.  It is independent of
the classification of the complementary gap-one family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A positive upper boundary face of a derived Shih summand. -/
def derivedShihUpperBoundaryTerm (X Y : SimplicialObject C) (n : ℕ)
    (i : ShihIndex n) (k : Fin (n + 2)) :
    X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) ⟶
      X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) :=
  ((-1 : ℤ) ^ k.val) •
    (derivedShihSummand X Y i ≫ (X.δ k.succ ⊗ₘ Y.δ k.succ))

/-- A positive lower boundary face of a derived Shih summand. -/
def derivedShihLowerBoundaryTerm (X Y : SimplicialObject C) (n : ℕ)
    (k : Fin (n + 2)) (i : ShihIndex n) :
    X.obj (Opposite.op ⦋n + 2⦌) ⊗ Y.obj (Opposite.op ⦋n + 2⦌) ⟶
      X.obj (Opposite.op ⦋n + 2⦌) ⊗ Y.obj (Opposite.op ⦋n + 2⦌) :=
  ((-1 : ℤ) ^ k.val) •
    ((X.δ k.succ ⊗ₘ Y.δ k.succ) ≫ derivedShihSummand X Y i)

theorem shihUpperBoundaryTerm_succ_succ (X Y : SimplicialObject C) (n : ℕ)
    (i : ShihIndex n) (k : Fin (n + 2)) :
    shihUpperBoundaryTerm X Y (n + 1) i.succ k.succ =
      derivedShihUpperBoundaryTerm X Y n i k := by
  simp [shihUpperBoundaryTerm, derivedShihUpperBoundaryTerm,
    shihSummand_succ, pow_succ]

theorem shihLowerBoundaryTerm_succ_succ (X Y : SimplicialObject C) (n : ℕ)
    (k : Fin (n + 2)) (i : ShihIndex n) :
    shihLowerBoundaryTerm X Y (n + 1) k.succ i.succ =
      derivedShihLowerBoundaryTerm X Y n k i := by
  simp [shihLowerBoundaryTerm, derivedShihLowerBoundaryTerm,
    shihSummand_succ, pow_succ]

/-- The front face of a derived summand is the original summand preceded by
the front face. -/
theorem derivedShihSummand_comp_δ_zero (X Y : SimplicialObject C) {n : ℕ}
    (i : ShihIndex n) :
    derivedShihSummand X Y i ≫
        (X.δ (0 : Fin (n + 3)) ⊗ₘ Y.δ (0 : Fin (n + 3))) =
      (X.δ (0 : Fin (n + 2)) ⊗ₘ Y.δ (0 : Fin (n + 2))) ≫
        shihSummand X Y i := by
  unfold derivedShihSummand shihSummand
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom,
    map_derivedSimplexHom_comp_δ_zero,
    map_derivedSimplexHom_comp_δ_zero]

/-- The front upper face of every gap-greater-than-one summand cancels the
front lower face of the corresponding lower-degree summand. -/
theorem shihBoundaryTerm_succ_zero_add_lower_zero (X Y : SimplicialObject C)
    {n : ℕ} (i : ShihIndex n) :
    shihUpperBoundaryTerm X Y (n + 1) i.succ (0 : Fin (n + 3)) +
        shihLowerBoundaryTerm X Y n (0 : Fin (n + 2)) i = 0 := by
  simp only [shihUpperBoundaryTerm, shihLowerBoundaryTerm, Fin.val_zero,
    pow_zero, one_zsmul, shihSummand_succ, Preadditive.neg_comp]
  rw [derivedShihSummand_comp_δ_zero]
  exact neg_add_cancel _

/-- After reindexing by `ShihIndex.succ`, all front upper faces in the
gap-greater-than-one family cancel all front lower faces one degree below. -/
theorem sum_upper_gap_gt_one_zero_add_sum_lower_zero (X Y : SimplicialObject C)
    (n : ℕ) :
    (∑ i : {i : ShihIndex (n + 1) // 1 < i.gap},
        shihUpperBoundaryTerm X Y (n + 1) i.1 (0 : Fin (n + 3))) +
      ∑ i : ShihIndex n,
        shihLowerBoundaryTerm X Y n (0 : Fin (n + 2)) i = 0 := by
  calc
    _ = ∑ i : ShihIndex n,
        (shihUpperBoundaryTerm X Y (n + 1) i.succ (0 : Fin (n + 3)) +
          shihLowerBoundaryTerm X Y n (0 : Fin (n + 2)) i) := by
      have hindex :
          (∑ i : {i : ShihIndex (n + 1) // 1 < i.gap},
              shihUpperBoundaryTerm X Y (n + 1) i.1 (0 : Fin (n + 3))) =
            ∑ i : ShihIndex n,
              shihUpperBoundaryTerm X Y (n + 1) i.succ (0 : Fin (n + 3)) :=
        ShihIndex.sum_gap_gt_one fun i =>
          shihUpperBoundaryTerm X Y (n + 1) i (0 : Fin (n + 3))
      rw [hindex, Finset.sum_add_distrib]
    _ = 0 := Finset.sum_eq_zero fun i _ =>
      shihBoundaryTerm_succ_zero_add_lower_zero X Y i

/-- Pointwise positive-face interaction on the upper boundary of a derived
summand.  Both simplex maps remain derived after the face is absorbed. -/
theorem derivedShihUpperBoundaryTerm_eq (X Y : SimplicialObject C) (n : ℕ)
    (i : ShihIndex n) (k : Fin (n + 2)) :
    derivedShihUpperBoundaryTerm X Y n i k =
      (((-1 : ℤ) ^ k.val) * i.sign) •
        (X.map (derivedSimplexHom (SimplexCategory.δ k ≫ i.leftHom)).op ⊗ₘ
          Y.map (derivedSimplexHom (SimplexCategory.δ k ≫ i.rightHom)).op) := by
  unfold derivedShihUpperBoundaryTerm derivedShihSummand
  rw [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom,
    map_derivedSimplexHom_comp_δ_succ,
    map_derivedSimplexHom_comp_δ_succ, mul_smul]

/-- Pointwise positive-face interaction on the lower boundary of a derived
summand.  Both simplex maps remain derived after the face is absorbed. -/
theorem derivedShihLowerBoundaryTerm_eq (X Y : SimplicialObject C) (n : ℕ)
    (k : Fin (n + 2)) (i : ShihIndex n) :
    derivedShihLowerBoundaryTerm X Y n k i =
      (((-1 : ℤ) ^ k.val) * i.sign) •
        (X.map (derivedSimplexHom (i.leftHom ≫ SimplexCategory.δ k)).op ⊗ₘ
          Y.map (derivedSimplexHom (i.rightHom ≫ SimplexCategory.δ k)).op) := by
  unfold derivedShihLowerBoundaryTerm derivedShihSummand
  rw [Preadditive.comp_zsmul,
    MonoidalCategory.tensorHom_comp_tensorHom,
    δ_succ_comp_map_derivedSimplexHom,
    δ_succ_comp_map_derivedSimplexHom, mul_smul]

/-- All positive upper faces of the gap-greater-than-one family reindex to
the positive upper faces of derived degree-`n` summands. -/
theorem sum_upper_gap_gt_one_positive_faces (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap},
        ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i.1 k.succ =
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 2), derivedShihUpperBoundaryTerm X Y n i k := by
  calc
    _ = ∑ i : ShihIndex n,
          ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i.succ k.succ :=
      ShihIndex.sum_gap_gt_one
        (fun i => ∑ k : Fin (n + 2), shihUpperBoundaryTerm X Y (n + 1) i k.succ)
    _ = _ := Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => shihUpperBoundaryTerm_succ_succ X Y n i k

/-- All positive lower faces of the gap-greater-than-one family reindex to
the positive lower faces of derived degree-`n` summands. -/
theorem sum_lower_gap_gt_one_positive_faces (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex (n + 1) // 1 < i.gap},
        ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y (n + 1) k.succ i.1 =
      ∑ i : ShihIndex n,
        ∑ k : Fin (n + 2), derivedShihLowerBoundaryTerm X Y n k i := by
  calc
    _ = ∑ i : ShihIndex n,
          ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y (n + 1) k.succ i.succ :=
      ShihIndex.sum_gap_gt_one
        (fun i => ∑ k : Fin (n + 2), shihLowerBoundaryTerm X Y (n + 1) k.succ i)
    _ = _ := Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => shihLowerBoundaryTerm_succ_succ X Y n k i

end AlgebraicTopology.EilenbergZilber
