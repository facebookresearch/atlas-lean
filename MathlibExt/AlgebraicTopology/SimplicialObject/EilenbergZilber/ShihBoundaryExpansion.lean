/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormula

/-!
# Boundary expansion for the explicit Shih operator

This file expands the two composites in the Shih homotopy boundary into finite
double sums.  It deliberately stops before the combinatorial cancellation of
interior faces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A face applied after a degree-`n` Shih summand. -/
def shihUpperBoundaryTerm (X Y : SimplicialObject C) (n : ℕ)
    (i : ShihIndex n) (k : Fin (n + 2)) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  ((-1 : ℤ) ^ k.val) •
    (shihSummand X Y i ≫ (X.δ k ⊗ₘ Y.δ k))

/-- A face applied before a degree-`n` Shih summand.  This is the second
boundary contribution in degree `n + 1`. -/
def shihLowerBoundaryTerm (X Y : SimplicialObject C) (n : ℕ)
    (k : Fin (n + 2)) (i : ShihIndex n) :
    X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) ⟶
      X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) :=
  ((-1 : ℤ) ^ k.val) •
    ((X.δ k ⊗ₘ Y.δ k) ≫ shihSummand X Y i)

set_option backward.isDefEq.respectTransparency false in
theorem shihComponent_comp_d (X Y : SimplicialObject C) (n : ℕ) :
    shihComponent X Y n ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) n =
      ∑ z : Fin (n + 2) × ShihIndex n,
        shihUpperBoundaryTerm X Y n z.2 z.1 := by
  unfold shihComponent AlgebraicTopology.AlternatingFaceMapComplex.objD
    shihUpperBoundaryTerm
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.comp_zsmul, Finset.smul_sum]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]
  apply Finset.sum_congr rfl
  intro z _
  change ((-1 : ℤ) ^ z.1.val) •
    (shihSummand X Y z.2 ≫ (X.δ z.1 ⊗ₘ Y.δ z.1)) = _
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem d_comp_shihComponent (X Y : SimplicialObject C) (n : ℕ) :
    AlgebraicTopology.AlternatingFaceMapComplex.objD (X ⊗ Y) n ≫
        shihComponent X Y n =
      ∑ z : ShihIndex n × Fin (n + 2),
        shihLowerBoundaryTerm X Y n z.2 z.1 := by
  unfold shihComponent AlgebraicTopology.AlternatingFaceMapComplex.objD
    shihLowerBoundaryTerm
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp]
  rw [← Finset.sum_product']
  simp only [Finset.univ_product_univ]
  apply Finset.sum_congr rfl
  intro z _
  change ((-1 : ℤ) ^ z.2.val) •
    ((X.δ z.2 ⊗ₘ Y.δ z.2) ≫ shihSummand X Y z.1) = _
  rfl

end AlgebraicTopology.EilenbergZilber
