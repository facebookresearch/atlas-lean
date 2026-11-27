/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihFormulaRecursion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOne

/-!
# The gap-one Shih boundary family

The front face of a gap-one Shih summand factors through an
Alexander--Whitney front/back face pair followed by its shuffle.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial SimplexCategory
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

variable {C : Type u} [Category.{v} C]

/-- The Alexander--Whitney/shuffle simplex map in the left factor associated
to a gap-one Shih index. -/
def gapOneBaseLeftHom {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) : ⦋n⦌ ⟶ ⦋n⦌ :=
  eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
    i.shuffle.leftHom ≫
      AlexanderWhitney.frontInclusion ((i.p : ℕ) + 1) i.q n
        (i.p_add_one_add_q_eq hi)

/-- The Alexander--Whitney/shuffle simplex map in the right factor associated
to a gap-one Shih index. -/
def gapOneBaseRightHom {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) : ⦋n⦌ ⟶ ⦋n⦌ :=
  eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
    i.shuffle.rightHom ≫
      AlexanderWhitney.backInclusion ((i.p : ℕ) + 1) i.q n
        (i.p_add_one_add_q_eq hi)

theorem δ_zero_comp_leftHom_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ i.leftHom =
      eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
        i.shuffle.leftHom ≫
          AlexanderWhitney.frontInclusion ((i.p : ℕ) + 1) i.q n
            (i.p_add_one_add_q_eq hi) := by
  ext k
  refine (i.leftHom_succ_of_gap_eq_one hi k).trans ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    eqToHom_toOrderHom, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    AlexanderWhitney.frontInclusion_toOrderHom]

theorem leftHom_eq_cone_gapOneBaseLeftHom {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    i.leftHom = coneSimplexHom (i.gapOneBaseLeftHom hi) := by
  ext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [coneSimplexHom, derivedSimplexHom, SimplexCategory.σ,
      leftHom_zero_of_gap_eq_one i hi]
  · simpa [coneSimplexHom, derivedSimplexHom, SimplexCategory.σ,
      gapOneBaseLeftHom] using i.leftHom_succ_of_gap_eq_one hi k

/-- Every positive face of the left gap-one map remains a cone. -/
theorem δ_succ_comp_leftHom_of_gap_eq_one {n : ℕ} (i : ShihIndex (n + 1))
    (hi : i.gap = 1) (k : Fin (n + 2)) :
    SimplexCategory.δ k.succ ≫ i.leftHom =
      coneSimplexHom (SimplexCategory.δ k ≫ i.gapOneBaseLeftHom hi) := by
  rw [i.leftHom_eq_cone_gapOneBaseLeftHom hi,
    δ_succ_comp_coneSimplexHom]

theorem map_leftHom_comp_δ_succ_of_gap_eq_one (X : SimplicialObject C)
    {n : ℕ} (i : ShihIndex (n + 1)) (hi : i.gap = 1) (k : Fin (n + 2)) :
    X.map i.leftHom.op ≫ X.δ k.succ =
      X.map (coneSimplexHom
        (SimplexCategory.δ k ≫ i.gapOneBaseLeftHom hi)).op := by
  simpa only [gapOneBaseLeftHom, X.δ_def, ← X.map_comp,
    CategoryTheory.op_comp] using
    congrArg (fun f => X.map f.op) (i.δ_succ_comp_leftHom_of_gap_eq_one hi k)

theorem δ_zero_comp_rightHom_of_gap_eq_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ i.rightHom =
      eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
        i.shuffle.rightHom ≫
          AlexanderWhitney.backInclusion ((i.p : ℕ) + 1) i.q n
            (i.p_add_one_add_q_eq hi) := by
  ext k
  refine (i.rightHom_succ_of_gap_eq_one hi k).trans ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    eqToHom_toOrderHom, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    AlexanderWhitney.backInclusion_toOrderHom]
  omega

theorem rightHom_eq_cone_gapOneBaseRightHom {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    i.rightHom = coneSimplexHom (i.gapOneBaseRightHom hi) := by
  ext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [coneSimplexHom, derivedSimplexHom, SimplexCategory.σ,
      rightHom_zero_of_gap_eq_one i hi]
  · simpa [coneSimplexHom, derivedSimplexHom, SimplexCategory.σ,
      gapOneBaseRightHom, Nat.add_comm] using i.rightHom_succ_of_gap_eq_one hi k

/-- Every positive face of the right gap-one map remains a cone. -/
theorem δ_succ_comp_rightHom_of_gap_eq_one {n : ℕ} (i : ShihIndex (n + 1))
    (hi : i.gap = 1) (k : Fin (n + 2)) :
    SimplexCategory.δ k.succ ≫ i.rightHom =
      coneSimplexHom (SimplexCategory.δ k ≫ i.gapOneBaseRightHom hi) := by
  rw [i.rightHom_eq_cone_gapOneBaseRightHom hi,
    δ_succ_comp_coneSimplexHom]

theorem map_rightHom_comp_δ_succ_of_gap_eq_one (X : SimplicialObject C)
    {n : ℕ} (i : ShihIndex (n + 1)) (hi : i.gap = 1) (k : Fin (n + 2)) :
    X.map i.rightHom.op ≫ X.δ k.succ =
      X.map (coneSimplexHom
        (SimplexCategory.δ k ≫ i.gapOneBaseRightHom hi)).op := by
  simpa only [gapOneBaseRightHom, X.δ_def, ← X.map_comp,
    CategoryTheory.op_comp] using
    congrArg (fun f => X.map f.op) (i.δ_succ_comp_rightHom_of_gap_eq_one hi k)

/-- Functorial form of `δ_zero_comp_leftHom_of_gap_eq_one`. -/
theorem map_leftHom_comp_δ_zero_of_gap_eq_one (X : SimplicialObject C)
    {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    X.map i.leftHom.op ≫ X.δ (0 : Fin (n + 2)) =
      AlexanderWhitney.frontFace (C := C) X (i.p_add_one_add_q_eq hi) ≫
        X.map i.shuffle.leftHom.op ≫
          X.map (eqToHom (by rw [i.p_add_one_add_q_eq hi])).op := by
  simpa only [Category.assoc, X.δ_def, AlexanderWhitney.frontFace,
    ← X.map_comp, CategoryTheory.op_comp] using congrArg (fun f => X.map f.op)
      (i.δ_zero_comp_leftHom_of_gap_eq_one hi)

theorem map_leftHom_comp_δ_zero_eq_gapOneBaseLeftHom
    (X : SimplicialObject C) {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    X.map i.leftHom.op ≫ X.δ (0 : Fin (n + 2)) =
      X.map (i.gapOneBaseLeftHom hi).op := by
  rw [i.map_leftHom_comp_δ_zero_of_gap_eq_one X hi]
  unfold gapOneBaseLeftHom AlexanderWhitney.frontFace
  rw [← X.map_comp, ← X.map_comp]
  rfl

/-- Functorial form of `δ_zero_comp_rightHom_of_gap_eq_one`. -/
theorem map_rightHom_comp_δ_zero_of_gap_eq_one (X : SimplicialObject C)
    {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    X.map i.rightHom.op ≫ X.δ (0 : Fin (n + 2)) =
      AlexanderWhitney.backFace (C := C) X (i.p_add_one_add_q_eq hi) ≫
        X.map i.shuffle.rightHom.op ≫
          X.map (eqToHom (by rw [i.p_add_one_add_q_eq hi])).op := by
  simpa only [Category.assoc, X.δ_def, AlexanderWhitney.backFace,
    SimplicialObject.δ₀Iter, AlexanderWhitney.backInclusion,
    ← X.map_comp, CategoryTheory.op_comp] using congrArg (fun f => X.map f.op)
      (i.δ_zero_comp_rightHom_of_gap_eq_one hi)

theorem map_rightHom_comp_δ_zero_eq_gapOneBaseRightHom
    (X : SimplicialObject C) {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    X.map i.rightHom.op ≫ X.δ (0 : Fin (n + 2)) =
      X.map (i.gapOneBaseRightHom hi).op := by
  rw [i.map_rightHom_comp_δ_zero_of_gap_eq_one X hi]
  unfold gapOneBaseRightHom AlexanderWhitney.backFace SimplicialObject.δ₀Iter
  rw [← X.map_comp, ← X.map_comp]
  rfl

end ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The `AW ≫ shuffle` summand indexed by a gap-one Shih index, before the
cone construction that raises degree. -/
def gapOneBaseSummand (X Y : SimplicialObject C) {n : ℕ}
    (i : ShihIndex n) (hi : i.gap = 1) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  shuffleSignZ i.shuffle •
    (X.map (i.gapOneBaseLeftHom hi).op ⊗ₘ
      Y.map (i.gapOneBaseRightHom hi).op)

/-- A gap-one Shih summand is the cone of its underlying
Alexander--Whitney/shuffle summand, factor by factor. -/
theorem shihSummand_eq_cone_gapOneBaseSummand (X Y : SimplicialObject C)
    {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    shihSummand X Y i =
      shuffleSignZ i.shuffle •
        (X.map (coneSimplexHom (i.gapOneBaseLeftHom hi)).op ⊗ₘ
          Y.map (coneSimplexHom (i.gapOneBaseRightHom hi)).op) := by
  unfold shihSummand
  rw [i.sign_of_gap_eq_one hi, i.leftHom_eq_cone_gapOneBaseLeftHom hi,
    i.rightHom_eq_cone_gapOneBaseRightHom hi]

/-- The front boundary face of a gap-one Shih summand is its
Alexander--Whitney front/back face pair followed by the corresponding shuffle
simplex maps.  This is the pointwise `AW ≫ shuffle` survivor. -/
theorem shihUpperBoundaryTerm_zero_of_gap_eq_one (X Y : SimplicialObject C)
    {n : ℕ} (i : ShihIndex n) (hi : i.gap = 1) :
    shihUpperBoundaryTerm X Y n i (0 : Fin (n + 2)) =
      gapOneBaseSummand X Y i hi := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Fin.val_zero, pow_zero, one_zsmul]
  rw [i.sign_of_gap_eq_one hi]
  rw [Preadditive.zsmul_comp, MonoidalCategory.tensorHom_comp_tensorHom]
  rw [i.map_leftHom_comp_δ_zero_eq_gapOneBaseLeftHom X hi,
    i.map_rightHom_comp_δ_zero_eq_gapOneBaseRightHom Y hi]
  rfl

/-- Explicit cone form of every positive upper boundary face in the gap-one
family.  The remaining survivor calculation is therefore entirely a statement
about the Alexander--Whitney/shuffle base maps. -/
theorem shihUpperBoundaryTerm_succ_of_gap_eq_one (X Y : SimplicialObject C)
    {n : ℕ} (i : ShihIndex (n + 1)) (hi : i.gap = 1) (k : Fin (n + 2)) :
    shihUpperBoundaryTerm X Y (n + 1) i k.succ =
      (((-1 : ℤ) ^ k.succ.val) * shuffleSignZ i.shuffle) •
        (X.map (coneSimplexHom
              (SimplexCategory.δ k ≫ i.gapOneBaseLeftHom hi)).op ⊗ₘ
          Y.map (coneSimplexHom
              (SimplexCategory.δ k ≫ i.gapOneBaseRightHom hi)).op) := by
  unfold shihUpperBoundaryTerm shihSummand
  rw [i.sign_of_gap_eq_one hi, Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [i.map_leftHom_comp_δ_succ_of_gap_eq_one X hi k,
    i.map_rightHom_comp_δ_succ_of_gap_eq_one Y hi k, mul_smul]

/-- The entire front-face contribution of the gap-one family is the sum of
the nonzero-front-degree Alexander--Whitney/shuffle summands displayed above. -/
theorem sum_upper_gap_one_zero (X Y : SimplicialObject C) (n : ℕ) :
    ∑ i : {i : ShihIndex n // i.gap = 1},
        shihUpperBoundaryTerm X Y n i.1 (0 : Fin (n + 2)) =
      ∑ i : {i : ShihIndex n // i.gap = 1},
        gapOneBaseSummand X Y i.1 i.2 := by
  exact Finset.sum_congr rfl fun i _ =>
    shihUpperBoundaryTerm_zero_of_gap_eq_one X Y i.1 i.2

end AlgebraicTopology.EilenbergZilber
