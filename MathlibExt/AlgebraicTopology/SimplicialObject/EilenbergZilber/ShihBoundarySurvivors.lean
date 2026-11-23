/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihGapOne
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

/-!
# Exceptional survivors in the Shih boundary

This file identifies the negative identity term and the zero-face gap-one
terms that form the positive Alexander--Whitney--shuffle contribution.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- The unique Shih index producing the negative identity survivor in degree
`n + 1`. -/
def identitySurvivor (n : ℕ) : ShihIndex (n + 1) where
  p := ⟨0, by omega⟩
  q := ⟨0, by simp⟩
  shuffle := Shuffle.rightUnitShuffle 1

/-- The face paired with `identitySurvivor`. -/
def identitySurvivorFace (n : ℕ) : Fin (n + 3) :=
  ⟨n + 1, by omega⟩

@[simp]
theorem identitySurvivor_gap (n : ℕ) :
    (identitySurvivor n).gap = n + 1 := by
  simp [identitySurvivor, gap]

@[simp]
theorem identitySurvivor_sign (n : ℕ) :
    (identitySurvivor n).sign = (-1 : ℤ) ^ n := by
  simp [sign, identitySurvivor, gap, pow_succ]

theorem delta_identitySurvivorFace_comp_leftHom (n : ℕ) :
    SimplexCategory.δ (identitySurvivorFace n) ≫
        (identitySurvivor n).leftHom = 𝟙 _ := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.id_toOrderHom,
    ShihIndex.leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    identitySurvivor_gap]
  by_cases hk : k.val < n + 1
  · have hkface : k.castSucc < identitySurvivorFace n := by
      simp only [Fin.lt_def, Fin.val_castSucc, identitySurvivorFace]
      exact hk
    have hbranch :
        ((identitySurvivorFace n).succAbove k).val < n + 1 := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
      simpa only [Fin.val_castSucc] using hk
    rw [dite_eq_left hbranch]
    change ((identitySurvivorFace n).succAbove k).val = k.val
    rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
    rfl
  · have hkface : identitySurvivorFace n ≤ k.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, identitySurvivorFace]
      omega
    have hbranch : ¬
        ((identitySurvivorFace n).succAbove k).val < n + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hkface]
      simp only [Fin.val_succ]
      omega
    rw [dite_eq_right hbranch]
    have hkval : k.val = n + 1 := by
      have hklt := k.isLt
      change k.val < n + 2 at hklt
      omega
    change n + 1 - 1 +
      (identitySurvivor n).shuffle.leftHom.toOrderHom
        ((identitySurvivor n).suffixInput
          ((identitySurvivorFace n).succAbove k) (by
            rw [identitySurvivor_gap]
            omega)) = k.val
    have hsuffixVal :
        ((identitySurvivor n).suffixInput
            ((identitySurvivorFace n).succAbove k) (by
              rw [identitySurvivor_gap]
              omega)).val = 1 := by
      change ((identitySurvivorFace n).succAbove k).val -
        (identitySurvivor n).gap = 1
      rw [Fin.succAbove_of_le_castSucc _ _ hkface]
      simp only [Fin.val_succ, identitySurvivor_gap]
      rw [hkval]
      omega
    have hshuffle :
        ((identitySurvivor n).shuffle.leftHom.toOrderHom
          ((identitySurvivor n).suffixInput
            ((identitySurvivorFace n).succAbove k) (by
              rw [identitySurvivor_gap]
              omega))).val =
          ((identitySurvivor n).suffixInput
            ((identitySurvivorFace n).succAbove k) (by
              rw [identitySurvivor_gap]
              omega)).val := by
      simp [identitySurvivor]
      rfl
    rw [hshuffle, hsuffixVal]
    omega

theorem delta_identitySurvivorFace_comp_rightHom (n : ℕ) :
    SimplexCategory.δ (identitySurvivorFace n) ≫
        (identitySurvivor n).rightHom = 𝟙 _ := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.id_toOrderHom,
    ShihIndex.rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
    identitySurvivor_gap]
  by_cases hk : k.val < n + 1
  · have hkface : k.castSucc < identitySurvivorFace n := by
      simp only [Fin.lt_def, Fin.val_castSucc, identitySurvivorFace]
      exact hk
    have hbranch :
        ((identitySurvivorFace n).succAbove k).val < n + 1 := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
      simpa only [Fin.val_castSucc] using hk
    rw [dite_eq_left hbranch]
    change ((identitySurvivorFace n).succAbove k).val = k.val
    rw [Fin.succAbove_of_castSucc_lt _ _ hkface]
    rfl
  · have hkface : identitySurvivorFace n ≤ k.castSucc := by
      simp only [Fin.le_def, Fin.val_castSucc, identitySurvivorFace]
      omega
    have hbranch : ¬
        ((identitySurvivorFace n).succAbove k).val < n + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hkface]
      simp only [Fin.val_succ]
      omega
    rw [dite_eq_right hbranch]
    have hkval : k.val = n + 1 := by
      have hklt := k.isLt
      change k.val < n + 2 at hklt
      omega
    change n + 1 + (identitySurvivor n).p +
      (identitySurvivor n).shuffle.rightHom.toOrderHom
        ((identitySurvivor n).suffixInput
          ((identitySurvivorFace n).succAbove k) (by
            rw [identitySurvivor_gap]
            omega)) = k.val
    have hshuffle :
        ((identitySurvivor n).shuffle.rightHom.toOrderHom
          ((identitySurvivor n).suffixInput
            ((identitySurvivorFace n).succAbove k) (by
              rw [identitySurvivor_gap]
              omega))).val = 0 := by
      simp [identitySurvivor]
    rw [hshuffle]
    simp only [identitySurvivor]
    rw [hkval]

end ShihIndex

theorem delta_zero_comp_leftHom_of_gap_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ i.leftHom =
      eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
        i.shuffle.leftHom ≫
          AlexanderWhitney.frontInclusion (i.p + 1) i.q n
            (i.p_add_one_add_q_eq hi) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
  rw [Fin.zero_succAbove]
  rw [AlexanderWhitney.frontInclusion_toOrderHom]
  exact i.leftHom_succ_of_gap_eq_one hi k

theorem delta_zero_comp_rightHom_of_gap_one {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    SimplexCategory.δ (0 : Fin (n + 2)) ≫ i.rightHom =
      eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
        i.shuffle.rightHom ≫
          AlexanderWhitney.backInclusion (i.p + 1) i.q n
            (i.p_add_one_add_q_eq hi) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply, SimplexCategory.eqToHom_toOrderHom,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
  rw [Fin.zero_succAbove]
  rw [AlexanderWhitney.backInclusion_toOrderHom]
  have h := i.rightHom_succ_of_gap_eq_one hi k
  omega

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The Alexander--Whitney--shuffle summand encoded by a gap-one Shih index.
The simplex words are displayed before applying an arbitrary simplicial
object, so no additive or abelian specialization is built into the indexing. -/
def gapOneAlexanderWhitneyShuffleTerm (X Y : SimplicialObject C) {n : ℕ}
    (i : ShihIndex n) (hi : i.gap = 1) :
    X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) ⟶
      X.obj (Opposite.op ⦋n⦌) ⊗ Y.obj (Opposite.op ⦋n⦌) :=
  shuffleSignZ i.shuffle •
    (X.map (eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
          i.shuffle.leftHom ≫
          AlexanderWhitney.frontInclusion (i.p + 1) i.q n
            (i.p_add_one_add_q_eq hi)).op ⊗ₘ
      Y.map (eqToHom (by rw [i.p_add_one_add_q_eq hi]) ≫
          i.shuffle.rightHom ≫
          AlexanderWhitney.backInclusion (i.p + 1) i.q n
            (i.p_add_one_add_q_eq hi)).op)

/-- The zero upper face of every gap-one Shih index is precisely its positive
Alexander--Whitney--shuffle summand. -/
theorem shihGapOneZeroBoundaryTerm_eq
    (X Y : SimplicialObject C) {n : ℕ} (i : ShihIndex n)
    (hi : i.gap = 1) :
    shihUpperBoundaryTerm X Y n i 0 =
      gapOneAlexanderWhitneyShuffleTerm X Y i hi := by
  unfold shihUpperBoundaryTerm shihSummand
    gapOneAlexanderWhitneyShuffleTerm
  simp only [Fin.val_zero, pow_zero, one_smul, Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft := congrArg (fun f => X.map f.op)
    (delta_zero_comp_leftHom_of_gap_one i hi)
  have hright := congrArg (fun f => Y.map f.op)
    (delta_zero_comp_rightHom_of_gap_one i hi)
  rw [i.sign_of_gap_eq_one hi]
  have htensor := congrArg₂ MonoidalCategory.tensorHom hleft hright
  simpa [SimplicialObject.δ] using
    congrArg (fun f => shuffleSignZ i.shuffle • f) htensor

theorem shihIdentitySurvivor_eq_neg_id (X Y : SimplicialObject C) (n : ℕ) :
    shihUpperBoundaryTerm X Y (n + 1) (ShihIndex.identitySurvivor n)
      (ShihIndex.identitySurvivorFace n) =
        -𝟙 (X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌)) := by
  unfold shihUpperBoundaryTerm shihSummand
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft := congrArg (fun f => X.map f.op)
    (ShihIndex.delta_identitySurvivorFace_comp_leftHom n)
  have hright := congrArg (fun f => Y.map f.op)
    (ShihIndex.delta_identitySurvivorFace_comp_rightHom n)
  have htensor :
      (X.map (ShihIndex.identitySurvivor n).leftHom.op ≫
          X.δ (ShihIndex.identitySurvivorFace n)) ⊗ₘ
        (Y.map (ShihIndex.identitySurvivor n).rightHom.op ≫
          Y.δ (ShihIndex.identitySurvivorFace n)) = 𝟙 _ := by
    simpa [SimplicialObject.δ] using
      congrArg₂ MonoidalCategory.tensorHom hleft hright
  rw [htensor, ShihIndex.identitySurvivor_sign, smul_smul]
  have hcoeff :
      ((-1 : ℤ) ^ (ShihIndex.identitySurvivorFace n).val) *
          (-1 : ℤ) ^ n = -1 := by
    calc
      _ = (-1 : ℤ) ^ (n + 1 + n) := by
        simp only [ShihIndex.identitySurvivorFace, pow_add]
      _ = (-1 : ℤ) ^ (2 * n + 1) := by congr 1; omega
      _ = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hcoeff]
  simp

end AlgebraicTopology.EilenbergZilber
