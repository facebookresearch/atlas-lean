/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundarySurvivors
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Signs
/-!
# The zero-cut survivor in the Shih boundary

The last face of the terminal gap-one index supplies the Alexander--Whitney
cut of left degree zero.  This is the one cut not indexed by the zero faces of
the gap-one Shih family.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial SimplexCategory
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

namespace ShihIndex

/-- The terminal gap-one index whose last face gives the zero-left-degree
Alexander--Whitney cut. -/
def zeroCutSurvivor (n : ℕ) : ShihIndex (n + 1) where
  p := ⟨0, by omega⟩
  q := ⟨n, by simp⟩
  shuffle := Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle n)
    (Fin.last 1)

/-- The last face of `zeroCutSurvivor`. -/
def zeroCutSurvivorFace (n : ℕ) : Fin (n + 3) := Fin.last (n + 2)

@[simp]
theorem zeroCutSurvivor_gap (n : ℕ) :
    (zeroCutSurvivor n).gap = 1 := by
  simp [zeroCutSurvivor, gap]

@[simp]
theorem zeroCutSurvivor_sign (n : ℕ) :
    (zeroCutSurvivor n).sign = (-1 : ℤ) ^ n := by
  rw [sign, zeroCutSurvivor_gap]
  simp only [zeroCutSurvivor, one_add_one_eq_two, neg_one_sq, one_mul]
  have h := Shuffle.shuffleSignZ_leftBoundaryShuffle
    (Shuffle.leftUnitShuffle n) (Fin.last 1)
  simp only [Shuffle.leftBoundaryIndex_last, Fin.val_last,
    Shuffle.leftUnitShuffle_sign] at h
  have h' :
      (-1 : ℤ) ^ (n + 1) *
          shuffleSignZ
            (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle n)
              (Fin.last 1)) = -1 := by
    simpa [Nat.add_comm] using h
  calc
    shuffleSignZ
          (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle n) (Fin.last 1)) =
        ((-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1)) *
          shuffleSignZ
            (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle n)
              (Fin.last 1)) := by rw [← pow_add]; simp
    _ = (-1 : ℤ) ^ (n + 1) *
          (((-1 : ℤ) ^ (n + 1)) *
            shuffleSignZ
              (Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle n)
                (Fin.last 1))) := by ring
    _ = (-1 : ℤ) ^ (n + 1) * (-1) := by rw [h']
    _ = (-1 : ℤ) ^ n := by rw [pow_succ]; ring

set_option backward.isDefEq.respectTransparency false in
theorem delta_zeroCutSurvivorFace_comp_leftHom (n : ℕ) :
    SimplexCategory.δ (zeroCutSurvivorFace n) ≫
        (zeroCutSurvivor n).leftHom =
      SimplexCategory.const ⦋n + 1⦌ ⦋n + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply,
    ShihIndex.leftHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply, zeroCutSurvivor_gap]
  have hlast : k.castSucc < zeroCutSurvivorFace n := by
    simp [zeroCutSurvivorFace]
  rw [Fin.succAbove_of_castSucc_lt _ _ hlast]
  change (if _hk : k.castSucc.val < 1 then _ else _) = _
  split
  · rename_i hk
    apply Fin.ext
    change k.val = 0
    have hk' : k.val < 1 := by simpa only [Fin.val_castSucc] using hk
    omega
  · rename_i hk
    apply Fin.ext
    simp only [Fin.val_castSucc] at hk
    simp only [zeroCutSurvivor, suffixInput, ShihIndex.gap,
      Fin.val_castSucc, Fin.val_zero, SimplexCategory.const,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk]
    let z : Fin (0 + n + 1) := ⟨k.val - 1, by
      have hklt := k.isLt
      change k.val < n + 2 at hklt
      omega⟩
    have hinput :
        (⟨k.val - 1, by
            have hklt := k.isLt
            change k.val < n + 2 at hklt
            change k.val - 1 < (0 + 1 + n) + 1
            omega⟩ : Fin (0 + 1 + n + 1)) =
          (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle n)
              (Fin.last 1)).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [Shuffle.leftBoundaryIndex_last, Fin.succAbove_last,
        Fin.val_castSucc, Fin.val_cast, z]
    have hboundary := Shuffle.leftHom_leftBoundaryShuffle_succAbove
      (Shuffle.leftUnitShuffle n) (Fin.last 1) z
    simp only [show n + 1 - 0 - n = 1 by omega]
    rw [hinput]
    rw [hboundary]
    simp

set_option backward.isDefEq.respectTransparency false in
theorem delta_zeroCutSurvivorFace_comp_rightHom (n : ℕ) :
    SimplexCategory.δ (zeroCutSurvivorFace n) ≫
        (zeroCutSurvivor n).rightHom =
      𝟙 ⦋n + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.id_toOrderHom,
    ShihIndex.rightHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply, zeroCutSurvivor_gap]
  have hlast : k.castSucc < zeroCutSurvivorFace n := by
    simp [zeroCutSurvivorFace]
  rw [Fin.succAbove_of_castSucc_lt _ _ hlast]
  change (if _hk : k.castSucc.val < 1 then _ else _) = _
  split
  · rename_i hk
    apply Fin.ext
    rfl
  · rename_i hk
    apply Fin.ext
    simp only [Fin.val_castSucc] at hk
    simp only [zeroCutSurvivor, suffixInput, ShihIndex.gap,
      Fin.val_castSucc]
    let z : Fin (0 + n + 1) := ⟨k.val - 1, by
      have hklt := k.isLt
      change k.val < n + 2 at hklt
      omega⟩
    have hinput :
        (⟨k.val - 1, by
            have hklt := k.isLt
            change k.val < n + 2 at hklt
            change k.val - 1 < (0 + 1 + n) + 1
            omega⟩ : Fin (0 + 1 + n + 1)) =
          (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle n)
              (Fin.last 1)).succAbove (Fin.cast (by omega) z) := by
      apply Fin.ext
      simp only [Shuffle.leftBoundaryIndex_last, Fin.succAbove_last,
        Fin.val_castSucc, Fin.val_cast, z]
    have hright := Shuffle.rightHom_leftBoundaryShuffle_succAbove
      (Shuffle.leftUnitShuffle n) (Fin.last 1) z
    simp only [show n + 1 - 0 - n = 1 by omega]
    rw [hinput]
    rw [hright]
    simp [z]
    omega

end ShihIndex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The degree-zero-left-cut Alexander--Whitney/shuffle summand. -/
def zeroCutAlexanderWhitneyShuffleTerm (X Y : SimplicialObject C) (n : ℕ) :
    X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) ⟶
      X.obj (Opposite.op ⦋n + 1⦌) ⊗ Y.obj (Opposite.op ⦋n + 1⦌) :=
  X.map (SimplexCategory.const ⦋n + 1⦌ ⦋n + 1⦌ 0).op ⊗ₘ 𝟙 _

/-- The terminal last face is exactly the missing zero-left-degree
Alexander--Whitney/shuffle summand. -/
theorem shihZeroCutSurvivor_eq (X Y : SimplicialObject C) (n : ℕ) :
    shihUpperBoundaryTerm X Y (n + 1) (ShihIndex.zeroCutSurvivor n)
        (ShihIndex.zeroCutSurvivorFace n) =
      zeroCutAlexanderWhitneyShuffleTerm X Y n := by
  unfold shihUpperBoundaryTerm shihSummand
    zeroCutAlexanderWhitneyShuffleTerm
  simp only [Preadditive.zsmul_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  have hleft := congrArg (fun f => X.map f.op)
    (ShihIndex.delta_zeroCutSurvivorFace_comp_leftHom n)
  have hright := congrArg (fun f => Y.map f.op)
    (ShihIndex.delta_zeroCutSurvivorFace_comp_rightHom n)
  have htensor :
      (X.map (ShihIndex.zeroCutSurvivor n).leftHom.op ≫
          X.δ (ShihIndex.zeroCutSurvivorFace n)) ⊗ₘ
        (Y.map (ShihIndex.zeroCutSurvivor n).rightHom.op ≫
          Y.δ (ShihIndex.zeroCutSurvivorFace n)) =
      X.map (SimplexCategory.const ⦋n + 1⦌ ⦋n + 1⦌ 0).op ⊗ₘ 𝟙 _ := by
    simpa [SimplicialObject.δ] using
      congrArg₂ MonoidalCategory.tensorHom hleft hright
  rw [htensor, ShihIndex.zeroCutSurvivor_sign, smul_smul]
  have hcoeff :
      (-1 : ℤ) ^ (ShihIndex.zeroCutSurvivorFace n).val *
          (-1 : ℤ) ^ n = 1 := by
    rw [← pow_add]
    have heven : (ShihIndex.zeroCutSurvivorFace n).val + n =
        2 * (n + 1) := by
      change n + 2 + n = 2 * (n + 1)
      omega
    rw [heven, pow_mul]
    norm_num
  rw [hcoeff]
  simp

end AlgebraicTopology.EilenbergZilber
