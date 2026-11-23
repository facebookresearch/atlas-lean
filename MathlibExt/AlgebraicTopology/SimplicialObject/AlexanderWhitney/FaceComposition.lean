/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplexCategory.Subinterval
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

/-!
# Front and back face composition formulas

Front and back inclusions in the simplex category satisfy explicit composition
formulas with coface maps. Applying simplicial objects gives the corresponding
front-face and back-face identities, including the complementary faces that
enter the Alexander-Whitney differential calculation.
-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace AlgebraicTopology.AlexanderWhitney

theorem frontInclusion_comp_delta (p q : ℕ) (i : Fin (p + 2)) :
    SimplexCategory.δ i ≫
        frontInclusion (p + 1) q (p + q + 1) (by omega) =
      frontInclusion p q (p + q) rfl ≫
        SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) := by
  simpa [frontInclusion] using
    SimplexCategory.δ_comp_subinterval (j := 0) (l := p) (n := p + q)
      (by omega) i

theorem backInclusion_comp_delta (p q : ℕ) (i : Fin (q + 2)) :
    SimplexCategory.δ i ≫
        backInclusion p (q + 1) (p + q + 1) (by omega) =
      backInclusion p q (p + q) rfl ≫
        SimplexCategory.δ (⟨p + i.val, by omega⟩ : Fin (p + q + 2)) := by
  simpa [backInclusion] using
    SimplexCategory.δ_comp_subinterval (j := p) (l := q) (n := p + q)
      (by omega) i

theorem frontFace_comp_delta
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    (p q : ℕ) (i : Fin (p + 2)) :
    frontFace X (show (p + 1) + q = p + q + 1 by omega) ≫ X.δ i =
      X.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) ≫
        frontFace X (show p + q = p + q by rfl) := by
  simpa [frontFace, SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (frontInclusion_comp_delta p q i)

theorem backFace_comp_delta
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    (p q : ℕ) (i : Fin (q + 2)) :
    backFace X (show p + (q + 1) = p + q + 1 by omega) ≫ X.δ i =
      X.δ (⟨p + i.val, by omega⟩ : Fin (p + q + 2)) ≫
        backFace X (show p + q = p + q by rfl) := by
  simpa [backFace, SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (backInclusion_comp_delta p q i)

theorem backInclusion_succ_left (p q : ℕ) (i : Fin (p + 1)) :
    backInclusion (p + 1) q (p + q + 1) (by omega) =
      backInclusion p q (p + q) rfl ≫
        SimplexCategory.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  have hk : k.val ≤ q := by simpa using Nat.le_of_lt_succ k.isLt
  change k.val + (p + 1) = ((⟨i.val, by omega⟩ : Fin (p + q + 2)).succAbove
    (⟨k.val + p, by omega⟩ : Fin (p + q + 1))).val
  rw [Fin.succAbove_of_le_castSucc]
  · simp; omega
  · apply Fin.le_iff_val_le_val.mpr; simp; omega

theorem frontInclusion_succ_right (p q : ℕ) (j : Fin (q + 1)) :
    frontInclusion p (q + 1) (p + q + 1) (by omega) =
      frontInclusion p q (p + q) rfl ≫
        SimplexCategory.δ (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  have hk : k.val ≤ p := by simpa using Nat.le_of_lt_succ k.isLt
  change k.val = ((⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)).succAbove
    (⟨k.val, by omega⟩ : Fin (p + q + 1))).val
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · change k.val < p + 1 + j.val; omega

theorem delta_comp_backFace
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    (p q : ℕ) (i : Fin (p + 1)) :
    X.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) ≫
        backFace X (show p + q = p + q by rfl) =
      backFace X (show (p + 1) + q = p + q + 1 by omega) := by
  simpa [backFace, SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (backInclusion_succ_left p q i).symm

theorem delta_comp_frontFace
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    (p q : ℕ) (j : Fin (q + 1)) :
    X.δ (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) ≫
        frontFace X (show p + q = p + q by rfl) =
      frontFace X (show p + (q + 1) = p + q + 1 by omega) := by
  simpa [frontFace, SimplicialObject.δ] using
    congrArg (fun f => X.map f.op) (frontInclusion_succ_right p q j).symm

end AlgebraicTopology.AlexanderWhitney
