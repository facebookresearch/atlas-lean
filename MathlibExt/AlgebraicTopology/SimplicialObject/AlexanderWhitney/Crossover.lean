/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

/-!
# Alexander–Whitney crossover identities

Computes the last front face and the first back face at an Alexander–Whitney
cut. The corresponding simplex inclusions and their images in any simplicial
object satisfy the crossover identities.
-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace AlgebraicTopology.AlexanderWhitney

theorem frontInclusion_last_crossover (p q : ℕ) :
    SimplexCategory.δ (⟨p + 1, by omega⟩ : Fin (p + 2)) ≫
        frontInclusion (p + 1) q (p + q + 1) (by omega) =
      frontInclusion p (q + 1) (p + q + 1) (by omega) := by
  ext i
  change
    ((⟨p + 1, by omega⟩ : Fin (p + 2)).succAbove i).val = i.val
  rw [show (⟨p + 1, by omega⟩ : Fin (p + 2)) = Fin.last (p + 1) by rfl]
  simp

theorem backInclusion_zero_crossover (p q : ℕ) :
    backInclusion (p + 1) q (p + q + 1) (by omega) =
      SimplexCategory.δ (⟨0, by omega⟩ : Fin (q + 2)) ≫
        backInclusion p (q + 1) (p + q + 1) (by omega) := by
  ext i
  change i.val + (p + 1) = (Fin.succ i).val + p
  simp
  omega

theorem frontFace_last_crossover
    {C : Type u} [Category.{v} C] (X : SimplicialObject C) (p q : ℕ) :
    frontFace X (show (p + 1) + q = p + q + 1 by omega) ≫
        X.map (SimplexCategory.δ
          (⟨p + 1, by omega⟩ : Fin (p + 2))).op =
      frontFace X (show p + (q + 1) = p + q + 1 by omega) := by
  rw [frontFace, frontFace, ← X.map_comp]
  change
    X.map ((SimplexCategory.δ (⟨p + 1, by omega⟩ : Fin (p + 2)) ≫
      frontInclusion (p + 1) q (p + q + 1) (by omega)).op) =
      X.map (frontInclusion p (q + 1) (p + q + 1) (by omega)).op
  exact congrArg (fun f => X.map f.op) (frontInclusion_last_crossover p q)

theorem backFace_zero_crossover
    {C : Type u} [Category.{v} C] (X : SimplicialObject C) (p q : ℕ) :
    backFace X (show (p + 1) + q = p + q + 1 by omega) =
      backFace X (show p + (q + 1) = p + q + 1 by omega) ≫
        X.map (SimplexCategory.δ
          (⟨0, by omega⟩ : Fin (q + 2))).op := by
  rw [backFace, backFace, ← X.map_comp]
  change
    X.map (backInclusion (p + 1) q (p + q + 1) (by omega)).op =
      X.map ((SimplexCategory.δ (⟨0, by omega⟩ : Fin (q + 2)) ≫
        backInclusion p (q + 1) (p + q + 1) (by omega)).op)
  exact congrArg (fun f => X.map f.op) (backInclusion_zero_crossover p q)

end AlgebraicTopology.AlexanderWhitney
