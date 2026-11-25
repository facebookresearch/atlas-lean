/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

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

end AlgebraicTopology.AlexanderWhitney
