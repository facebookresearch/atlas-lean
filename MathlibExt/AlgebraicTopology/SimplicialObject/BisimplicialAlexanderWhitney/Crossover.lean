/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.DifferentialExpansion
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Crossover

/-!
# Bisimplicial Alexander--Whitney crossover face

At adjacent cuts, the last outer face of the `(p+1,q)` summand is the same
map as the zeroth inner face of the `(p,q+1)` summand.  This is the geometric
crossover equality underlying cancellation of the two signed boundary
terms.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasCountableCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

omit [Limits.HasCountableCoproducts A] in
/-- Last-outer and zeroth-inner crossover equality for adjacent cuts. -/
theorem crossover_face_eq (p q n : ℕ) (h : p + q = n) :
    faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
      (B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))).app
        (Opposite.op ⦋q⦌) =
    faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
      (B.obj (Opposite.op ⦋p⦌)).δ
        (⟨0, by omega⟩ : Fin (q + 2)) := by
  subst n
  let outerLast := B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))
  have hbackNat := AlgebraicTopology.AlexanderWhitney.backFace_naturality
    outerLast (show (p + 1) + q = p + q + 1 by omega)
  have hfront := congrArg
    (fun k => k.app (Opposite.op ⦋p + q + 1⦌))
    (AlgebraicTopology.AlexanderWhitney.frontFace_last_crossover
      (C := SimplicialObject A) B p q)
  change (AlgebraicTopology.AlexanderWhitney.frontFace
      (C := SimplicialObject A) B
        (show (p + 1) + q = p + q + 1 by omega)).app
          (Opposite.op ⦋p + q + 1⦌) ≫
      outerLast.app (Opposite.op ⦋p + q + 1⦌) =
    (AlgebraicTopology.AlexanderWhitney.frontFace
      (C := SimplicialObject A) B
        (show p + (q + 1) = p + q + 1 by omega)).app
          (Opposite.op ⦋p + q + 1⦌) at hfront
  have hback := AlgebraicTopology.AlexanderWhitney.backFace_zero_crossover
    (C := A) (B.obj (Opposite.op ⦋p⦌)) p q
  unfold faceToBidegreeOfEq
  let f₁ := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show (p + 1) + q = p + q + 1 by omega)).app
        (Opposite.op ⦋p + q + 1⦌)
  let b₁ := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p + 1⦌))
      (show (p + 1) + q = p + q + 1 by omega)
  let oN := outerLast.app (Opposite.op ⦋p + q + 1⦌)
  let oq := outerLast.app (Opposite.op ⦋q⦌)
  let bt := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌))
      (show (p + 1) + q = p + q + 1 by omega)
  let f₀ := (AlgebraicTopology.AlexanderWhitney.frontFace
    (C := SimplicialObject A) B
      (show p + (q + 1) = p + q + 1 by omega)).app
        (Opposite.op ⦋p + q + 1⦌)
  let b₀ := AlgebraicTopology.AlexanderWhitney.backFace
    (B.obj (Opposite.op ⦋p⦌))
      (show p + (q + 1) = p + q + 1 by omega)
  let i₀ := (B.obj (Opposite.op ⦋p⦌)).δ
    (⟨0, by omega⟩ : Fin (q + 2))
  change (f₁ ≫ b₁) ≫ oq = (f₀ ≫ b₀) ≫ i₀
  exact (Category.assoc f₁ b₁ oq).trans
    ((f₁ ≫= hbackNat).trans
      ((Category.assoc f₁ oN bt).symm.trans
        ((hfront =≫ bt).trans
          ((f₀ ≫= hback).trans (Category.assoc f₀ b₀ i₀).symm))))

end AlgebraicTopology.BisimplicialAlexanderWhitney
