/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.GradedPairing
public import MathlibExt.Algebra.Category.Grp.Monoidal

/-! # Actual original tensor pairing tuple law on exact native complex data -/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s x y z t u v
open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

/-- The original native graded pairing has literal tensor cup values under
its original factor and target tuple evaluators. -/
def nativeGradedPairingTupleProperty
    {K₁ K₂ K₃ : CochainComplex AddCommGrpCat.{s} ℕ}
    (P : HomologicalComplex.CochainGradedPairing K₁ K₂ K₃)
    (T : ℕ → Type t) (U : ℕ → Type u) (V : ℕ → Type v)
    (X : Type x) (Y : Type y) (Z : Type z)
    (left : ∀ n, K₁.X n → T n → X)
    (right : ∀ n, K₂.X n → U n → Y)
    (target : ∀ n, K₃.X n → V n → Z)
    (front : ∀ p q, V (p + q) → T p)
    (back : ∀ p q, V (p + q) → U q)
    (pair : X → Y → Z) : Prop :=
  ∀ p q (a : K₁.X p) (b : K₂.X q) (t : V (p + q)),
    target (p + q) ((P.pair p q).hom (a ⊗ₜ[ℤ] b)) t =
      pair (left p a (front p q t)) (right q b (back p q t))

end CategoryTheory
