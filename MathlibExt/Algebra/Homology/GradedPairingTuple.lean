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

/-!
# Tuple evaluations of graded pairings

Let K₁,K₂,K₃ be nonnegative cochain complexes of abelian groups, and let
P:K₁⊗K₂ → K₃ be a graded pairing over ℤ. Choose arbitrary evaluations
left_p:K₁ᵖ → T_p → X, right_q:K₂ᑫ → U_q → Y and
target_n:K₃ⁿ → V_n → Z, and front and back maps from V_{p+q} to T_p
and U_q. The tuple pairing property says that evaluation of
P_{p,q}(a⊗b) at v equals the chosen value pairing of the two factor
evaluations at front(v) and back(v). The evaluation, tuple and value
types have independent universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s x y z t u v
open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

/-- For a graded pairing P:K₁⊗K₂ → K₃ of nonnegative cochain complexes of
abelian groups, choose tuple types T_p,U_q,V_n, value types X,Y,Z,
evaluations left_p:K₁ᵖ → T_p → X, right_q:K₂ᑫ → U_q → Y,
target_n:K₃ⁿ → V_n → Z, maps front_{p,q}:V_{p+q} → T_p and
back_{p,q}:V_{p+q} → U_q, and pair:X → Y → Z.
The tuple pairing property is the equality, for all p,q,a,b,v,
target_{p+q}(P_{p,q}(a⊗₍ℤ₎b))(v)
=pair(left_p(a)(front_{p,q}(v)),right_q(b)(back_{p,q}(v))). -/
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
