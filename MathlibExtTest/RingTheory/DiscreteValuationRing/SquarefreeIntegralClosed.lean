/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.SquarefreeIntegralClosed

@[expose] public section

-- Consumer with the original binders.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map
      (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F ϖ ^ n * x ∈
      Algebra.adjoin O {α}) :
    IsIntegrallyClosedIn (Algebra.adjoin O {α}) F :=
  IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
    hϖ hα hsq hgen

