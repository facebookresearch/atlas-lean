/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction

/-!
# Source-normalized exact-functor parameter action

All source Hom and S-diagonal carriers and the enriched composition
formula are native. The quotient-zero path comes from the actual
Verdier quotient, before K-theory is applied.

Source: BGT1001.2282v4, Sections 5.1, 7.1 and 9.1.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction

open StableInfinityCategoryModels BGTVerdierQuotients

universe u

/-- The fixed constant-zero map is exact on all the actual finite diagrams. -/
theorem_wanted native_zero_exact_functor (C D : StableInfinityCategory.{u}) :
  ZeroExactFunctorSource C D

/-- The full parameter action is the native enriched composition on every simplex. -/
def_wanted native_full_s_parameter_action (C D : StableInfinityCategory.{u}) :
  FullSParameterAction C D

/-- The actual Verdier quotient composite has its full natural zero equivalence. -/
def_wanted native_quotient_zero_path (E : StableExactSequence.{u})
    (Z : ZeroExactFunctorSource E.left E.right) : QuotientZeroPath E Z

/-- Its reverse is the original full zero-to-quotient-composite natural equivalence. -/
def_wanted native_quotient_zero_reverse_path (E : StableExactSequence.{u})
    (Z : ZeroExactFunctorSource E.left E.right) : QuotientZeroReversePath E Z

end MathlibExt.AlgebraicTopology.StableInfinitySParametrizedAction
