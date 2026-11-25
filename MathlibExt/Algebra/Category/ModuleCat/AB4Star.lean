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

public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Product exactness with independent module and scalar universes

Mathlib's module-category AB4* instance uses the scalar-ring universe for the
module carriers. This instance also permits larger carrier universes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

/-- Products of modules are exact in every carrier universe containing the
scalar universe. The lower priority
leaves Mathlib's existing instance preferred when its universes match. -/
instance (priority := 100) ab4StarOfAnyUniverse (R : Type v) [Ring R] :
    AB4Star (ModuleCat.{max u v} R) where
  ofShape J := HasExactLimitsOfShape.domain_of_functor (Discrete J)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

end ModuleCat
