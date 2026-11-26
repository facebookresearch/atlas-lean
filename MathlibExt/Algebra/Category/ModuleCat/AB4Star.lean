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
# Exact products of modules at a common universe height

Let R be a ring in universe v, choose a further universe u, and put W=max(u,v). The category of
left R-modules with carriers in W satisfies AB4*: products indexed by types in W preserve short
exact sequences.

For a W-indexed family 0→A_i→B_i→C_i→0, the product row 0→∏_i A_i→∏_i B_i→∏_i C_i→0 is short
exact. Product morphisms act coordinatewise, and exactness is inherited from the underlying
abelian groups.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

/-- Let R be a ring in universe v and W=max(u,v) for an arbitrary further universe u. The category
ModuleCat_W(R) satisfies AB4*. Thus for every family of short exact R-module rows indexed by a
type I in W, their product row is short exact. The scalar universe and extra carrier height
remain independent. -/
instance (priority := 100) ab4StarOfAnyUniverse (R : Type v) [Ring R] :
    AB4Star (ModuleCat.{max u v} R) where
  ofShape J := HasExactLimitsOfShape.domain_of_functor (Discrete J)
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})

end ModuleCat
