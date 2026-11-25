/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Operad.OperadObj.Hom
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.Types

/-!
# Set operads as the `Type` specialization of `OperadObj`

This module provides the thin `SetOperad` alias. There is one canonical operad
structure, namely `OperadObj`, relative to the canonical `FiniteTensor (Type u)`
instance. No operad axioms, substitution data, unit fields, category instances,
`Comm`, forgetful or evaluation functors, or coercions are duplicated here; the
existing `OperadObj` projections, category instance, and forgetful functor supply
everything.
-/

@[expose] public section

namespace CategoryTheory.Operad

universe u

/-- Set operad as the Cartesian finite-tensor specialization of `OperadObj`.

`SetOperad` is `OperadObj (Type u)` via the canonical `FiniteTensor (Type u)`
instance given by dependent products. It inherits the unit, substitution, and
right/left unit and associativity laws from `OperadObj` without duplication. -/
abbrev SetOperad := OperadObj (Type u)

/-- Morphism of set operads, as a compatibility and discoverability alias.

This is `OperadObj.Hom O P` for the canonical `Type` specialization; it preserves
the enriched unit and substitution. Use the existing `OperadObj` forgetful functor
and category structure for further operations. -/
abbrev SetOperadHom (O P : SetOperad.{u}) := OperadObj.Hom O P

end CategoryTheory.Operad
