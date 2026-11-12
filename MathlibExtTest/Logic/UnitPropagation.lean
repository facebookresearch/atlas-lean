/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.UnitPropagation

@[expose] public section

/-- Boundary check: the formula with a unit clause and its
negation derives a unit-propagation conflict. -/
example : UPConflict ({ {(0, true)}, {(0, false)} } :
    Finset (Finset Lit)) :=
  UPConflict.step _ (0, true) (by decide)
    (UPConflict.empty _ (by decide))

/-- Boundary check: the formula containing the empty clause
derives a conflict immediately. -/
example : UPConflict ({ ∅ } : Finset (Finset Lit)) :=
  UPConflict.empty _ (by decide)
