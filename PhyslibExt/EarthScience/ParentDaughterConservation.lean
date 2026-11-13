/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Closed parent/daughter conservation with a branch fraction

In a closed single-step parent/daughter system, parent
`P(t) = P0 * exp (-λ t)` and daughter
`D(t) = D0 + f * (P0 - P(t))` receiving branch fraction `f ≠ 0` of the
decayed parents, the branch-weighted total `P(t) + D(t) / f` equals its
initial value `P0 + D0 / f`.

## i. Overview

Dividing the daughter by `f` accounts for the parents that decayed
down other branches: only a fraction `f` of each decayed parent lands
in this daughter, so the daughter counts `f` times the decayed-parent
total. The proof is pure algebra (`field_simp`, `ring`); no
exponential identities are needed, and the decay constant `λ` plays
no role beyond defining `P(t)`.

## ii. Key results

- `EarthScience.parent_daughter_branch_conservation`: the
  branch-weighted total is conserved.

## iii. References

- `field_simp`, `ring` (Mathlib tactics).
-/

@[expose] public section

namespace EarthScience

/-- A closed single-step parent/daughter system conserves nuclei after
accounting for the branch fraction: with parent
`P(t) = P0 * exp (-λ t)` and daughter
`D(t) = D0 + f * (P0 - P(t))` receiving branch fraction `f ≠ 0` of the
decayed parents, the branch-weighted total `P(t) + D(t) / f` equals its
initial value `P0 + D0 / f`. -/
theorem parent_daughter_branch_conservation {lam P0 D0 f t : ℝ} (hf : f ≠ 0) :
    (P0 * Real.exp (-lam * t))
      + (D0 + f * (P0 - P0 * Real.exp (-lam * t))) / f
      = P0 + D0 / f := by
  field_simp
  ring

end EarthScience
