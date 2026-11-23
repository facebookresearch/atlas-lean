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
`D(t) = D0 + f * (P0 - P(t))` receiving branch fraction `f` of the
decayed parents, the branch-weighted total `P(t) + D(t) / f` equals its
initial value `P0 + D0 / f`.

## i. Overview

Physical domain: decay constant `λ > 0`, initial parent and daughter
inventories `P0 ≥ 0` and `D0 ≥ 0`, branch fraction `0 < f ≤ 1`, and
elapsed time `t ≥ 0`. `parent_daughter_branch_conservation_physical`
states the conservation law on this domain.
`parent_daughter_branch_conservation` is its unrestricted algebraic
extension: it holds for every real `λ`, `P0`, `D0`, `t` and every
`f ≠ 0`, and only on the physical domain does it describe a decaying
parent and its daughter; for `f < 0` or `f > 1`, negative inventories,
or `λ < 0` (exponential growth) it is an identity of the formulas only.

Dividing the daughter by `f` accounts for the parents that decayed
down other branches: only a fraction `f` of each decayed parent lands
in this daughter, so the daughter counts `f` times the decayed-parent
total. The proof is pure algebra (`field_simp`, `ring`); no
exponential identities are needed, and the decay constant `λ` plays
no role beyond defining `P(t)`.

## ii. Key results

- `EarthScience.parent_daughter_branch_conservation_physical`: on the
  physical domain, the branch-weighted total is conserved.
- `EarthScience.parent_daughter_branch_conservation`: the same
  identity for all real parameters with `f ≠ 0` (algebraic
  extension).

## iii. References

- `field_simp`, `ring` (Mathlib tactics).
-/

@[expose] public section

namespace EarthScience

/-- Branch-weighted conservation as an unrestricted algebraic identity:
for every real `lam`, `P0`, `D0`, `t` and every `f ≠ 0`, with
`P(t) = P0 * exp (-λ t)` and `D(t) = D0 + f * (P0 - P(t))`, the total
`P(t) + D(t) / f` equals `P0 + D0 / f`. It describes a closed
parent/daughter decay system only on the physical domain `λ > 0`,
`P0 ≥ 0`, `D0 ≥ 0`, `0 < f ≤ 1`, `t ≥ 0`; see
`parent_daughter_branch_conservation_physical`. -/
theorem parent_daughter_branch_conservation {lam P0 D0 f t : ℝ} (hf : f ≠ 0) :
    (P0 * Real.exp (-lam * t))
      + (D0 + f * (P0 - P0 * Real.exp (-lam * t))) / f
      = P0 + D0 / f := by
  field_simp
  ring

/-- A closed single-step parent/daughter system conserves nuclei after
accounting for the branch fraction: for a decay constant `λ > 0`, initial
parent and daughter inventories `P0 ≥ 0` and `D0 ≥ 0`, a branch fraction
`0 < f ≤ 1` and an elapsed time `t ≥ 0`, the parent
`P(t) = P0 * exp (-λ t)` and the daughter `D(t) = D0 + f * (P0 - P(t))`
satisfy `P(t) + D(t) / f = P0 + D0 / f`. Only `f ≠ 0` enters the proof
(`parent_daughter_branch_conservation`); the other hypotheses state the
physical domain. -/
theorem parent_daughter_branch_conservation_physical {lam P0 D0 f t : ℝ}
    (_hlam : 0 < lam) (_hP0 : 0 ≤ P0) (_hD0 : 0 ≤ D0) (hf : 0 < f) (_hf1 : f ≤ 1)
    (_ht : 0 ≤ t) :
    (P0 * Real.exp (-lam * t))
      + (D0 + f * (P0 - P0 * Real.exp (-lam * t))) / f
      = P0 + D0 / f :=
  parent_daughter_branch_conservation hf.ne'

end EarthScience
