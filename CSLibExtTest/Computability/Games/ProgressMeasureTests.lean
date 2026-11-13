/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Games.ProgressMeasure
public meta import CSLibExt.Computability.Games.ProgressMeasure

import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the progress-measure verifier

* A three-position game (owners `(even, even, odd)`, priorities `(0, 1, 0)`) whose position `2` is
  even-winning: the truncated lexicographic verifier accepts a certificate finite at `2`, which a
  componentwise-equality order would reject; the costed verifier agrees and stays within its proved
  bound.
* The verifier rejects a constant measure, since the odd-priority edge `1 → 0` needs a strict
  decrease, and accepts the all-`none` measure, which claims nothing.
* The truncated orders ignore components below the priority and let a larger higher component
  outweigh lower ones.
-/

@[expose] public section

namespace Cslib.Games.ProgressMeasure.Tests

/-! ## The truncated order versus componentwise equality -/

/-- A game that separates the truncated lexicographic order from componentwise equality: owners
`(even, even, odd)`,
priorities `(0, 1, 0)`, moves `0 → 0`, `1 → 0`, `2 → 0`, `2 → 1`.
Position `2` is even-winning (every play eventually loops at priority `0`),
but under the old componentwise-equality order no certificate finite at `2`
exists: priority-`0` edges would force `μ₂[1] = μ₀[1] = μ₁[1]`, while the
priority-`1` edge forces `μ₀[1] < μ₁[1]`. Under the truncated lexicographic
order the certificate below is accepted. Source: M. Jurdziński, "Small
progress measures for solving parity games", *Proceedings of STACS 2000*,
LNCS 1770, 290-301. -/
def counterexampleGame : EncodedParityGame 3 where
  owner v := decide (v = 2)
  move v w :=
    decide ((v = 0 ∧ w = 0) ∨ (v = 1 ∧ w = 0) ∨ (v = 2 ∧ w = 0) ∨
      (v = 2 ∧ w = 1))
  priority v := if v = 1 then 1 else 0

/-- A progress-measure certificate for the counterexample game:
`μ₀ = (0, 0)`, `μ₁ = μ₂ = (0, 1)` (tuples indexed by priority). The
priority-`1` edge `1 → 0` holds since `1 > 0` at component `1`; the
priority-`0` edges `2 → 0` and `2 → 1` hold since `(1, 0) ≥ (0, 0)`
and `(1, 0) ≥ (1, 0)` in the truncated lexicographic order at `0`, where
the larger component `1` outweighs the equal component `0`. Source:
M. Jurdziński, "Small progress measures for solving parity games",
*Proceedings of STACS 2000*, LNCS 1770, 290-301. -/
def counterexampleMeasure : Fin 3 → Option (Fin 2 → ℕ) :=
  fun v => some fun k => if (v = 1 ∨ v = 2) ∧ k = 1 then 1 else 0

/-- Regression test: the counterexample certificate is accepted by the
truncated-lexicographic verifier. Under the old componentwise-equality
order this fails, since that order forces `μ₂[1] = μ₀[1] = μ₁[1]` from
the two priority-`0` edges out of `2` while the priority-`1` edge `1 → 0`
forces `μ₀[1] < μ₁[1]`. -/
example : verifyProgress counterexampleGame counterexampleMeasure = true := by
  decide

/-- Regression test: the counterexample certificate is finite at `2`, so it witnesses that
position `2` is even-winning in the equivalence of
`Cslib.ParityGameComplexityWanted.parity_games_np_inter_coNP_wanted`. -/
example : ∃ f, counterexampleMeasure 2 = some f :=
  ⟨_, rfl⟩

/-- Regression test: the costed verifier accepts the counterexample
certificate with the same result as the uncosted verifier. -/
example : (costedVerifyProgress counterexampleGame counterexampleMeasure).1 = true :=
  by decide

/-- Regression test: the costed verifier's cost on the counterexample
game is within the proved bound (`d = 1`, priorities at most `1`). -/
example : (costedVerifyProgress counterexampleGame counterexampleMeasure).2 ≤
    verifyProgressCostBound 3 1 :=
  costedVerifyProgress_cost_le _ _

/-! ## Rejections and the orders themselves -/

/-- The constant measure fails at the odd-priority edge `1 → 0`, which needs a strict decrease. -/
example : verifyProgress counterexampleGame (fun _ => some fun _ => 0 : Fin 3 → Option (Fin 2 → ℕ))
    = false := by
  decide

/-- The all-`none` measure (every position claimed losing for the even player) imposes no
progress requirement, so the verifier accepts it. -/
example :
    verifyProgress counterexampleGame (fun _ => none : Fin 3 → Option (Fin 2 → ℕ)) = true := by
  decide

#guard verifyProgress counterexampleGame counterexampleMeasure

#guard (costedVerifyProgress counterexampleGame counterexampleMeasure).1 ==
  verifyProgress counterexampleGame counterexampleMeasure

#guard !(costedVerifyProgress counterexampleGame
  (fun _ => some fun _ => 0 : Fin 3 → Option (Fin 2 → ℕ))).1

/-- At priority `1` the component `0` is ignored. -/
example : lexGeTrunc (d := 1) 1 ![5, 0] ![0, 0] = true := by decide

/-- The larger component `1` outweighs the smaller component `0`. -/
example : lexGtTrunc (d := 1) 0 ![0, 1] ![7, 0] = true := by decide

/-- Equal tuples are not strictly ordered. -/
example : lexGtTrunc (d := 1) 0 ![3, 4] ![3, 4] = false := by decide

end Cslib.Games.ProgressMeasure.Tests
