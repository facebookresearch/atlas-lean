/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.TraceCard

/-! Kernel-checked clients of the trace-counting API. -/

open Cslib.MachineLearning.PACLearning

namespace CSLibExtTest.MachineLearning.PACLearning.TraceCard

/-- The two constant hypotheses, as a finite class given by a list. -/
private abbrev constantsList : List (ℕ → Bool) := [fun _ => false, fun _ => true]

-- At most `2 ^ 3` traces on three points (the actual count is `2`).
example : (finiteTraces constantsList {0, 1, 2}).card ≤ 2 ^ 3 := by
  rw [finiteTraces_eq_traceFamily]
  exact card_traceFamily_le_two_pow _ _

-- Both traces of a one-point sample are realized, so the constants shatter it.
example : SetShatters {c | c ∈ constantsList} ↑({0} : Finset ℕ) := by
  rw [setShatters_iff_card_traceFamily, ← finiteTraces_eq_traceFamily]
  decide

-- Only `2` of the `4` traces of a two-point sample are realized: no shattering.
example : ¬ SetShatters {c | c ∈ constantsList} ↑({0, 1} : Finset ℕ) := by
  rw [setShatters_iff_card_traceFamily, ← finiteTraces_eq_traceFamily]
  decide

-- The same failure, stated as a missing trace.
example : traceFamily {c | c ∈ constantsList} {0, 1} ≠ Finset.univ := by
  rw [Ne, traceFamily_eq_univ_iff, setShatters_iff_card_traceFamily,
    ← finiteTraces_eq_traceFamily]
  decide

-- Empty sample: a nonempty class realizes its single trace and shatters `∅`.
example : SetShatters {c | c ∈ constantsList} ↑(∅ : Finset ℕ) := by
  rw [setShatters_iff_card_traceFamily, ← finiteTraces_eq_traceFamily]
  decide

-- Empty sample: the empty class realizes no trace and does not shatter `∅`.
example : ¬ SetShatters (∅ : ConceptClass ℕ Bool) ↑(∅ : Finset ℕ) := by
  rw [setShatters_iff_card_traceFamily]
  have h : traceFamily (∅ : ConceptClass ℕ Bool) ∅ = ∅ := by
    ext t
    simp
  simp [h]

end CSLibExtTest.MachineLearning.PACLearning.TraceCard
