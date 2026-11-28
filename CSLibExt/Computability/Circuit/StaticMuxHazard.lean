/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Static mux hazard under transport delay

The two-path multiplexer `(a and b) or (not a and c)` is evaluated with
`b = c = true` while `a` rises once at time zero, under a transport-delay
model with steady initialization before time zero. Delays are
nonnegative reals (`NNReal`), so a delay cannot act as an advance: the
positive path output rises at `d1`, the complemented path output falls
at `d2`, and the output gate adds delay `dor`. When `d2 < d1` the output
is false on `[d2 + dor, d1 + dor)`; otherwise it stays true. Adding the
initialized consensus term `b and c` preserves the static Boolean function
and keeps the output true at all times. Inertial delay and pulse
suppression are outside the scope of this model.

Timed signals are functions `ℝ → Bool` and the path traces are explicit
step functions of the delay parameters. This is the leaf's own minimal
timed-signal interface: no canonical timed-signal representation is used
here, and the step-function path traces mark the exact adapter points.
-/

@[expose] public section

namespace CSLibExt.Computability.Circuit.StaticMuxHazard

/-- The static two-path multiplexer `(a and b) or (not a and c)`. -/
def muxFunction (a b c : Bool) : Bool :=
  (a && b) || (!a && c)

/-- The consensus-repaired multiplexer, adding the term `b and c`. -/
def consensusFunction (a b c : Bool) : Bool :=
  muxFunction a b c || (b && c)

/-- The positive-path trace: false before `d1`, true from `d1` on. -/
noncomputable def positivePath (d1 : NNReal) (t : ℝ) : Bool :=
  (d1 : ℝ) ≤ t

/-- The complemented-path trace: true before `d2`, false from `d2` on. -/
noncomputable def complementedPath (d2 : NNReal) (t : ℝ) : Bool :=
  !((d2 : ℝ) ≤ t)

/-- The transport-delay output trace of the unrepaired multiplexer with
`b = c = true`: the two path traces combined by an output gate delayed
by `dor`. -/
noncomputable def muxTrace (d1 d2 dor : NNReal) (t : ℝ) : Bool :=
  positivePath d1 (t - dor) || complementedPath d2 (t - dor)

/-- The consensus-path trace: `b and c` with `b = c = true`, initialized
before time zero, hence true at all times. -/
def consensusPath (_t : ℝ) : Bool :=
  true

/-- The transport-delay output trace with the consensus path added. -/
noncomputable def repairedTrace (d1 d2 dor : NNReal) (t : ℝ) : Bool :=
  muxTrace d1 d2 dor t || consensusPath (t - dor)

/-- The static multiplexer with `b = c = true` is constantly true. -/
theorem muxFunction_true_true (a : Bool) :
    muxFunction a true true = true := by
  cases a <;> rfl

/-- **Consensus preserves the Boolean function.** For all inputs, adding
the consensus term `b and c` does not change the multiplexer output. -/
theorem consensusFunction_eq_muxFunction (a b c : Bool) :
    consensusFunction a b c = muxFunction a b c := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Before time zero, the output is true: the steady initialization
value. -/
theorem muxTrace_eq_true_of_neg (d1 d2 dor : NNReal) (t : ℝ)
    (ht : t < 0) :
    muxTrace d1 d2 dor t = true := by
  have hd2 : (0 : ℝ) ≤ (d2 : ℝ) := NNReal.coe_nonneg d2
  have hdor : (0 : ℝ) ≤ (dor : ℝ) := NNReal.coe_nonneg dor
  have hneg : ¬ (d2 : ℝ) ≤ t - (dor : ℝ) := by
    have h1 : t - (dor : ℝ) < 0 := by linarith
    linarith
  simp [muxTrace, positivePath, complementedPath, hneg]

/-- **Glitch interval.** When `d2 < d1`, the output is false at every
time in `[d2 + dor, d1 + dor)`. -/
theorem muxTrace_eq_false_of_mem_glitch (d1 d2 dor : NNReal) (t : ℝ)
    (h : d2 < d1)
    (ht : t ∈ Set.Ico ((d2 : ℝ) + (dor : ℝ)) ((d1 : ℝ) + (dor : ℝ))) :
    muxTrace d1 d2 dor t = false := by
  rw [Set.mem_Ico] at ht
  obtain ⟨hlo, hhi⟩ := ht
  have h1 : (d2 : ℝ) ≤ t - (dor : ℝ) := by linarith
  have h2 : ¬ (d1 : ℝ) ≤ t - (dor : ℝ) := by linarith
  simp [muxTrace, positivePath, complementedPath, h1, h2]

/-- Before the glitch can start, the output is true. -/
theorem muxTrace_eq_true_of_lt (d1 d2 dor : NNReal) (t : ℝ)
    (ht : t < (d2 : ℝ) + (dor : ℝ)) :
    muxTrace d1 d2 dor t = true := by
  have hneg : ¬ (d2 : ℝ) ≤ t - (dor : ℝ) := by linarith
  simp [muxTrace, complementedPath, hneg]

/-- From `d1 + dor` on, the output is true. -/
theorem muxTrace_eq_true_of_ge (d1 d2 dor : NNReal) (t : ℝ)
    (ht : (d1 : ℝ) + (dor : ℝ) ≤ t) :
    muxTrace d1 d2 dor t = true := by
  have hpos : (d1 : ℝ) ≤ t - (dor : ℝ) := by linarith
  simp [muxTrace, positivePath, hpos]

/-- **A false output occurs exactly when `d2 < d1`.** -/
theorem exists_muxTrace_eq_false_iff (d1 d2 dor : NNReal) :
    (∃ t : ℝ, muxTrace d1 d2 dor t = false) ↔ d2 < d1 := by
  constructor
  · rintro ⟨t, ht⟩
    simp [muxTrace, positivePath, complementedPath] at ht
    obtain ⟨h1, h2⟩ := ht
    have hlt : (d2 : ℝ) < (d1 : ℝ) := by linarith
    exact_mod_cast hlt
  · intro h
    have hlt : (d2 : ℝ) < (d1 : ℝ) := by exact_mod_cast h
    refine ⟨(d2 : ℝ) + (dor : ℝ), ?_⟩
    apply muxTrace_eq_false_of_mem_glitch _ _ _ _ h
    rw [Set.mem_Ico]
    constructor
    · linarith
    · linarith

/-- When `d1 ≤ d2` there is no glitch: the output is true at all times. -/
theorem muxTrace_eq_true_of_le (d1 d2 dor : NNReal) (t : ℝ)
    (h : d1 ≤ d2) :
    muxTrace d1 d2 dor t = true := by
  have hle : (d1 : ℝ) ≤ (d2 : ℝ) := by exact_mod_cast h
  by_cases h1 : (d1 : ℝ) ≤ t - (dor : ℝ)
  · simp [muxTrace, positivePath, h1]
  · have h2 : ¬ (d2 : ℝ) ≤ t - (dor : ℝ) := by linarith
    simp [muxTrace, positivePath, complementedPath, h1, h2]

/-- **Consensus repair.** In the experiment modeled here (both data inputs
`b` and `c` held true, the select `a` rising once at time `0`, and the
consensus path initialized true before time `0`), the output with the
consensus path added is true at every real time `t`, for every choice of
the three nonnegative delays `d1`, `d2` and `dor`. The repair preserves the
multiplexer's Boolean function (`consensusFunction_eq_muxFunction`), so with
both data inputs false the repaired function is false. -/
theorem repairedTrace_eq_true (d1 d2 dor : NNReal) (t : ℝ) :
    repairedTrace d1 d2 dor t = true := by
  simp [repairedTrace, consensusPath]

/-- **Concrete glitch example.** With `d1 = 2`, `d2 = 1` and `dor = 0`,
the output is true at time `0`, false at time `3 / 2`, and true at time
`3`; the repaired output is true at time `3 / 2`. -/
theorem muxTrace_example :
    muxTrace 2 1 0 0 = true ∧ muxTrace 2 1 0 (3 / 2) = false ∧
      muxTrace 2 1 0 3 = true ∧ repairedTrace 2 1 0 (3 / 2) = true := by
  norm_num [muxTrace, positivePath, complementedPath, repairedTrace, consensusPath]

end CSLibExt.Computability.Circuit.StaticMuxHazard
