/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# LIF reset event times

Reset event times with active duration and refractory duration have a constant positive gap and do not accumulate in finite time.
-/

@[expose] public section

open Filter

namespace MathlibExt.Biology.Biophysics.IntegrateAndFire.Trajectory

/-- **LIF event-time gaps.** With active duration `T > 0` and
refractory duration `tref ≥ 0`, successive reset event times
`t n = n * (T + tref)` are separated by the constant gap
`T + tref > 0`. -/
theorem lif_event_gap {T tref : ℝ} (hT : 0 < T) (href : 0 ≤ tref) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (T + tref) - (n : ℝ) * (T + tref) = T + tref ∧
      0 < T + tref := by
  constructor
  · push_cast
    ring
  · linarith

/-- **LIF event times do not accumulate.** The event-time sequence
`t n = n * (T + tref)` tends to infinity, so only finitely many
events occur in any bounded time interval. -/
theorem lif_event_tendsto {T tref : ℝ} (hT : 0 < T) (href : 0 ≤ tref) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * (T + tref)) Filter.atTop Filter.atTop := by
  have hpos : 0 < T + tref := by linarith
  exact Tendsto.atTop_mul_const hpos tendsto_natCast_atTop_atTop

/-- **Zero refractory period.** At `tref = 0` the event gap is
exactly the active duration `T`. -/
theorem lif_event_gap_zero_refractory {T : ℝ} (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (T + 0) - (n : ℝ) * (T + 0) = T := by
  push_cast
  ring



end MathlibExt.Biology.Biophysics.IntegrateAndFire.Trajectory
