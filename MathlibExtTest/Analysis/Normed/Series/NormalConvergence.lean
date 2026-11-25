/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Series.NormalConvergence
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Tests for normal convergence of series of functions

Exercises `supNormOn`, `ConvergesNormallyOn`, and
`ConvergesLocallyNormallyOn`: the empty-set and zero-series simp lemmas,
monotonicity under shrinking the domain, projection from local convergence
at a point, and a concrete nonzero one-term series on a singleton domain.
-/

@[expose] public section

open Topology
open scoped ENNReal

-- `supNormOn` API: empty set, zero function, domain monotonicity.

example (g : ℝ → ℝ) : supNormOn g ∅ = 0 := supNormOn_empty g

example (S : Set ℝ) : supNormOn (0 : ℝ → ℝ) S = 0 := supNormOn_zero S

example {S T : Set ℝ} (h : T ⊆ S) (g : ℝ → ℝ) : supNormOn g T ≤ supNormOn g S :=
  supNormOn_mono h g

-- `ConvergesNormallyOn` API: empty set, zero series, domain monotonicity.

example (f : ℕ → ℝ → ℝ) : ConvergesNormallyOn f ∅ := convergesNormallyOn_empty f

example (S : Set ℝ) : ConvergesNormallyOn (0 : ℕ → ℝ → ℝ) S :=
  convergesNormallyOn_zero S

example {f : ℕ → ℝ → ℝ} {S T : Set ℝ} (h : ConvergesNormallyOn f S)
    (hTS : T ⊆ S) : ConvergesNormallyOn f T :=
  h.mono hTS

-- `ConvergesLocallyNormallyOn` API: empty set, zero series, domain
-- monotonicity, and projection at a point.

example (f : ℕ → ℝ → ℝ) : ConvergesLocallyNormallyOn f ∅ :=
  convergesLocallyNormallyOn_empty f

example (S : Set ℝ) : ConvergesLocallyNormallyOn (0 : ℕ → ℝ → ℝ) S :=
  convergesLocallyNormallyOn_zero S

example {f : ℕ → ℝ → ℝ} {S T : Set ℝ} (h : ConvergesLocallyNormallyOn f S)
    (hTS : T ⊆ S) : ConvergesLocallyNormallyOn f T :=
  h.mono hTS

example {f : ℕ → ℝ → ℝ} {S : Set ℝ} {x : ℝ} (h : ConvergesLocallyNormallyOn f S)
    (hx : x ∈ S) : ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S) :=
  h.exists_nhds_inter hx

/-- A concrete one-term series on `ℝ`: only the `n = 0` term is nonzero. -/
def oneTermSeries : ℕ → ℝ → ℝ := fun n _ => if n = 0 then 1 else 0

/-- The sup norm of the one-term series on the singleton `{0}` picks out the
active term. -/
theorem supNormOn_oneTermSeries (n : ℕ) :
    supNormOn (oneTermSeries n) ({0} : Set ℝ) = if n = 0 then (1 : ℝ≥0∞) else 0 := by
  have : Nonempty ↥(({0} : Set ℝ)) := ⟨⟨0, rfl⟩⟩
  unfold supNormOn
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl]
    have hbody : ∀ x : ↥(({0} : Set ℝ)),
        ENNReal.ofReal ‖oneTermSeries 0 ↑x‖ = 1 := by
      intro x
      change ENNReal.ofReal ‖(if (0 : ℕ) = 0 then (1 : ℝ) else 0)‖ = 1
      rw [ite_eq_left rfl, norm_one, ENNReal.ofReal_one]
    simp only [hbody]
    exact iSup_const
  · rw [ite_eq_right hn]
    have hbody : ∀ x : ↥(({0} : Set ℝ)),
        ENNReal.ofReal ‖oneTermSeries n ↑x‖ = 0 := by
      intro x
      change ENNReal.ofReal ‖(if n = 0 then (1 : ℝ) else 0)‖ = 0
      rw [ite_eq_right hn, norm_zero, ENNReal.ofReal_zero]
    simp only [hbody]
    exact iSup_const

/-- The active term is genuinely nonzero on the singleton domain. -/
example : supNormOn (oneTermSeries 0) ({0} : Set ℝ) = 1 := by
  rw [supNormOn_oneTermSeries, ite_eq_left rfl]

/-- The one-term series converges normally on the singleton `{0}`: its
sup-norm series is a single nonzero term. -/
theorem oneTermSeries_normal :
    ConvergesNormallyOn oneTermSeries ({0} : Set ℝ) := by
  unfold ConvergesNormallyOn
  rw [tsum_congr supNormOn_oneTermSeries,
    tsum_eq_single 0 (fun b hb => ite_eq_right hb), ite_eq_left rfl]
  exact ENNReal.one_ne_top

/-- The one-term series converges locally normally on the singleton `{0}`. -/
example : ConvergesLocallyNormallyOn oneTermSeries ({0} : Set ℝ) := by
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp [oneTermSeries_normal]⟩
