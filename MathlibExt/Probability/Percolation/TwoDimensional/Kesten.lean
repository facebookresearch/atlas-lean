/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessFromInputs
public import MathlibExt.Probability.Percolation.TildePc

/-!
# Kesten's theorem from a self-dual crossing function, with sharpness as a hypothesis

Harris's theorem `θ(1/2) = 0` for bond percolation on `ℤ²` gives `p_c ≥ 1/2`. This file proves
the propositional step from a *crossing function* `cross : ℝ≥0 → ℕ → ℝ`: if `cross (1/2) n = 1/2`
for all `n` (self-duality of the `n × (n + 1)` rectangle crossing) and positive percolation at
`1/2` would force `cross (1/2) n → 1`, then `θ(1/2) = 0`.

`cross` is an arbitrary function, so these hypotheses carry all the content: given
`hdualHalf`, the hypothesis `hpercToOne` holds if and only if `θ(1/2) = 0`. The results here are
reductions, not proofs of Harris's theorem.

## Main results

* `StatMech.TwoDim.theta_half_eq_zero`: `θ(1/2) = 0` from `hdualHalf` and `hpercToOne`.
* `StatMech.TwoDim.half_le_pc`: `1/2 ≤ p_c(2)` under the same hypotheses.
* `StatMech.TwoDim.pc_le_half`, `StatMech.TwoDim.pc_eq_half`: `p_c(2) ≤ 1/2` and `p_c(2) = 1/2`,
  taking sharpness of the phase transition as the hypotheses `hsharp`, `hsub`.

Sharpness is now proved (`StatMech.Percolation.sharp_phase_transition`); the forms without
`hsharp`, `hsub` are `StatMech.TwoDim.kesten_pc_le_half` and `StatMech.TwoDim.kesten_pc_eq_half`
in `MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf`.

## References

* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960), 13–20.
* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StatMech

namespace TwoDim

open StatMech.Percolation StatMech.Lattice

/-- Conditional form of **Harris's theorem** `θ(1/2) = 0` on `ℤ²` (Harris, 1960).

`cross` is arbitrary: the hypotheses `hdualHalf` (`cross (1/2) n = 1/2`) and `hpercToOne`
(`θ(1/2) > 0` forces `cross (1/2) n → 1`) together are equivalent to `θ(1/2) = 0`. In the intended
instance `cross p n` is the probability of a left–right crossing of an `(n + 1) × n` rectangle;
there `hdualHalf` is self-duality and `hpercToOne` is the Harris–Zhang argument, neither of which
is proved here. -/
theorem theta_half_eq_zero (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    theta 2 (1 / 2) h12 = 0 := by
  by_contra hne
  have hpos : 0 < theta 2 (1 / 2) h12 :=
    lt_of_le_of_ne (theta_nonneg 2 (1 / 2) h12) (Ne.symm hne)
  have hto1 : Tendsto (cross (1 / 2)) atTop (𝓝 1) := hpercToOne hpos
  have hconst : Tendsto (cross (1 / 2)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have : cross (1 / 2) = fun _ : ℕ => (1 / 2 : ℝ) := funext hdualHalf
    rw [this]; exact tendsto_const_nhds
  have : (1 / 2 : ℝ) = 1 := tendsto_nhds_unique hconst hto1
  norm_num at this

/-- `1/2` is subcritical under the hypotheses of `theta_half_eq_zero`. -/
theorem half_mem_subcriticalSet (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    (1 / 2 : ℝ≥0) ∈ subcriticalSet 2 :=
  ⟨h12, theta_half_eq_zero h12 cross hdualHalf hpercToOne⟩

/-- Lower half of **Kesten's theorem**, `1/2 ≤ p_c(ℤ²)` (Harris, 1960), conditional on the
hypotheses of `theta_half_eq_zero`, which are together equivalent to `θ(1/2) = 0`. -/
theorem half_le_pc (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
    (1 / 2 : ℝ≥0) ≤ pc 2 :=
  le_pc_of_mem_subcriticalSet (half_mem_subcriticalSet h12 cross hdualHalf hpercToOne)

/-- Upper half of Kesten's theorem, `p_c(ℤ²) ≤ 1/2`, with sharpness of the phase transition taken
as the hypotheses `hsharp` (`p̃_c = p_c`) and `hsub` (exponential decay of the one-arm probability
on `p̃_c`'s defining set). Both are now theorems (`StatMech.Percolation.sharp_phase_transition`);
the form without them is `StatMech.TwoDim.kesten_pc_le_half`. The remaining hypotheses are those
of `kesten_pc_le_half`. -/
theorem pc_le_half
    (hsharp : tildePc 2 = pc 2)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 ≤ (1 / 2 : ℝ≥0) := by
  rw [← hsharp]
  refine csSup_le_iff' ?_ |>.mpr ?_
  · exact ⟨1, fun _ hp => (mem_tildePcSet.mp hp).1⟩
  · intro p hp
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hp1, -⟩ := mem_tildePcSet.mp hp
    have hto0 : Tendsto (cross p) atTop (𝓝 0) := hdecayToZero p hp1 (hsub p hp hp1)
    have hge : ∀ n, (1 / 2 : ℝ) ≤ cross p n := fun n => by
      have := hmono n (1 / 2) p (le_of_lt hlt)
      rwa [hdualHalf n] at this
    have hlimge : (1 / 2 : ℝ) ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hto0
        (Filter.Eventually.of_forall hge)
    norm_num at hlimge

/-- Kesten's theorem `p_c(ℤ²) = 1/2`, conditional on the hypotheses of `half_le_pc` and
`pc_le_half` (including sharpness as `hsharp`, `hsub`). The form using the proved sharpness
theorem is `StatMech.TwoDim.kesten_pc_eq_half`; see its docstring for the remaining inputs. -/
theorem pc_eq_half (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (hsharp : tildePc 2 = pc 2)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1))
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 = (1 / 2 : ℝ≥0) :=
  le_antisymm
    (pc_le_half hsharp cross hsub hmono hdualHalf hdecayToZero)
    (half_le_pc h12 cross hdualHalf hpercToOne)

end TwoDim

end StatMech
