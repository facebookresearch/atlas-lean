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

* `StatMech.TwoDim.pc_le_half`: `p_c(2) ≤ 1/2`, taking sharpness of the phase transition as
  the hypotheses `hsharp`, `hsub`.

Sharpness is now proved (`StatMech.Percolation.sharp_phase_transition`); the form without
`hsharp`, `hsub` is `StatMech.TwoDim.kesten_pc_le_half`
in `MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf`.

The conditional Harris / lower-half capstones (`theta_half_eq_zero`, `half_le_pc`,
`pc_eq_half` and, in `KestenPcEqHalf`, `kesten_pc_eq_half`) were removed: their
`hdualHalf` + `hpercToOne` hypotheses are together equivalent to `θ(1/2) = 0`, so they
assumed the conclusion instead of proving Harris's theorem. The missing concrete crossing
result belongs in `WantedExt`.

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

end TwoDim

end StatMech
