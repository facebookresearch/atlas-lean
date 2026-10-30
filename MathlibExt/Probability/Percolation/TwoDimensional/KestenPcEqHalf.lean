/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessTheorem
public import MathlibExt.Probability.Percolation.TildePc
public import MathlibExt.Probability.Percolation.TwoDimensional.Kesten

/-!
# Kesten's theorem `p_c(ℤ²) = 1/2` from a self-dual crossing function

Kesten's theorem states that the critical probability of bond percolation on `ℤ²` is `1/2`. This
file reduces it to properties of a crossing function `cross : ℝ≥0 → ℕ → ℝ`, using the sharpness
of the phase transition (`StatMech.Percolation.sharp_phase_transition`, proved in the library):
below `p̃_c = p_c` the one-arm probability decays exponentially.

* Upper half `p_c ≤ 1/2` (`kesten_pc_le_half`): if `cross` is monotone in `p`, equals `1/2` at
  `p = 1/2`, and tends to `0` whenever the one-arm probability decays exponentially, then no
  `p > 1/2` lies below `p̃_c`.
* Lower half `1/2 ≤ p_c` (`StatMech.TwoDim.half_le_pc`, in `TwoDimensional.Kesten`).

The name `KestenPcEqHalf` refers to the use of the proved sharpness theorem instead of a sharpness
hypothesis; the statements are **not** unconditional: they take `cross` and the hypotheses
`hmono`, `hdualHalf`, `hpercToOne`, `hdecayToZero`.

## Main results

* `StatMech.TwoDim.kesten_pc_le_half`: `p_c(2) ≤ 1/2`.
* `StatMech.TwoDim.kesten_pc_eq_half`: `p_c(2) = 1/2`.

## Implementation notes

Since `cross` is arbitrary, the hypotheses are close to the conclusion: given `hdualHalf`,
`hpercToOne` is equivalent to `θ(1/2) = 0`; with `cross p n = 1/2` for `p ≤ 1/2` and `1` for
`p > 1/2`, `hmono` and `hdualHalf` hold and `hdecayToZero` says that the one-arm probability does
not decay exponentially for `p > 1/2`. No instance of `cross` is constructed in the library. For
the intended instance (`cross p n` the probability of a left–right crossing of an `(n + 1) × n`
rectangle) the missing inputs are:

* `hdualHalf`: self-duality of that rectangle at `p = 1/2` (the planar-duality dichotomy);
* `hpercToOne`: Harris's theorem `θ(1/2) = 0` (via Zhang's argument, cf.
  `StatMech.TwoDim.kzh_corLowerBound`);
* `hmono`: monotonicity of an increasing event in `p` (standard coupling);
* `hdecayToZero`: a union bound over starting points of the crossing, as in
  `StatMech.TwoDim.kcd_horizontal_tendsto_zero_of_exp` (proved there for the square
  `[0, n]²`, not for the `(n + 1) × n` rectangle).

## References

* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960), 13–20.
* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Chapter 11.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace StatMech

namespace TwoDim

open StatMech.Percolation StatMech.Lattice

/-- Upper half of **Kesten's theorem**, `p_c(ℤ²) ≤ 1/2` (Kesten, 1980), conditional on a crossing
function `cross` that is monotone in `p` (`hmono`), equals `1/2` at `p = 1/2` (`hdualHalf`), and
tends to `0` whenever the one-arm probability decays exponentially (`hdecayToZero`). Sharpness of
the phase transition is used in its proved form. See the module docstring for what the
hypotheses still require. -/
theorem kesten_pc_le_half
    (cross : ℝ≥0 → ℕ → ℝ)
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 ≤ (1 / 2 : ℝ≥0) := by
  obtain ⟨hsharp, hsub, -⟩ := sharp_phase_transition (d := 2) (by norm_num)
  rw [← hsharp]
  refine csSup_le_iff' ?_ |>.mpr ?_
  · exact ⟨1, fun _ hp => (mem_tildePcSet.mp hp).1⟩
  · intro p hp
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hp1, -⟩ := mem_tildePcSet.mp hp
    have hto0 : Tendsto (cross p) atTop (𝓝 0) := hdecayToZero p hp1 (hsub p hp hp1)
    have hge : ∀ n, (1 / 2 : ℝ) ≤ cross p n := fun n => by
      have hmn := hmono n (1 / 2) p (le_of_lt hlt)
      rwa [hdualHalf n] at hmn
    have hlimge : (1 / 2 : ℝ) ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hto0
        (Filter.Eventually.of_forall hge)
    norm_num at hlimge

/-- **Kesten's theorem** `p_c(ℤ²) = 1/2` for bond percolation (Kesten, "The critical probability
of bond percolation on the square lattice equals 1/2", 1980), conditional on a crossing function
`cross` satisfying `hmono`, `hdualHalf`, `hpercToOne` and `hdecayToZero`.

This is a reduction, not a proof of Kesten's theorem: `hdualHalf` and `hpercToOne` together are
equivalent to `θ(1/2) = 0`, and the inputs still missing for a concrete crossing function are
listed in the module docstring.

See also `StatMech.Universality.kesten_pc_eq_half_of_bxp`, a different conditional form (stated
for `criticalProbability`, with a self-dual box family, Zhang's lower bound and a sharp-threshold
statement as hypotheses). -/
theorem kesten_pc_eq_half (h12 : (1 / 2 : ℝ≥0) ≤ 1)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hpercToOne : 0 < theta 2 (1 / 2) h12 →
      Tendsto (cross (1 / 2)) atTop (𝓝 1))
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 = (1 / 2 : ℝ≥0) :=
  le_antisymm
    (kesten_pc_le_half cross hmono hdualHalf hdecayToZero)
    (half_le_pc h12 cross hdualHalf hpercToOne)

end TwoDim

end StatMech
