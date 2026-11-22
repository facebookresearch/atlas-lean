/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.DataProcessing

/-! # Tests for `MathlibExt.InformationTheory.DataProcessing`

* Exact total variation of explicit PMFs on `Bool`: two point masses (`1`), and the point mass
  at `true` against the fair coin (`1 / 2`).
* The Helstrom identity on both pairs; for the second pair the sum of maxima is computed from the
  definitions, which pins the `1 + tvDist` normalization.
* Data processing (`tvDist_bind_le`) through kernels into other types: a collapsing kernel
  `Bool → PMF Unit` contracts strictly (`1` to `0`), and a relabeling kernel
  `Bool → PMF (Fin 3)` attains equality.
-/

open MathlibExt.Probability.MarkovChainContraction (tvDist tvDist_bind_le)
open MathlibExt.InformationTheory.DataProcessing

namespace MathlibExtTest.InformationTheory.DataProcessing

/-- The fair coin. -/
noncomputable def coin : PMF Bool :=
  PMF.ofFintype (fun _ => 2⁻¹) (by rw [Fintype.sum_bool, ENNReal.inv_two_add_inv_two])

theorem coin_toReal (b : Bool) : (coin b).toReal = 1 / 2 := by
  simp [coin, PMF.ofFintype_apply]

theorem tvDist_pure_pure : tvDist (PMF.pure true) (PMF.pure false) = 1 := by
  simp [tvDist, MathlibExt.Probability.MarkovMixing.tvDist, PMF.pure_apply]
  norm_num

theorem tvDist_pure_coin : tvDist (PMF.pure true) coin = 1 / 2 := by
  simp [tvDist, MathlibExt.Probability.MarkovMixing.tvDist, PMF.pure_apply, coin_toReal]
  norm_num

/-! ### The Helstrom identity -/

/-- Disjoint point masses: the sum of maxima is `1 + 1 = 2`, so one sample identifies the
hypothesis with certainty. -/
example :
    (∑ b, max ((PMF.pure true : PMF Bool) b).toReal ((PMF.pure false : PMF Bool) b).toReal) =
      2 := by
  rw [helstrom_max_sum, tvDist_pure_pure]; norm_num

/-- The point mass at `true` against the fair coin, from the definitions:
`max 1 (1 / 2) + max 0 (1 / 2) = 3 / 2`. -/
theorem sum_max_pure_coin :
    (∑ b, max ((PMF.pure true : PMF Bool) b).toReal (coin b).toReal) = 3 / 2 := by
  simp [PMF.pure_apply, coin_toReal]
  norm_num

/-- Helstrom factor: the identity turns the sum of maxima `3 / 2` into `tvDist = 1 / 2`, the
value computed from the definition of `tvDist`; a different normalization would not match. -/
example : tvDist (PMF.pure true) coin = 1 / 2 := by
  have h := helstrom_max_sum (PMF.pure true) coin
  rw [sum_max_pure_coin] at h
  linarith

/-- Both sides of the identity, computed independently, agree on this pair. -/
example :
    (∑ b, max ((PMF.pure true : PMF Bool) b).toReal (coin b).toReal) =
      1 + tvDist (PMF.pure true) coin := by
  rw [sum_max_pure_coin, tvDist_pure_coin]; norm_num

/-! ### Data processing through kernels into other types -/

/-- The collapsing kernel: every input goes to the point mass on `Unit`. -/
noncomputable abbrev collapse : Bool → PMF Unit := fun _ => PMF.pure ()

/-- Strict contraction: after the collapsing kernel the two laws coincide, so the distance drops
from `1` to `0`. -/
example :
    tvDist ((PMF.pure true).bind collapse) ((PMF.pure false).bind collapse) = 0 ∧
      tvDist ((PMF.pure true).bind collapse) ((PMF.pure false).bind collapse) <
        tvDist (PMF.pure true) (PMF.pure false) := by
  have h0 : tvDist ((PMF.pure true).bind collapse) ((PMF.pure false).bind collapse) = 0 := by
    rw [PMF.pure_bind, PMF.pure_bind]
    exact MathlibExt.Probability.MarkovMixing.tvDist_self _
  refine ⟨h0, ?_⟩
  rw [h0, tvDist_pure_pure]
  norm_num

/-- `tvDist_bind_le` for a kernel from `Bool` to `Unit`. -/
example (p q : PMF Bool) : tvDist (p.bind collapse) (q.bind collapse) ≤ tvDist p q :=
  tvDist_bind_le collapse p q

/-- The relabeling kernel `true ↦ 0`, `false ↦ 2` from `Bool` to `Fin 3`. -/
noncomputable abbrev relabel : Bool → PMF (Fin 3) := fun b => PMF.pure (if b then 0 else 2)

/-- Equality: binding with `relabel` sends the point masses at `true` and `false` to the point
masses at `0` and `2`, still at distance `1`, so the bound of `tvDist_bind_le` is attained. -/
example :
    tvDist ((PMF.pure true).bind relabel) ((PMF.pure false).bind relabel) =
      tvDist (PMF.pure true) (PMF.pure false) := by
  rw [PMF.pure_bind, PMF.pure_bind, tvDist_pure_pure]
  simp [relabel, tvDist, MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_three,
    PMF.pure_apply]
  norm_num

end MathlibExtTest.InformationTheory.DataProcessing
