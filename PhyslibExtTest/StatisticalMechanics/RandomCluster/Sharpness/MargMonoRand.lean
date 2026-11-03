/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MargMonoRand

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MargMonoRand`

* `mmr_margMonoRand_f_at_zero` on `K₂` at `p = 1/2`, `q = 2` for the coordinate observable;
* `mmr_margMonoRand_at_n` (unconditional, any weight);
* `mmr_margRand_f_at_zero_eq`: at step zero the marginal is `f` of the joined code.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MargMonoRand

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.AdaptDisintegration

-- Marginal monotonicity at step zero on `K₂` for the coordinate of `s(0, 1)`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_MargMonoRand (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
      (Lindeberg.coord s(0, 1)) (Lindeberg.coord s(0, 1)) t 0 A :=
  mmr_margMonoRand_f_at_zero
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) σ (Lindeberg.coord_mono _) t A

-- Marginal monotonicity holds trivially at the final step `n`, for any weight.
example {E : Type*} [Fintype E] [DecidableEq E] (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f g : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_MargMonoRand μ σ f g t n A :=
  mmr_margMonoRand_at_n μ σ f g t A

-- At step zero the randomized marginal is `f` evaluated at the joined code.
example {E : Type*} [Fintype E] [DecidableEq E] (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_margRand μ σ f f t 0 A
      = fun B => f (codeMap μ (σ : Fin n → E) (acp_join t A B)) :=
  mmr_margRand_f_at_zero_eq μ σ f t A

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MargMonoRand
