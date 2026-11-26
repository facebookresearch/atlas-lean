/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPSplice

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPSplice`

On one edge (`E = Fin 1`, `n = 1`, identity order, uniform mass, observable `0`), at `t = 0`:
* `sp1_tailSelMP` gives the measure-preservation `atl_TailSelMP` at `s = t + 1`;
* `sp1_restrictedSum_at_s_eq_t_succ` gives the restricted-sum identity at `s = t + 1`;
* `sp1_restrictedSum_of_tailSelMP` turns the first into the second.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPSplice

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration

-- Tail selection is measure preserving after splicing, on a one-edge instance.
example (A : {i : Fin 1 // (i : ℕ) < 0} → ℝ) :
    atl_TailSelMP (fun _ : ConfigSpace (Fin 1) => (1 / 2 : ℝ)) (Equiv.refl (Fin 1)) 0 0 1 A :=
  sp1_tailSelMP _ _ _ 0 (by norm_num) A

-- The restricted-sum identity at `s = t + 1`, on the same instance.
example (A : {i : Fin 1 // (i : ℕ) < 0} → ℝ) :
    tsm_TailSelMP_restrictedSum (fun _ : ConfigSpace (Fin 1) => (1 / 2 : ℝ))
      (Equiv.refl (Fin 1)) 0 0 1 A :=
  sp1_restrictedSum_at_s_eq_t_succ _ _ _ 0 (by norm_num) A

-- Measure preservation implies the restricted-sum identity, for any data.
example {n : ℕ} (μ : ConfigSpace (Fin 2) → ℝ) (σ : Fin n ≃ Fin 2) (f : ConfigSpace (Fin 2) → ℝ)
    (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (h : atl_TailSelMP μ σ f t s A) :
    tsm_TailSelMP_restrictedSum μ σ f t s A :=
  sp1_restrictedSum_of_tailSelMP μ σ f t s A h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailSelMPSplice
