/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.OptionalStopping

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.OptionalStopping`

* `osp_tailSelFixed_mp` at the concrete values `n = 2`, `t = 0`, `s = 1`, `k = 0`;
* `osp_tailSelFixed_law` for the random-cluster mass on `K₂` at `p = 1/2`, `q = 2` and the
  bounded observable `g = 1`;
* `osp_tailSelMP_of_const_switch` applied conditionally on a constant stopping value;
* the refutation `osp_naive_per_partition_glue_false` restated.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.OptionalStopping

open MeasureTheory
open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.GrandCoupling _root_.StatMech.OSSS.AdaptMConditional

-- The fixed tail selection is measure preserving at concrete parameters.
example (A : {i : Fin 2 // (i : ℕ) < 0} → ℝ) :
    MeasurePreserving (osp_tailSelFixed 0 1 0 A) ((ubfTail 2 0).prod (Vcube 2)) (Vcube 2) :=
  osp_tailSelFixed_mp 0 1 0 (by norm_num) A

-- The law of the fixed tail selection, for the FK mass on `K₂` and the constant observable.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (A : {i : Fin n // (i : ℕ) < 0} → ℝ) :
    (∫ B, (∫ V, (fun _ => (1 : ℝ)) (Coding.codeMap (MonotonicFK.fkMass ⊤ (1 / 2) 2)
        (σ : Fin n → Sym2 (Fin 2)) (adaptWt (acp_join 0 A B) V 0 1)) ∂(Vcube n))
        ∂(ubfTail n 0))
      = Lindeberg.mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (fun _ => (1 : ℝ)) :=
  osp_tailSelFixed_law _
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num)) σ (fun _ => (1 : ℝ)) (Cg := 1) (fun _ => by norm_num) 0 1 0 (by norm_num) A

-- The stopped tail selection is measure preserving given a constant switch.
example {E : Type*} [Fintype E] [DecidableEq E] (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (A : {i : Fin n // (i : ℕ) < 0} → ℝ) (k₀ : ℕ)
    (hconst : ∀ B, stopVal μ σ f (acp_join 0 A B) = k₀) :
    atl_TailSelMP μ σ f 0 1 A :=
  osp_tailSelMP_of_const_switch μ σ 0 1 (by norm_num) A k₀ hconst

-- Gluing two measure-preserving maps along a partition is not measure preserving in general.
example :
    ¬ (∀ {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω) (ν : Measure β)
        (h₀ h₁ : Ω → β) (p : Ω → Prop) [DecidablePred p]
        (_h0 : MeasurePreserving h₀ μ ν) (_h1 : MeasurePreserving h₁ μ ν)
        (h : Ω → β) (_hpiece : ∀ x, h x = if p x then h₀ x else h₁ x),
        MeasurePreserving h μ ν) :=
  osp_naive_per_partition_glue_false

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.OptionalStopping
