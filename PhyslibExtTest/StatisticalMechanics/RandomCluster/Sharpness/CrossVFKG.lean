/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CrossVFKG

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CrossVFKG`

* `cvf_Cross41_const_switch` on `K₂` at `p = 1/2`, `q = 2` for the coordinate observable,
  conditional on the stopping time being constant on the tail;
* `cvf_tailCondLaw_of_cross41`: the cross inequality at every step gives the tail law;
* `cvf_Cross41_of_margMono` from its two marginal-monotonicity hypotheses.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CrossVFKG

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.AdaptDisintegration

-- The cross inequality on `K₂` when the stopping time does not depend on the tail.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m₀ : ℕ)
    (hconst : ∀ B, stopVal (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
      (Lindeberg.coord s(0, 1)) (acp_join t A B) = m₀) :
    cvf_Cross41 (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
      (Lindeberg.coord s(0, 1)) t htn A :=
  cvf_Cross41_const_switch
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    σ (Lindeberg.coord_mono _) (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)
    t htn A m₀ hconst

-- The cross inequality at every step yields the tail conditional law.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1)
    (h : ∀ (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
      cvf_Cross41 μ σ f t htn A) :
    acp_TailCondLaw μ σ f :=
  cvf_tailCondLaw_of_cross41 hpos hμ1 σ hfC h

-- The cross inequality from marginal monotonicity of `f` and of the next coordinate.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (h1 : atl_MargMonoRand μ σ f f t (t + 1) A)
    (h2 : atl_MargMonoRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A) :
    cvf_Cross41 μ σ f t htn A :=
  cvf_Cross41_of_margMono μ hpos hμ1 σ hfC t htn A h1 h2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CrossVFKG
