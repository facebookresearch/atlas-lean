/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CrossMonotone

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CrossMonotone`

* `cmn_tailCondLaw` (unconditional) for the random-cluster mass on `K₂` at `p = 1/2`, `q = 2`
  and the monotone observable "edge `s(0, 1)` is open", for an arbitrary order;
* `cmn_Cross41` for an arbitrary monotonic measure, monotone bounded observable and step.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CrossMonotone

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.AdaptDisintegration

-- The tail conditional law on `K₂` for the coordinate of `s(0, 1)`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    acp_TailCondLaw (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
      (Lindeberg.coord s(0, 1)) :=
  cmn_tailCondLaw
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    σ (Lindeberg.coord_mono _) (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)

-- The one-step cross inequality `cvf_Cross41` for any monotonic measure.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    cvf_Cross41 μ σ f t htn A :=
  cmn_Cross41 hpos hμ1 hmono σ hf hfC t htn A

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.CrossMonotone
