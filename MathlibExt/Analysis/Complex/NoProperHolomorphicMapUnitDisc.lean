/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_41.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement and its informal description.
Authors: L. Pu et al. (MA-ProofBench)
Licensed under the MIT License.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# No proper holomorphic map from the unit disc to the complex plane

Every holomorphic map on the open unit disc has a compact set with noncompact preimage.
We apply the maximum modulus principle to `z ↦ z ^ n / f z` on annuli near the unit circle.
-/

open Set Metric

namespace MathlibExt.Analysis.Complex.NoProperHolomorphicMapUnitDiscWanted

/-- A compact preimage of a closed ball stays inside a strictly smaller open disc. -/
private theorem exists_radius {f : ℂ → ℂ} {M : ℝ}
    (h : IsCompact ((fun z : ball (0 : ℂ) 1 => f z) ⁻¹' closedBall 0 M)) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ < 1 → M < ‖f z‖ := by
  have hc := h.image continuous_subtype_val
  obtain ⟨r, hr, hsub⟩ := exists_pos_lt_subset_ball zero_lt_one hc.isClosed
    (fun _ ⟨z, _, hz⟩ => hz ▸ z.property)
  refine ⟨r, hr, fun z hrz hz => ?_⟩
  by_contra! hM
  have hz' : z ∈ ball (0 : ℂ) 1 := by simpa using hz
  have hmem := hsub (show z ∈ _ from
    ⟨⟨z, hz'⟩, (show f z ∈ closedBall 0 M by simpa using hM), rfl⟩)
  exact hrz.not_gt (by simpa using hmem)

/-- **No proper holomorphic map from the unit disc to the complex plane.** Let
$\Delta := \{z\in\mathbb{C}\mid |z|<1\}$ be the unit disc in the complex plane. There is no proper
holomorphic map $f:\Delta\to\mathbb{C}$, where proper means that the preimage under $f$ of every
compact subset of $\mathbb{C}$ is a compact subset of $\Delta$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_41.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem not_exists_differentiableOn_ball_isCompact_preimage :
    ¬ ∃ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
          (∀ K : Set ℂ, IsCompact K →
            IsCompact ((fun z : Metric.ball (0 : ℂ) 1 => f z) ⁻¹' K)) := by
  rintro ⟨f, hf, hproper⟩
  have escape (M : ℝ) := exists_radius (hproper _ (isCompact_closedBall 0 M))
  obtain ⟨r, hr, hinner⟩ := escape 1
  obtain ⟨s, hrs, hs⟩ := exists_between hr.2
  have hsNorm : ‖(s : ℂ)‖ = s := Complex.norm_of_nonneg (hr.1.trans hrs).le
  -- At s, choose n large enough that the quotient exceeds the inner boundary bound r ^ n.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖f (s : ℂ)‖ ((one_lt_div hr.1).2 hrs)
  have hrn : 0 < r ^ n := pow_pos hr.1 n
  -- Choose an outer circle where the denominator dominates even the factor r⁻ⁿ.
  obtain ⟨t, ht, houter⟩ := escape (r ^ n)⁻¹
  obtain ⟨R, hR, hR1⟩ := exists_between (max_lt hs ht.2)
  have hsR : s < R := (le_max_left s t).trans_lt hR
  let U := (fun z : ℂ => ‖z‖) ⁻¹' Ioo r R
  have hcl : closure U ⊆ (fun z : ℂ => ‖z‖) ⁻¹' Icc r R :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_norm)
  have hdisc : closure U ⊆ ball (0 : ℂ) 1 := fun z hz => by
    simpa using (hcl hz).2.trans_lt hR1
  have hlarge {z : ℂ} (hz : z ∈ closure U) : 1 < ‖f z‖ :=
    hinner z (hcl hz).1 ((hcl hz).2.trans_lt hR1)
  have hd : DifferentiableOn ℂ (fun z => z ^ n / f z) (closure U) :=
    (differentiableOn_id.pow n).div (hf.mono hdisc) fun z hz =>
      norm_pos_iff.mp (zero_lt_one.trans (hlarge hz))
  have hboundary (z : ℂ) (hz : z ∈ frontier U) : ‖z ^ n / f z‖ ≤ r ^ n := by
    have hzcl := frontier_subset_closure hz
    have hpos := zero_lt_one.trans (hlarge hzcl)
    rw [norm_div, norm_pow, div_le_iff₀ hpos]
    have hcircle : ‖z‖ ∈ frontier (Ioo r R) :=
      continuous_norm.frontier_preimage_subset _ hz
    rw [frontier_Ioo (hrs.trans hsR), mem_insert_iff, mem_singleton_iff] at hcircle
    rcases hcircle with heq | heq
    · rw [heq]
      exact le_mul_of_one_le_right hrn.le (hlarge hzcl).le
    · have hM := houter z ((le_max_right s t).trans (hR.le.trans heq.ge)) (heq ▸ hR1)
      exact (pow_le_one₀ (norm_nonneg z) (heq.le.trans hR1.le)).trans
        ((inv_le_iff_one_le_mul₀' hrn).mp hM.le)
  have hmem : (s : ℂ) ∈ U := by
    change r < ‖(s : ℂ)‖ ∧ ‖(s : ℂ)‖ < R
    rw [hsNorm]
    exact ⟨hrs, hsR⟩
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball.subset (subset_closure.trans hdisc)) hd.diffContOnCl hboundary
    (subset_closure hmem)
  rw [norm_div, norm_pow, hsNorm, div_le_iff₀ (zero_lt_one.trans (hlarge (subset_closure hmem)))]
    at hmax
  rw [div_pow, lt_div_iff₀ hrn, mul_comm] at hn
  exact hn.not_ge hmax

end MathlibExt.Analysis.Complex.NoProperHolomorphicMapUnitDiscWanted
