/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABBoundaryLimit

open Filter Set Topology

namespace StatMech
namespace Sharpness




theorem abml_meanfield_limit
    (Mn : Nat → Real → Real) (M : Real → Real) (beta : Real)
    (hbeta : 0 < beta)
    (hfinite : ∀ n b, beta ≤ b →
      1 - Mn n b ≤ b * deriv (Mn n) b)
    (hdiffFinite : ∀ n b, DifferentiableAt Real (Mn n) b)
    (hconv : ∀ b, beta ≤ b →
      Tendsto (fun n ↦ Mn n b) atTop (nhds (M b)))
    (hdiff : DifferentiableAt Real M beta) :
    1 - M beta ≤ beta * deriv M beta := by
  have hendpoint : ∀ t, 0 < t →
      (beta + t) * (1 - M (beta + t)) ≤
        beta * (1 - M beta) := by
    intro t ht
    have hanti : ∀ n,
        AntitoneOn (fun b ↦ b * (1 - Mn n b))
          (Icc beta (beta + t)) := by
      intro n
      apply antitoneOn_of_deriv_nonpos (convex_Icc beta (beta + t))
      · intro b hb
        exact ((differentiableAt_id.mul
          ((differentiableAt_const (c := (1 : Real))).sub
            (hdiffFinite n b))).continuousAt).continuousWithinAt
      · intro b hb
        exact (differentiableAt_id.mul
          ((differentiableAt_const (c := (1 : Real))).sub
            (hdiffFinite n b))).differentiableWithinAt
      · intro b hb
        rw [interior_Icc, mem_Ioo] at hb
        have hder := (hasDerivAt_id b).mul
          ((hasDerivAt_const (x := b) (c := (1 : Real))).sub
            (hdiffFinite n b).hasDerivAt)
        change deriv (id * ((fun _ : Real ↦ (1 : Real)) - Mn n)) b ≤ 0
        rw [hder.deriv]
        dsimp
        have hmf := hfinite n b (by linarith [hb.1])
        nlinarith
    have hfin : ∀ n,
        (beta + t) * (1 - Mn n (beta + t)) ≤
          beta * (1 - Mn n beta) := by
      intro n
      exact hanti n (left_mem_Icc.mpr (by linarith))
        (right_mem_Icc.mpr (by linarith)) (by linarith)
    have hleft : Tendsto
        (fun n ↦ (beta + t) * (1 - Mn n (beta + t))) atTop
        (nhds ((beta + t) * (1 - M (beta + t)))) := by
      exact tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (hconv (beta + t) (by linarith)))
    have hright : Tendsto
        (fun n ↦ beta * (1 - Mn n beta)) atTop
        (nhds (beta * (1 - M beta))) := by
      exact tendsto_const_nhds.mul
        (tendsto_const_nhds.sub (hconv beta le_rfl))
    exact le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall hfin)
  have hslope : ∀ t, 0 < t →
      1 - M (beta + t) ≤
        beta * ((M (beta + t) - M beta) / t) := by
    intro t ht
    have he := hendpoint t ht
    rw [← mul_div_assoc]
    apply (le_div_iff₀ ht).2
    nlinarith
  have hevent : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      1 - M (beta + t) ≤
        beta * ((M (beta + t) - M beta) / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hslope t ht
  have hleft : Tendsto (fun t ↦ 1 - M (beta + t))
      (nhdsWithin 0 (Ioi 0)) (nhds (1 - M beta)) := by
    have hadd : Tendsto (fun t : Real ↦ beta + t)
        (nhdsWithin 0 (Ioi 0)) (nhds beta) := by
      have hbase : Tendsto (fun t : Real ↦ beta + t)
          (nhds 0) (nhds beta) :=
        by
          simpa using (tendsto_const_nhds (x := beta)).add
            (tendsto_id : Tendsto (fun t : Real ↦ t) (nhds 0) (nhds 0))
      exact hbase.mono_left inf_le_left
    exact tendsto_const_nhds.sub (hdiff.continuousAt.tendsto.comp hadd)
  have hright : Tendsto
      (fun t ↦ beta * ((M (beta + t) - M beta) / t))
      (nhdsWithin 0 (Ioi 0)) (nhds (beta * deriv M beta)) := by
    apply tendsto_const_nhds.mul
    simpa [div_eq_inv_mul, mul_comm] using
      hdiff.hasDerivAt.tendsto_slope_zero_right
  exact le_of_tendsto_of_tendsto hleft hright hevent

end Sharpness
end StatMech
