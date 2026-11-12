/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABBoundaryLimit
import Code.Sharpness.ABForwardCharacteristic
import Code.Sharpness.PercoSusceptibility
import Code.Sharpness.Item1Htc1
import Code.Percolation.PcUpperViaFK
import Code.Lattice.PlanarTopology

open Filter Finset Set SimpleGraph Topology

namespace StatMech
namespace Sharpness

open ConfigSpace Lattice
open StatMech.Percolation



theorem abbs_latticeCoupling_translate {d : Nat} (x u v : Site d) :
    abblLatticeCoupling d s(FK.fktc_translate x u, FK.fktc_translate x v) =
      abblLatticeCoupling d s(u, v) := by
  rw [abblLatticeCoupling_mk, abblLatticeCoupling_mk]
  exact if_congr (FK.fktc_translate_adj x u v) rfl rfl


theorem abbs_latticeCoupling_row_summable {d : Nat} (x : Site d) :
    Summable (fun y ↦ if (hypercubicLattice d).Adj x y
      then abblLatticeCoupling d s(x, y) else 0) := by
  apply summable_of_ne_finset_zero
    (s := (hypercubicLattice d).neighborFinset x)
  intro y hy
  rw [if_neg]
  intro hxy
  exact hy ((mem_neighborFinset (hypercubicLattice d) x y).mpr hxy)


theorem abbs_latticeCoupling_row_tsum {d : Nat} (x : Site d) :
    (∑' y, if (hypercubicLattice d).Adj x y
      then abblLatticeCoupling d s(x, y) else 0) = (2 * d : Real) := by
  rw [tsum_eq_sum (s := (hypercubicLattice d).neighborFinset x) (by
    intro y hy
    rw [if_neg]
    intro hxy
    exact hy ((mem_neighborFinset (hypercubicLattice d) x y).mpr hxy))]
  calc
    (∑ y ∈ (hypercubicLattice d).neighborFinset x,
        if (hypercubicLattice d).Adj x y
          then abblLatticeCoupling d s(x, y) else 0) =
        ∑ _y ∈ (hypercubicLattice d).neighborFinset x, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hxy := (mem_neighborFinset (hypercubicLattice d) x y).mp hy
      rw [if_pos hxy, abblLatticeCoupling_mk, if_pos hxy]
    _ = (2 * d : Real) := by
      simp [card_neighborFinset_eq_degree, degree_eq]


theorem abbs_latticeCoupling_window_row {d : Nat} (S : Finset (Site d))
    (x : S) :
    abcrIncidentCoupling
      (abigWindowGraph (hypercubicLattice d) S)
      (abigWindowCoupling (abblLatticeCoupling d) S) x ≤ (2 * d : Real) := by
  apply abigWindow_incidentCoupling_le
  apply abigUniformFiniteRowBound_of_tsum
  · exact abblLatticeCoupling_nonneg d
  · exact abbs_latticeCoupling_row_summable
  · intro y
    exact le_of_eq (abbs_latticeCoupling_row_tsum y)



theorem abbs_forward_characteristic {d : Nat} (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 < h) :
    ∀ epsilon, 0 < epsilon → ∃ delta > 0,
      ∀ t ∈ Icc (0 : Real) delta,
        abigMag (hypercubicLattice d) (abblLatticeCoupling d)
            (0 : Site d) (beta + t) h ≤
          abigMag (hypercubicLattice d) (abblLatticeCoupling d)
            (0 : Site d) beta
              (h + ((2 * d : Real) *
                (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
                  (0 : Site d) beta h + epsilon)) * t) := by
  apply abfc_abig_forward_characteristic_of_exhaustion
    (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
    (2 * d : Real) beta h (by positivity) hbeta hh
    (abblLatticeCoupling_nonneg d) abblLatticeCoupling_support
    (ablBoxFinset d) (zero_mem_ablBoxFinset d)
  · intro n x
    exact abbs_latticeCoupling_window_row (ablBoxFinset d n) x
  · intro b t hb ht n x
    exact le_of_eq (abigMag_eq_of_transitive
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      b t FK.fktc_translate
      (by intro y; funext i; simp [FK.fktc_translate_apply])
      FK.fktc_translate_adj abbs_latticeCoupling_translate
      (fun k ↦ abigGhostWindow (ablBoxFinset d k))
      (ablGhostWindow_cover d) (x : Site d))
  · exact ablGhostWindow_mono d
  · exact ablGhostWindow_cover d



theorem abbs_finite_integratingFactor_antitone {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hcrit : tildePc d ≤ bondParam beta) :
    AntitoneOn (fun b ↦ b * (1 - abbMag d n b h)) (Ici beta) := by
  let N : Real → Real := fun b ↦ abbMag d n b h
  let g : Real → Real := fun b ↦ b * (1 - N b)
  have hdiffN : ∀ b, DifferentiableAt Real N b := by
    intro b
    have hjoint := abbMag_differentiableAt_joint d n b h
    have hline : DifferentiableAt Real (fun x : Real ↦ (x, h)) b :=
      differentiableAt_id.prodMk (differentiableAt_const h)
    simpa [N, Function.comp_def, Function.uncurry] using hjoint.comp b hline
  have hdiffg : ∀ b, DifferentiableAt Real g b := by
    intro b
    exact differentiableAt_id.mul
      (differentiableAt_const (c := (1 : Real)).sub (hdiffN b))
  have hgderiv : ∀ b,
      deriv g b = 1 - N b - b * deriv N b := by
    intro b
    have hN := (hdiffN b).hasDerivAt
    have hg := (hasDerivAt_id b).mul
      ((hasDerivAt_const (x := b) (1 : Real)).sub hN)
    change deriv (fun x ↦ x * (1 - N x)) b =
      1 - N b - b * deriv N b
    convert hg.deriv using 1 <;> simp <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici beta)
  · intro b hb
    exact (hdiffg b).continuousAt.continuousWithinAt
  · intro b hb
    exact (hdiffg b).differentiableWithinAt
  · intro b hb
    have hbmem : b ∈ Ici beta := interior_subset hb
    have hb0 : 0 ≤ b := hbeta.trans hbmem
    have hpc : tildePc d ≤ bondParam b :=
      hcrit.trans (bondParam_mono hbmem)
    have hmf := abbMag_meanfield_of_tildePc_le hn b h hb0 hh hpc
    rw [hgderiv]
    change 1 - abbMag d n b h -
      b * deriv (fun x ↦ abbMag d n x h) b ≤ 0
    linarith




theorem abbs_infinite_integratingFactor_antitone {d : Nat}
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 < h)
    (hcrit : tildePc d ≤ bondParam beta) :
    AntitoneOn
      (fun b ↦ b * (1 - abigMag (hypercubicLattice d)
        (abblLatticeCoupling d) (0 : Site d) b h))
      (Ici beta) := by
  intro b₁ hb₁ b₂ hb₂ hb₁₂
  have hb₁0 : 0 ≤ b₁ := hbeta.trans hb₁
  have hb₂0 : 0 ≤ b₂ := hbeta.trans hb₂
  have hconv₁ := abbl_tendsto_abbMag_shifted d b₁ h hb₁0 hh
  have hconv₂ := abbl_tendsto_abbMag_shifted d b₂ h hb₂0 hh
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hconv₂))
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hconv₁))
  exact Filter.Eventually.of_forall fun n ↦
    abbs_finite_integratingFactor_antitone (Nat.succ_pos n)
      beta h hbeta hh.le hcrit hb₁ hb₂ hb₁₂




theorem abbs_infinite_field_meanfield {d : Nat} (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 < h)
    (hcrit : tildePc d ≤ bondParam beta) :
    1 - abigMag (hypercubicLattice d) (abblLatticeCoupling d)
        (0 : Site d) beta h ≤
      beta * (2 * d : Real) *
        (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
          (0 : Site d) beta h *
        deriv (fun t ↦ abigMag (hypercubicLattice d)
          (abblLatticeCoupling d) (0 : Site d) beta t) h) := by
  let M : Real → Real → Real := fun b t ↦
    abigMag (hypercubicLattice d) (abblLatticeCoupling d)
      (0 : Site d) b t
  let J0 : Real := (2 * d : Real)
  have hanti : AntitoneOn (fun b ↦ b * (1 - M b h)) (Ici beta) := by
    simpa [M] using
      abbs_infinite_integratingFactor_antitone beta h hbeta hh hcrit
  have hdiff : DifferentiableAt Real (fun t ↦ M beta t) h := by
    exact abigMag_differentiableAt_field_of_exhaustion
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      beta h hbeta hh (abblLatticeCoupling_nonneg d)
      abblLatticeCoupling_support (ablBoxFinset d)
      (zero_mem_ablBoxFinset d) (ablGhostWindow_mono d)
      (ablGhostWindow_cover d)
  have hmono : MonotoneOn (fun t ↦ M beta t) (Ici 0) := by
    exact abigMag_monotoneOn_field_of_exhaustion
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      beta hbeta (abblLatticeCoupling_nonneg d)
      abblLatticeCoupling_support (ablBoxFinset d)
      (zero_mem_ablBoxFinset d) (ablGhostWindow_mono d)
      (ablGhostWindow_cover d)
  have hdh : 0 ≤ deriv (fun t ↦ M beta t) h :=
    abigMag_deriv_field_nonneg_of_monotone
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      beta h hh hmono hdiff
  have hepsilon : ∀ epsilon : Real, 0 < epsilon →
      1 - M beta h ≤ beta *
        (J0 * (M beta h + epsilon)) *
          deriv (fun t ↦ M beta t) h := by
    intro epsilon hepsilon
    let c : Real := J0 * (M beta h + epsilon)
    obtain ⟨delta, hdelta, hforward⟩ :=
      abbs_forward_characteristic (d := d) beta h hbeta hh epsilon hepsilon
    have hevent : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        1 - M beta h ≤
          (beta + t) * ((M beta (h + c * t) - M beta h) / t) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hdelta)] with t ht htd
      have ht0 : 0 ≤ t := ht.le
      have hbt0 : 0 ≤ beta + t := add_nonneg hbeta ht0
      have htIci : beta + t ∈ Ici beta := mem_Ici.mpr (by linarith)
      have hanti_t := hanti (mem_Ici.mpr le_rfl) htIci (by linarith)
      have hfor : M (beta + t) h ≤ M beta (h + c * t) := by
        simpa [M, J0, c] using hforward t ⟨ht0, htd⟩
      have hsecant :
          t * (1 - M beta h) ≤
            (beta + t) * (M (beta + t) h - M beta h) := by
        nlinarith [hanti_t]
      have hchar :
          (beta + t) * (M (beta + t) h - M beta h) ≤
            (beta + t) * (M beta (h + c * t) - M beta h) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hfor _) hbt0
      calc
        1 - M beta h ≤
            ((beta + t) * (M beta (h + c * t) - M beta h)) / t :=
          (le_div_iff₀ ht).2 (by
            simpa [mul_comm] using hsecant.trans hchar)
        _ = (beta + t) * ((M beta (h + c * t) - M beta h) / t) := by ring
    have hinner : HasDerivAt (fun t : Real ↦ h + c * t) c 0 := by
      convert (hasDerivAt_const (x := (0 : Real)) h).add
        ((hasDerivAt_id (0 : Real)).const_mul c) using 1 <;> ring
    have hcomp : HasDerivAt (fun t ↦ M beta (h + c * t))
        (c * deriv (fun y ↦ M beta y) h) 0 := by
      have hder := hdiff.hasDerivAt.comp_of_eq 0 hinner (by ring)
      simpa [Function.comp_def, mul_comm] using hder
    have hslope : Tendsto
        (fun t ↦ (M beta (h + c * t) - M beta h) / t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (c * deriv (fun y ↦ M beta y) h)) := by
      simpa [div_eq_inv_mul, mul_comm] using hcomp.tendsto_slope_zero_right
    have hcoef : Tendsto (fun t : Real ↦ beta + t)
        (nhdsWithin 0 (Ioi 0)) (nhds beta) := by
      have hid : Tendsto (fun t : Real ↦ t)
          (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using tendsto_const_nhds.add hid
    have hlim := hcoef.mul hslope
    have hbound := le_of_tendsto_of_tendsto
      tendsto_const_nhds hlim hevent
    simpa [c, J0, mul_assoc] using hbound
  let dh := deriv (fun t ↦ M beta t) h
  by_cases hcoef : 0 < beta * J0 * dh
  · apply le_of_forall_pos_le_add
    intro delta hdelta
    have he := hepsilon (delta / (beta * J0 * dh))
      (div_pos hdelta hcoef)
    have hne : beta * J0 * dh ≠ 0 := hcoef.ne'
    have hcancel : (beta * J0 * dh) *
        (delta / (beta * J0 * dh)) = delta := by
      exact mul_div_cancel₀ delta hne
    calc
      1 - M beta h ≤ beta * (J0 *
          (M beta h + delta / (beta * J0 * dh))) * dh := he
      _ = beta * J0 * (M beta h * dh) +
          (beta * J0 * dh) * (delta / (beta * J0 * dh)) := by ring
      _ = beta * J0 * (M beta h * dh) + delta := by rw [hcancel]
  · have he := hepsilon 1 zero_lt_one
    have hnonpos : beta * J0 * dh ≤ 0 := le_of_not_gt hcoef
    have hzero : beta * J0 * dh = 0 :=
      le_antisymm hnonpos (mul_nonneg (mul_nonneg hbeta (by positivity)) hdh)
    calc
      1 - M beta h ≤ beta * (J0 * (M beta h + 1)) * dh := he
      _ = beta * J0 * (M beta h * dh) := by
        rw [show beta * (J0 * (M beta h + 1)) * dh =
          beta * J0 * (M beta h * dh) + beta * J0 * dh by ring, hzero,
          add_zero]



theorem abbs_field_sq_lower_bound_pos (K : Real) (hK : 0 < K)
    (m : Real → Real)
    (hdiff : ∀ h ∈ Ioi (0 : Real), DifferentiableAt Real m h)
    (hmono : ∀ h ∈ Ioi (0 : Real), 0 ≤ deriv m h)
    (heq : ∀ h ∈ Ioi (0 : Real),
      1 - m h ≤ K * (m h * deriv m h))
    (h₀ : Real) (hh₀ : 0 < h₀) (hle : m h₀ ≤ 1 / 2) :
    h₀ / K ≤ (m h₀) ^ 2 := by
  have hmMono : MonotoneOn m (Ioi (0 : Real)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro h hh
      exact (hdiff h hh).continuousAt.continuousWithinAt
    · intro h hh
      exact (hdiff h (interior_subset hh)).differentiableWithinAt
    · intro h hh
      exact hmono h (interior_subset hh)
  have hbound : ∀ h ∈ Ioc (0 : Real) h₀, m h ≤ 1 / 2 := by
    intro h hh
    exact (hmMono hh.1 (mem_Ioi.mpr hh₀) hh.2).trans hle
  let g : Real → Real := fun h ↦ (m h) ^ 2 - h / K
  have hgderiv : ∀ h ∈ Ioi (0 : Real),
      deriv g h = 2 * m h * deriv m h - 1 / K := by
    intro h hh
    have hpow := ((hdiff h hh).hasDerivAt).pow 2
    have hlin : HasDerivAt (fun t : Real ↦ t / K) (1 / K) h := by
      simpa using (hasDerivAt_id h).div_const K
    have hg := hpow.sub hlin
    convert hg.deriv using 1 <;> simp [g, pow_one] <;> ring
  have hcut : ∀ epsilon ∈ Ioc (0 : Real) h₀,
      -epsilon / K ≤ g h₀ := by
    intro epsilon hepsilon
    have hgMono : MonotoneOn g (Icc epsilon h₀) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc epsilon h₀)
      · intro h hh
        exact ((hdiff h (by
          have : epsilon ≤ h := hh.1
          exact mem_Ioi.mpr (hepsilon.1.trans_le this))).continuousAt.pow 2).sub
            (continuousAt_id.div_const K) |>.continuousWithinAt
      · intro h hh
        exact ((hdiff h (by
          have : epsilon ≤ h := interior_subset hh |>.1
          exact mem_Ioi.mpr (hepsilon.1.trans_le this))).pow 2).sub
            (differentiableAt_id.div_const K) |>.differentiableWithinAt
      · intro h hh
        rw [interior_Icc, Set.mem_Ioo] at hh
        rw [hgderiv h (mem_Ioi.mpr (hepsilon.1.trans hh.1))]
        have hab := heq h (mem_Ioi.mpr (hepsilon.1.trans hh.1))
        have hmle : m h ≤ 1 / 2 :=
          hbound h ⟨hepsilon.1.trans hh.1, hh.2.le⟩
        have hhalf : (1 : Real) / 2 ≤ K * (m h * deriv m h) := by
          linarith
        rw [sub_nonneg, div_le_iff₀ hK]
        nlinarith [hhalf]
    have hgh := hgMono (left_mem_Icc.mpr hepsilon.2)
      (right_mem_Icc.mpr hepsilon.2) hepsilon.2
    have hsq : 0 ≤ (m epsilon) ^ 2 := sq_nonneg _
    change -epsilon / K ≤ (m h₀) ^ 2 - h₀ / K
    change (m epsilon) ^ 2 - epsilon / K ≤
      (m h₀) ^ 2 - h₀ / K at hgh
    exact (by
      calc
        -epsilon / K ≤ (m epsilon) ^ 2 - epsilon / K := by
          simpa only [zero_sub, neg_div] using
            sub_le_sub_right hsq (epsilon / K)
        _ ≤ (m h₀) ^ 2 - h₀ / K := hgh)
  have hevent : ∀ᶠ epsilon in nhdsWithin 0 (Ioi 0),
      -epsilon / K ≤ g h₀ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hh₀)] with epsilon he hle₀
    exact hcut epsilon ⟨he, hle₀⟩
  have htend : Tendsto (fun epsilon : Real ↦ -epsilon / K)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hid : Tendsto (fun epsilon : Real ↦ epsilon)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using hid.neg.div_const K
  have hg0 : 0 ≤ g h₀ := le_of_tendsto htend hevent
  dsimp [g] at hg0
  linarith



theorem abbs_field_sqrt_lower_bound_pos (K : Real) (hK : 0 < K)
    (m : Real → Real)
    (hdiff : ∀ h ∈ Ioi (0 : Real), DifferentiableAt Real m h)
    (hmono : ∀ h ∈ Ioi (0 : Real), 0 ≤ deriv m h)
    (hmnn : ∀ h, 0 ≤ m h)
    (heq : ∀ h ∈ Ioi (0 : Real),
      1 - m h ≤ K * (m h * deriv m h)) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (K / 4),
      c * Real.sqrt h ≤ m h := by
  refine ⟨1 / Real.sqrt K, by positivity, ?_⟩
  intro h hh
  have hroot : Real.sqrt (h / K) ≤ m h := by
    by_cases hcase : m h ≤ 1 / 2
    · have hsq := abbs_field_sq_lower_bound_pos K hK m hdiff hmono
        heq h hh.1 hcase
      calc
        Real.sqrt (h / K) ≤ Real.sqrt ((m h) ^ 2) :=
          Real.sqrt_le_sqrt hsq
        _ = m h := Real.sqrt_sq (hmnn h)
    · have hmhalf : 1 / 2 < m h := lt_of_not_ge hcase
      have hq : h / K ≤ 1 / 4 := by
        rw [div_le_iff₀ hK]
        linarith [hh.2]
      calc
        Real.sqrt (h / K) ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hq
        _ = 1 / 2 := by norm_num
        _ ≤ m h := hmhalf.le
  rw [Real.sqrt_div hh.1.le] at hroot
  simpa [div_eq_mul_inv, mul_comm] using hroot





theorem abbs_perco_meanfield_sqrt {d : Nat} (hd : 0 < d)
    (beta : Real) (hbeta : 0 < beta)
    (hcrit : tildePc d ≤ bondParam beta) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (beta * (2 * d : Real) / 4),
      c * Real.sqrt h ≤
        abigMag (hypercubicLattice d) (abblLatticeCoupling d)
          (0 : Site d) beta h := by
  let m : Real → Real := fun h ↦
    abigMag (hypercubicLattice d) (abblLatticeCoupling d)
      (0 : Site d) beta h
  let K : Real := beta * (2 * d : Real)
  have hK : 0 < K := mul_pos hbeta (by positivity)
  apply abbs_field_sqrt_lower_bound_pos K hK m
  · intro h hh
    exact abigMag_differentiableAt_field_of_exhaustion
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      beta h hbeta.le hh (abblLatticeCoupling_nonneg d)
      abblLatticeCoupling_support (ablBoxFinset d)
      (zero_mem_ablBoxFinset d) (ablGhostWindow_mono d)
      (ablGhostWindow_cover d)
  · intro h hh
    have hmono : MonotoneOn m (Ici 0) := by
      exact abigMag_monotoneOn_field_of_exhaustion
        (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
        beta hbeta.le (abblLatticeCoupling_nonneg d)
        abblLatticeCoupling_support (ablBoxFinset d)
        (zero_mem_ablBoxFinset d) (ablGhostWindow_mono d)
        (ablGhostWindow_cover d)
    have hdiff : DifferentiableAt Real m h := by
      exact abigMag_differentiableAt_field_of_exhaustion
        (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
        beta h hbeta.le hh (abblLatticeCoupling_nonneg d)
        abblLatticeCoupling_support (ablBoxFinset d)
        (zero_mem_ablBoxFinset d) (ablGhostWindow_mono d)
        (ablGhostWindow_cover d)
    exact abigMag_deriv_field_nonneg_of_monotone
      (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
      beta h hh hmono hdiff
  · intro h
    exact abigMag_nonneg (hypercubicLattice d) (abblLatticeCoupling d)
      (0 : Site d) beta h
  · intro h hh
    simpa [K, m, mul_assoc] using
      abbs_infinite_field_meanfield beta h hbeta.le hh hcrit



theorem abbs_perco_meanfield_sqrt_critical {d : Nat} (hd : 0 < d)
    (htc1 : (tildePc d : Real) < 1) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : Real)
        (betaTildeC d 1 * (2 * d : Real) / 4),
      c * Real.sqrt h ≤
        abigMag (hypercubicLattice d) (abblLatticeCoupling d)
          (0 : Site d) (betaTildeC d 1) h := by
  have hbeta : 0 < betaTildeC d 1 :=
    betaTildeC_pos one_pos hd htc1
  have hparam : bondParam (betaTildeC d 1) = tildePc d := by
    apply NNReal.coe_injective
    rw [abb_bondParam_coe_eq_pBeta _ hbeta.le,
      pBeta_betaTildeC one_pos htc1]
  exact abbs_perco_meanfield_sqrt hd (betaTildeC d 1) hbeta hparam.ge



theorem abbs_perco_meanfield_sqrt_unconditional {d : Nat} (hd : 2 ≤ d) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : Real)
        (betaTildeC d 1 * (2 * d : Real) / 4),
      c * Real.sqrt h ≤
        abigMag (hypercubicLattice d) (abblLatticeCoupling d)
          (0 : Site d) (betaTildeC d 1) h := by
  apply abbs_perco_meanfield_sqrt_critical (by omega)
  exact sh1_tildePc_lt_one_of_pc_lt_one (by omega)
    (pc_nontrivial_of_two_le hd).2

end Sharpness
end StatMech
