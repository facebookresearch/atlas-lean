/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWSpinFourier
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TorusSpinSectors

/-!

# From the spin Kac-Ward identities to Onsager's formula

If each signed sector sum squares to its sector determinant, the even-subgraph sums of the torus
have the growth rate of Onsager's integral.

## i. Overview

The spin Kac-Ward identities state that on every torus `spin_{ab}(tanh β)² = det_{ab}(β)` for the
four spin structures. Off the critical point all four sector determinants are positive and
`log det_{ab} / (2L²)` converges to `ons_freeEnergyIntegral β - 2 log cosh β`. Since
`2 X_L ≤ ∑ |spin_{ab}| ≤ 4 X_L`, the same limit holds for `log X_L / L²`, which is
`ons_KacWardResidue β`. At `β = 0` the identities hold trivially.

## ii. Key results

- `ons_spinKacWardIdentities` : the four spin Kac-Ward identities on all tori
- `ons_spinKacWardMatrixIdentities` : the same in terms of twisted Kac-Ward determinants
- `ons_KacWardResidue_of_spinKacWard` : the identities imply convergence of `log X_L / L²`

## iii. Table of contents

- A. The spin Kac-Ward identities
- B. Growth of the even-subgraph sums

## iv. References

- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337
- N. P. Dolbilin, Yu. M. Zinov'ev, A. S. Mishchenko, M. A. Shtan'ko and M. I. Shtogrin, *Homological
  properties of two-dimensional coverings of lattices on surfaces*, Funct. Anal. Appl. 30 (1996)
  163-173
- D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023

-/

@[expose] public section

namespace StatMech.Onsager

open StatMech.Ising

/-! ## A. The spin Kac-Ward identities -/

/-- The spin Kac-Ward identities at inverse temperature `β`: on every `L × L` torus with `L > 2`,
each signed sector sum at `tanh β` squares to the corresponding sector determinant. -/
def ons_spinKacWardIdentities (beta : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ons_spin11 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 0 0 ∧
    ons_spin01 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 1 0 ∧
    ons_spin10 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 0 1 ∧
    ons_spin00 L (Real.tanh beta) ^ 2 = ons_spinDet L beta 1 1

/-- The spin Kac-Ward identities written with the twisted Kac-Ward determinants `det (1 - Λ_{ab})`
at `x = tanh β`. -/
def ons_spinKacWardMatrixIdentities (beta : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : 2 < L),
    letI : Fact (2 < L) := ⟨hL⟩
    ((ons_spin11 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 0) (ons_spinPhase L 0)).det) ∧
    ((ons_spin01 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 1) (ons_spinPhase L 0)).det) ∧
    ((ons_spin10 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 0) (ons_spinPhase L 1)).det) ∧
    ((ons_spin00 L (Real.tanh beta) : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
        (ons_spinPhase L 1) (ons_spinPhase L 1)).det)

lemma ons_spinKacWardIdentities_of_matrix (beta : ℝ)
    (h : ons_spinKacWardMatrixIdentities beta) :
    ons_spinKacWardIdentities beta := by
  intro L hL
  let : Fact (2 < L) := ⟨hL⟩
  have : NeZero L := ⟨by omega⟩
  have : Fact (1 < L) := ⟨by omega⟩
  rcases h L hL with ⟨h11, h01, h10, h00⟩
  rw [ons_KWmatPhase_det_eq_spinDet] at h11 h01 h10 h00
  constructor
  · exact_mod_cast h11
  constructor
  · exact_mod_cast h01
  constructor
  · exact_mod_cast h10
  · exact_mod_cast h00

lemma ons_spinKacWardMatrixIdentities_zero :
    ons_spinKacWardMatrixIdentities 0 := by
  intro L hL
  let : Fact (2 < L) := ⟨hL⟩
  have hmat : ons_KWmatPhase L (0 : ℂ) ons_turnRoot
      (ons_spinPhase L 0) (ons_spinPhase L 0) = 0 := by
    ext p q
    simp [ons_KWmatPhase, ons_KWmat]
  have hmat10 : ons_KWmatPhase L (0 : ℂ) ons_turnRoot
      (ons_spinPhase L 1) (ons_spinPhase L 0) = 0 := by
    ext p q
    simp [ons_KWmatPhase, ons_KWmat]
  have hmat01 : ons_KWmatPhase L (0 : ℂ) ons_turnRoot
      (ons_spinPhase L 0) (ons_spinPhase L 1) = 0 := by
    ext p q
    simp [ons_KWmatPhase, ons_KWmat]
  have hmat11 : ons_KWmatPhase L (0 : ℂ) ons_turnRoot
      (ons_spinPhase L 1) (ons_spinPhase L 1) = 0 := by
    ext p q
    simp [ons_KWmatPhase, ons_KWmat]
  simp only [Real.tanh_zero, Complex.ofReal_zero]
  rw [hmat, hmat10, hmat01, hmat11]
  simp [ons_spin00, ons_spin10, ons_spin01, ons_spin11,
    ons_sector00, ons_sector10, ons_sector01, ons_sector11,
    ons_sectorWeight_zero]

/-! ## B. Growth of the even-subgraph sums -/

private lemma log_abs_of_sq_eq {p d : ℝ} (h : p ^ 2 = d) :
    Real.log |p| = Real.log d / 2 := by
  calc
    Real.log |p| = Real.log (|p| ^ 2) / 2 := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log d / 2 := by rw [sq_abs, h]

private lemma spin_abs_pos_of_sq_eq {p d : ℝ} (hd : 0 < d) (h : p ^ 2 = d) :
    0 < |p| := by
  apply abs_pos.mpr
  intro hp
  have hd0 : d = 0 := by rw [← h, hp]; norm_num
  exact hd.ne' hd0

lemma ons_KacWardResidue_of_spinKacWard (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcrit : beta ≠ ons_betaC) (hspin : ons_spinKacWardIdentities beta) :
    ons_KacWardResidue beta := by
  let q : ℝ := ons_freeEnergyIntegral beta - 2 * Real.log (Real.cosh beta)
  let s11 : ℕ → ℝ := fun L => if hL : 2 < L then
      letI : Fact (2 < L) := ⟨hL⟩
      Real.log |ons_spin11 L (Real.tanh beta)| / (L : ℝ) ^ 2
    else 0
  let s01 : ℕ → ℝ := fun L => if hL : 2 < L then
      letI : Fact (2 < L) := ⟨hL⟩
      Real.log |ons_spin01 L (Real.tanh beta)| / (L : ℝ) ^ 2
    else 0
  let s10 : ℕ → ℝ := fun L => if hL : 2 < L then
      letI : Fact (2 < L) := ⟨hL⟩
      Real.log |ons_spin10 L (Real.tanh beta)| / (L : ℝ) ^ 2
    else 0
  let s00 : ℕ → ℝ := fun L => if hL : 2 < L then
      letI : Fact (2 < L) := ⟨hL⟩
      Real.log |ons_spin00 L (Real.tanh beta)| / (L : ℝ) ^ 2
    else 0
  have hs11 : Filter.Tendsto s11 Filter.atTop (nhds q) := by
    have ht := ons_spinDet_density_tendsto beta hbeta hcrit (0 : Fin 2) (0 : Fin 2)
    refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
    have h2 : 2 < L := by omega
    let : Fact (2 < L) := ⟨h2⟩
    rw [show s11 L = Real.log |ons_spin11 L (Real.tanh beta)| / (L : ℝ) ^ 2 by
      simp [s11, h2]]
    rw [log_abs_of_sq_eq (hspin L h2).1]
    ring
  have hs01 : Filter.Tendsto s01 Filter.atTop (nhds q) := by
    have ht := ons_spinDet_density_tendsto beta hbeta hcrit (1 : Fin 2) (0 : Fin 2)
    refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
    have h2 : 2 < L := by omega
    let : Fact (2 < L) := ⟨h2⟩
    rw [show s01 L = Real.log |ons_spin01 L (Real.tanh beta)| / (L : ℝ) ^ 2 by
      simp [s01, h2]]
    rw [log_abs_of_sq_eq (hspin L h2).2.1]
    ring
  have hs10 : Filter.Tendsto s10 Filter.atTop (nhds q) := by
    have ht := ons_spinDet_density_tendsto beta hbeta hcrit (0 : Fin 2) (1 : Fin 2)
    refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
    have h2 : 2 < L := by omega
    let : Fact (2 < L) := ⟨h2⟩
    rw [show s10 L = Real.log |ons_spin10 L (Real.tanh beta)| / (L : ℝ) ^ 2 by
      simp [s10, h2]]
    rw [log_abs_of_sq_eq (hspin L h2).2.2.1]
    ring
  have hs00 : Filter.Tendsto s00 Filter.atTop (nhds q) := by
    have ht := ons_spinDet_density_tendsto beta hbeta hcrit (1 : Fin 2) (1 : Fin 2)
    refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
    have h2 : 2 < L := by omega
    let : Fact (2 < L) := ⟨h2⟩
    rw [show s00 L = Real.log |ons_spin00 L (Real.tanh beta)| / (L : ℝ) ^ 2 by
      simp [s00, h2]]
    rw [log_abs_of_sq_eq (hspin L h2).2.2.2]
    ring
  let mlog : ℕ → ℝ := fun L => max (s00 L) (max (s10 L) (max (s01 L) (s11 L)))
  have hmlog : Filter.Tendsto mlog Filter.atTop (nhds q) := by
    have ht := hs00.max (hs10.max (hs01.max hs11))
    simpa [mlog] using ht
  let xlog : ℕ → ℝ := fun L => if hL : 2 < L then
      letI : Fact (2 < L) := ⟨hL⟩
      Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / (L : ℝ) ^ 2
    else 0
  have htanh : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  have hlower : mlog ≤ xlog := by
    intro L
    by_cases h2 : 2 < L
    · let : Fact (2 < L) := ⟨h2⟩
      have hbounds := ons_abs_spin_le_X L htanh
      have hXpos := ons_X_pos (onsTorusGraph L) (Real.tanh beta) htanh
      have hden : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
      have hlog_le {p : ℝ} (hppos : 0 < |p|)
          (hp : |p| ≤ ons_X (onsTorusGraph L) (Real.tanh beta)) :
          Real.log |p| / (L : ℝ) ^ 2 ≤
            Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / (L : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right
          (Real.log_le_log hppos hp)
          hden
      have hp11 := spin_abs_pos_of_sq_eq
        (ons_spinDet_pos L beta hbeta hcrit 0 0) (hspin L h2).1
      have hp01 := spin_abs_pos_of_sq_eq
        (ons_spinDet_pos L beta hbeta hcrit 1 0) (hspin L h2).2.1
      have hp10 := spin_abs_pos_of_sq_eq
        (ons_spinDet_pos L beta hbeta hcrit 0 1) (hspin L h2).2.2.1
      have hp00 := spin_abs_pos_of_sq_eq
        (ons_spinDet_pos L beta hbeta hcrit 1 1) (hspin L h2).2.2.2
      simp only [mlog, s00, s10, s01, s11, xlog, dite_eq_left h2]
      refine max_le (hlog_le hp00 hbounds.1) (max_le (hlog_le hp10 hbounds.2.1)
        (max_le (hlog_le hp01 hbounds.2.2.1) (hlog_le hp11 hbounds.2.2.2)))
    · simp [mlog, s00, s10, s01, s11, xlog, h2]
  have hupper : xlog ≤ fun L => mlog L + Real.log 2 / (L : ℝ) ^ 2 := by
    intro L
    by_cases h2 : 2 < L
    · let : Fact (2 < L) := ⟨h2⟩
      let p00 := ons_spin00 L (Real.tanh beta)
      let p10 := ons_spin10 L (Real.tanh beta)
      let p01 := ons_spin01 L (Real.tanh beta)
      let p11 := ons_spin11 L (Real.tanh beta)
      let M := max |p00| (max |p10| (max |p01| |p11|))
      have hp11 : 0 < |p11| := by
        dsimp [p11]
        exact spin_abs_pos_of_sq_eq
          (ons_spinDet_pos L beta hbeta hcrit 0 0) (hspin L h2).1
      have hMpos : 0 < M := by
        dsimp [M]
        exact lt_of_lt_of_le hp11 <| le_trans (le_max_right _ _) <|
          le_trans (le_max_right _ _) (le_max_right _ _)
      have hsum_le : |p00| + |p10| + |p01| + |p11| ≤ 4 * M := by
        have h00 : |p00| ≤ M := le_max_left _ _
        have h10 : |p10| ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
        have h01 : |p01| ≤ M :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        have h11 : |p11| ≤ M :=
          le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        linarith
      have hXM : ons_X (onsTorusGraph L) (Real.tanh beta) ≤ 2 * M := by
        have hrev := ons_two_mul_X_le_sum_abs_spin L (Real.tanh beta)
        change 2 * ons_X (onsTorusGraph L) (Real.tanh beta) ≤
          |p00| + |p10| + |p01| + |p11| at hrev
        linarith
      have hXpos := ons_X_pos (onsTorusGraph L) (Real.tanh beta) htanh
      have hlogXM : Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) ≤
          Real.log 2 + Real.log M := by
        calc
          Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) ≤ Real.log (2 * M) :=
            Real.log_le_log hXpos hXM
          _ = Real.log 2 + Real.log M := Real.log_mul (by norm_num) hMpos.ne'
      have hlogM : Real.log M =
          max (Real.log |p00|) (max (Real.log |p10|)
            (max (Real.log |p01|) (Real.log |p11|))) := by
        have hp00 : 0 < |p00| := spin_abs_pos_of_sq_eq
          (ons_spinDet_pos L beta hbeta hcrit 1 1) (hspin L h2).2.2.2
        have hp10 : 0 < |p10| := spin_abs_pos_of_sq_eq
          (ons_spinDet_pos L beta hbeta hcrit 0 1) (hspin L h2).2.2.1
        have hp01 : 0 < |p01| := spin_abs_pos_of_sq_eq
          (ons_spinDet_pos L beta hbeta hcrit 1 0) (hspin L h2).2.1
        have hp0111 : 0 < max |p01| |p11| :=
          lt_of_lt_of_le hp11 (le_max_right _ _)
        have hp100111 : 0 < max |p10| (max |p01| |p11|) :=
          lt_of_lt_of_le hp0111 (le_max_right _ _)
        exact (Real.strictMonoOn_log.monotoneOn.map_max hp00
          hp100111).trans <|
          congrArg (max (Real.log |p00|)) <|
            (Real.strictMonoOn_log.monotoneOn.map_max hp10
              hp0111).trans <|
              congrArg (max (Real.log |p10|)) <|
                Real.strictMonoOn_log.monotoneOn.map_max hp01 hp11
      have hdenpos : 0 < (L : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast (show 0 < L by omega))
      have hdiv := div_le_div_of_nonneg_right hlogXM hdenpos.le
      rw [hlogM] at hdiv
      simp only [xlog, mlog, s00, s10, s01, s11, dite_eq_left h2]
      rw [max_div_div_right hdenpos.le, max_div_div_right hdenpos.le,
        max_div_div_right hdenpos.le]
      calc
        Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / (L : ℝ) ^ 2 ≤
            (Real.log 2 + max (Real.log |p00|)
              (max (Real.log |p10|) (max (Real.log |p01|) (Real.log |p11|)))) /
              (L : ℝ) ^ 2 := hdiv
        _ = max (Real.log |p00|) (max (Real.log |p10|)
              (max (Real.log |p01|) (Real.log |p11|))) / (L : ℝ) ^ 2 +
              Real.log 2 / (L : ℝ) ^ 2 := by ring
    · simp only [xlog, mlog, s00, s10, s01, s11, dite_eq_right h2, max_self,
        zero_add]
      exact div_nonneg (Real.log_nonneg (by norm_num)) (sq_nonneg _)
  have herr : Filter.Tendsto (fun L : ℕ => Real.log 2 / (L : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    have ht := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    have ht' := (tendsto_const_nhds.mul ht : Filter.Tendsto
      (fun L : ℕ => Real.log 2 * (1 / (L : ℝ)) ^ 2) Filter.atTop (nhds (Real.log 2 * 0 ^ 2)))
    simpa [div_eq_mul_inv, one_div, inv_pow] using ht'
  have hxlog : Filter.Tendsto xlog Filter.atTop (nhds q) :=
    Filter.Tendsto.squeeze hmlog (by simpa using hmlog.add herr) hlower hupper
  exact hxlog

lemma ons_KacWardResidue_of_spinKacWardMatrix (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcrit : beta ≠ ons_betaC) (hspin : ons_spinKacWardMatrixIdentities beta) :
    ons_KacWardResidue beta :=
  ons_KacWardResidue_of_spinKacWard beta hbeta hcrit
    (ons_spinKacWardIdentities_of_matrix beta hspin)

end StatMech.Onsager
