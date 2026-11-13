/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.WiredBoxCriticalGeneral

open MeasureTheory
open scoped BigOperators

namespace StatMech
namespace OSSS
namespace FKSharpnessHomogeneous

open Lattice FK IsingFK
open WiredBoxLocalized WiredBoxSharpness WiredBoxCritical WiredBoxCriticalGeneral



private theorem allClosed_not_connToBdry
    (d n : Nat) :
    ¬ (ConnToBdry (boxGraph d n) (boxBoundary d n)
      (fun _ => false) (boxOrigin d n)) := by
  rintro ⟨y, hy, hconn⟩
  have hopen : openSub (boxGraph d n) (fun _ => false) = ⊥ := by
    ext x z
    simp [openSub_adj]
  unfold StatMech.FK.Connected at hconn
  rw [hopen, SimpleGraph.reachable_bot] at hconn
  subst y
  change (0 : Site d) ∈ vertexBoundary d n at hy
  exact hy.2 (by intro i; simp)



theorem wiredBoxBoundaryMass_lt_one
    (d n : Nat) (q beta : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) :
    (wiredFiniteMeasure d n
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) < 1 := by
  classical
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    dsimp [p]
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-beta)]
  let mu := wiredFkProb (boxGraph d n) (boxBoundary d n) p q
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | ConnToBdry (boxGraph d n) (boxBoundary d n) omega (boxOrigin d n)}
  have hmeas : MeasurableSet (boxRestrict d n ⁻¹' A) :=
    (continuous_boxRestrict d n).measurable MeasurableSet.of_discrete
  have hmass :
      (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) =
        ∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega := by
    rw [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl]
    simpa [mu] using
      fkgq_wiredFiniteMeasure_real_boxRestrictEvent n hp hp1
        (zero_lt_one.trans_le hq) A hmeas
  rw [hmass]
  have hterm : forall omega,
      A.indicator (fun _ => (1 : Real)) omega * mu omega <= mu omega := by
    intro omega
    by_cases homega : omega ∈ A
    · simp [Set.indicator_of_mem homega]
    · rw [Set.indicator_of_notMem homega, zero_mul]
      exact wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n)
        hp hp1 (zero_lt_one.trans_le hq) omega
  have hclosed : (fun _ => false) ∉ A := allClosed_not_connToBdry d n
  have hstrict :
      A.indicator (fun _ => (1 : Real)) (fun _ => false) *
          mu (fun _ => false) < mu (fun _ => false) := by
    rw [Set.indicator_of_notMem hclosed, zero_mul]
    exact wiredFkProb_pos (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq) _
  calc
    (∑ omega, A.indicator (fun _ => (1 : Real)) omega * mu omega) <
        ∑ omega, mu omega :=
      Finset.sum_lt_sum (fun omega _ => hterm omega)
        ⟨fun _ => false, Finset.mem_univ _, hstrict⟩
    _ = 1 := wiredFkProb_sum_eq_one (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq)



theorem wiredBoxBoundary_exponential_decay
    (d : Nat) (q beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta : 0 < beta) (hsub : beta < fkCriticalBetaQ d q) :
    exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n ->
      (wiredFiniteMeasure d n
          (by
            have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
            linarith : 0 < 1 - Real.exp (-beta))
          (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) <=
          Real.exp (-((n : Real) / Q)) := by
  classical
  obtain ⟨Q0, hQ0, hdecay⟩ :=
    wiredOuterInner_exponential_decay_below_fkCriticalBetaQ
      d q beta hd hq hbeta hsub
  let delta := (fkCriticalBetaQ d q - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let R := Q0 / delta
  have hR : 0 < R := div_pos hQ0 hdelta
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    dsimp [p]
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-beta)]
  let a : Nat -> Real := fun n =>
    (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
  have ha0 : forall n, 0 <= a n := fun _ => measureReal_nonneg
  have ha1lt : a 1 < 1 := by
    simpa [a, p] using wiredBoxBoundaryMass_lt_one d 1 q beta hq hbeta
  let r := (a 1 + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith [ha0 1]
  have hr1 : r < 1 := by dsimp [r]; linarith
  let Q1 := -1 / Real.log r
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hQ1 : 0 < Q1 := by
    dsimp [Q1]
    exact div_pos_of_neg_of_neg (by norm_num) hlogr
  have hexpQ1 : Real.exp (-(1 / Q1)) = r := by
    have hlogne : Real.log r ≠ 0 := ne_of_lt hlogr
    rw [show -(1 / Q1) = Real.log r by
      dsimp [Q1]
      field_simp]
    exact Real.exp_log hr0
  let Q := max (3 * R) Q1
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (by norm_num) hR) (le_max_left _ _)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  change a n <= Real.exp (-((n : Real) / Q))
  by_cases hn1 : n = 1
  · subst n
    have hQ1Q : Q1 <= Q := le_max_right _ _
    have hexpMono : Real.exp (-(1 / Q1)) <= Real.exp (-(1 / Q)) := by
      apply Real.exp_le_exp.mpr
      have := one_div_le_one_div_of_le hQ1 hQ1Q
      linarith
    calc
      a 1 <= r := by dsimp [r]; linarith
      _ = Real.exp (-(1 / Q1)) := hexpQ1.symm
      _ <= Real.exp (-(1 / Q)) := hexpMono
      _ = Real.exp (-(((1 : Nat) : Real) / Q)) := by norm_num
  · have hn2 : 2 <= n := by omega
    let k := n / 2
    have hk : 1 <= k := by dsimp [k]; omega
    have hnk : n <= 3 * k := by dsimp [k]; omega
    have hanti := fkgq_boxBdryConnEvent_diag_antitone
      (d := d) hp hp1 hq
    have hind : 2 * k - 1 <= n - 1 := by dsimp [k]; omega
    have hmassMono : a n <= a (2 * k) := by
      have h := hanti hind
      simpa [a, Nat.sub_add_cancel (by omega : 1 <= n),
        Nat.sub_add_cancel (by omega : 1 <= 2 * k)] using h
    have houter : a (2 * k) <= wiredOuterInnerTheta d q beta k := by
      rw [show a (2 * k) =
          (wiredFiniteMeasure d (2 * k) hp hp1 (zero_lt_one.trans_le hq) :
            Measure _).real (boxBdryConnEvent d (2 * k)) by rfl,
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d k hk q beta hq hbeta]
      exact measureReal_mono
        (boxBdryConnEvent_subset_le k (2 * k) hk (n_le_two_mul k))
        (measure_ne_top _ _)
    have hlocalized :
        wiredOuterInnerTheta d q beta k <= Real.exp (-((k : Real) / R)) := by
      have h := hdecay k hk
      convert h using 1
      dsimp [R, delta]
      field_simp
    have hQR : 3 * R <= Q := le_max_left _ _
    have hrate1 : (n : Real) / (3 * R) <= (k : Real) / R := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hR) hR]
      have hnkR : (n : Real) <= 3 * (k : Real) := by exact_mod_cast hnk
      nlinarith
    have hrate2 : (n : Real) / Q <= (n : Real) / (3 * R) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hR) hQR
    calc
      a n <= a (2 * k) := hmassMono
      _ <= wiredOuterInnerTheta d q beta k := houter
      _ <= Real.exp (-((k : Real) / R)) := hlocalized
      _ <= Real.exp (-((n : Real) / (3 * R))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ <= Real.exp (-((n : Real) / Q)) :=
        Real.exp_le_exp.mpr (by linarith)



theorem betaFKThetaQ_meanField_near_critical
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    exists c : Real, 0 < c ∧ forall beta,
      fkCriticalBetaQ d q <= beta -> beta <= fkCriticalBetaQ d q + 1 ->
        c * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta := by
  let c := wiredSharpConstant d (fkCriticalBetaQ d q + 1)
  refine ⟨c, wiredSharpConstant_pos d _, ?_⟩
  intro beta hcrit hupper
  have hexp : Real.exp (-(fkCriticalBetaQ d q + 1)) <= Real.exp (-beta) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow := pow_le_pow_left₀
    (Real.exp_pos (-(fkCriticalBetaQ d q + 1))).le hexp (2 * d)
  have hc : c <= wiredSharpConstant d beta := by
    dsimp [c]
    unfold wiredSharpConstant
    exact div_le_div_of_nonneg_right hpow (by norm_num)
  have hgap : 0 <= beta - fkCriticalBetaQ d q := sub_nonneg.mpr hcrit
  exact (mul_le_mul_of_nonneg_right hc hgap).trans
    ((fkSharpness_homogeneous d q hd hq).1 beta hcrit)




theorem fkSharpness_homogeneous_physical_boxes
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    (exists c : Real, 0 < c ∧ forall beta,
      fkCriticalBetaQ d q <= beta -> beta <= fkCriticalBetaQ d q + 1 ->
        c * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta) ∧
    (forall beta (hbeta : 0 < beta), beta < fkCriticalBetaQ d q ->
      exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n ->
        (wiredFiniteMeasure d n
            (by
              have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
              linarith : 0 < 1 - Real.exp (-beta))
            (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
            (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) <=
            Real.exp (-((n : Real) / Q))) := by
  constructor
  · exact betaFKThetaQ_meanField_near_critical d q hd hq
  · intro beta hbeta hsub
    exact wiredBoxBoundary_exponential_decay d q beta hd hq hbeta hsub

end FKSharpnessHomogeneous
end OSSS
end StatMech
