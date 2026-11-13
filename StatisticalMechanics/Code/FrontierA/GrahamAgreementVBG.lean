/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.GHSLebowitz
import Code.Walls.vbgtriangle
import Code.FrontierA.GrahamImprovementBridge











open Finset SimpleGraph
open scoped BigOperators
open Classical

namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Walls
open StatMech.Walls.VBG
open StatMech.Walls.GhcEqGap StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def grahamReplicaAgree (a b : ConfigSpace V) (k : V) : Real :=
  if a k = b k then 1 else 0

theorem grahamReplicaAgree_mate (q a : ConfigSpace V) (k : V) :
    grahamReplicaAgree a (ghsLMate q a) k = vbg_coordUp k q := by
  unfold grahamReplicaAgree vbg_coordUp ghsLMate
  by_cases hq : q k <;> cases ha : a k <;> simp [hq, ha]

theorem grahamReplicaAgree_eq_half (a b : ConfigSpace V) (k : V) :
    grahamReplicaAgree a b k = (1 + spin a k * spin b k) / 2 := by
  unfold grahamReplicaAgree spin
  cases ha : a k <;> cases hb : b k <;> norm_num [ha, hb]

theorem grahamReplicaAgree_mul_tvar (a b : ConfigSpace V) (k : V) :
    grahamReplicaAgree a b k * tvar a b k = tvar a b k := by
  unfold grahamReplicaAgree tvar spin
  cases ha : a k <;> cases hb : b k <;> norm_num [ha, hb]



theorem ghsLFibreExpectation_mul_agree
    (beta h : Real) (F : ConfigSpace V -> ConfigSpace V -> Real)
    (k : V) (q : ConfigSpace V) :
    ghsLFibreExpectation G beta h
        (fun a b => F a b * grahamReplicaAgree a b k) q =
      ghsLFibreExpectation G beta h F q * vbg_coordUp k q := by
  unfold ghsLFibreExpectation ghsLFibreNumerator
  have hagree : forall a : ConfigSpace V,
      grahamReplicaAgree a (ghsLMate q a) k = vbg_coordUp k q :=
    fun a => grahamReplicaAgree_mate q a k
  simp_rw [hagree]
  rw [div_mul_eq_mul_div]
  congr 1
  change Finset.univ.sum (fun a =>
      ghsLFibreWeight G beta h q a *
        (F a (ghsLMate q a) * vbg_coordUp k q)) = _
  calc
    _ = Finset.univ.sum (fun a =>
        (ghsLFibreWeight G beta h q a * F a (ghsLMate q a)) *
          vbg_coordUp k q) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := (Finset.sum_mul Finset.univ
      (fun a => ghsLFibreWeight G beta h q a * F a (ghsLMate q a))
      (vbg_coordUp k q)).symm

theorem ghsLFibreExpectation_eq_of_fixed
    (beta h : Real) (F : ConfigSpace V -> ConfigSpace V -> Real)
    (q : ConfigSpace V) (r : Real)
    (hF : forall a, F a (ghsLMate q a) = r) :
    ghsLFibreExpectation G beta h F q = r := by
  unfold ghsLFibreExpectation ghsLFibreNumerator ghsLFibreMass
  simp_rw [hF]
  have hm : (∑ a : ConfigSpace V, ghsLFibreWeight G beta h q a) ≠ 0 :=
    (ghsLFibreMass_pos G beta h q).ne'
  change (Finset.univ.sum (fun a => ghsLFibreWeight G beta h q a * r)) /
      Finset.univ.sum (fun a => ghsLFibreWeight G beta h q a) = r
  rw [← Finset.sum_mul]
  field_simp [hm]

theorem ghsLFibreUU_self_eq
    (beta h : Real) (i : V) (q : ConfigSpace V) :
    ghsLFibreUU G beta h i i q = 1 - vbg_coordUp i q := by
  unfold ghsLFibreUU
  apply ghsLFibreExpectation_eq_of_fixed
  intro a
  rw [ghsL_uvar_mate]
  unfold vbg_coordUp
  by_cases hq : q i
  · simp [hq]
  · simp [hq, spin_sq]

theorem vbg_coordUp_monotone_local (i : V) :
    Monotone (vbg_coordUp i : ConfigSpace V -> Real) := by
  intro q r hqr
  have hi := hqr i
  by_cases hq : q i
  · have hr : r i := (Bool.le_iff_imp.mp hi) hq
    simp [vbg_coordUp, hq, hr]
  · by_cases hr : r i <;> simp [vbg_coordUp, hq, hr]

theorem grahamAgreement_exp_eq
    (beta h : Real) (k : V) :
    vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) =
      (1 + onePt G beta h k ^ 2) / 2 := by
  rw [show vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) =
      isingExp2 G beta h (fun a b => grahamReplicaAgree a b k) by
    rw [ghsL_isIngExp2_fibre]
    unfold vbg_exp
    apply Finset.sum_congr rfl
    intro q _
    rw [show ghsLFibreExpectation G beta h
        (fun a b => grahamReplicaAgree a b k) q = vbg_coordUp k q by
      simpa using ghsLFibreExpectation_mul_agree G beta h
        (fun _ _ => (1 : Real)) k q]
    ]
  rw [show (fun a b : ConfigSpace V => grahamReplicaAgree a b k) =
      (fun a b => (1 / 2 : Real) * 1 +
        (1 / 2 : Real) * (spin a k * spin b k)) by
    funext a b
    rw [grahamReplicaAgree_eq_half]
    ring]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor]
  have hone : isingExpectation G beta h (fun _ : ConfigSpace V => (1 : Real)) = 1 := by
    unfold isingExpectation
    simpa using isingProb_sum_eq_one G beta h
  have hone2 : isingExp2 G beta h (fun _ _ => (1 : Real)) = 1 := by
    rw [show (fun _ _ : ConfigSpace V => (1 : Real)) =
        (fun a b => (fun _ => (1 : Real)) a * (fun _ => (1 : Real)) b) by
      funext a b; ring]
    rw [isingExp2_factor, hone]
    ring
  rw [hone2]
  unfold onePt
  ring

theorem grahamAgreement_exp_mul_fibreT
    (beta h : Real) (k : V) :
    vbg_exp (ghsLAgreementProb G beta h)
        (fun q => vbg_coordUp k q * ghsLFibreT G beta h k q) =
      onePt G beta h k := by
  rw [show vbg_exp (ghsLAgreementProb G beta h)
        (fun q => vbg_coordUp k q * ghsLFibreT G beta h k q) =
      isingExp2 G beta h
        (fun a b => grahamReplicaAgree a b k * tvar a b k) by
    rw [ghsL_isIngExp2_fibre]
    unfold vbg_exp
    apply Finset.sum_congr rfl
    intro q _
    rw [show ghsLFibreExpectation G beta h
        (fun a b => grahamReplicaAgree a b k * tvar a b k) q =
          vbg_coordUp k q * ghsLFibreT G beta h k q by
      rw [show (fun a b => grahamReplicaAgree a b k * tvar a b k) =
          (fun a b => tvar a b k * grahamReplicaAgree a b k) by
        funext a b; ring]
      rw [ghsLFibreExpectation_mul_agree]
      unfold ghsLFibreT
      ring]
    ]
  simp_rw [grahamReplicaAgree_mul_tvar]
  exact (ghsDV_onePt_eq_tt G beta h k).symm

theorem grahamAgreement_exp_fibreT
    (beta h : Real) (k : V) :
    vbg_exp (ghsLAgreementProb G beta h) (ghsLFibreT G beta h k) =
      onePt G beta h k := by
  unfold vbg_exp
  unfold ghsLFibreT
  rw [← ghsL_isIngExp2_fibre]
  exact ghsDV_onePt_eq_tt G beta h k |>.symm

theorem grahamAgreement_exp_fibreUU
    (beta h : Real) (i j : V) :
    vbg_exp (ghsLAgreementProb G beta h) (ghsLFibreUU G beta h i j) =
      cov2 G beta h i j / 2 := by
  unfold vbg_exp
  unfold ghsLFibreUU
  rw [← ghsL_isIngExp2_fibre]
  have hcov := ghsDV_cov2_eq_two_uu G beta h i j
  linarith

theorem grahamAgreement_exp_fibreUU_mul_fibreT
    (beta h : Real) (i j k : V) :
    vbg_exp (ghsLAgreementProb G beta h)
        (fun q => ghsLFibreUU G beta h i j q *
          ghsLFibreT G beta h k q) =
      isingExp2 G beta h
        (fun a b => uvar a b i * uvar a b j * tvar a b k) := by
  rw [ghsL_isIngExp2_fibre]
  unfold vbg_exp
  apply Finset.sum_congr rfl
  intro q _
  rw [ghsL_fibreFactorization G beta h i j k q]

theorem grahamAgreement_cov_fibreUU_fibreT
    (beta h : Real) (i j k : V) :
    vbg_cov (ghsLAgreementProb G beta h)
        (ghsLFibreUU G beta h i j) (ghsLFibreT G beta h k) =
      eg_ursell3 G beta h i j k / 4 := by
  unfold vbg_cov
  rw [grahamAgreement_exp_fibreUU_mul_fibreT,
    grahamAgreement_exp_fibreUU, grahamAgreement_exp_fibreT]
  have hu := ghsL_ursell_eq_four_duplicate_cov G beta h i j k
  have ht := ghsDV_onePt_eq_tt G beta h k
  have hii := ghsDV_cov2_eq_two_uu G beta h i j
  change eg_ursell3 G beta h i j k = 4 *
      (isingExp2 G beta h (fun a b => uvar a b i * uvar a b j * tvar a b k) -
        isingExp2 G beta h (fun a b => uvar a b i * uvar a b j) *
          isingExp2 G beta h (fun a b => tvar a b k)) at hu
  rw [hii, ht]
  linarith

theorem grahamAgreement_exp_fibreUU_mul_agree
    (beta h : Real) (i j k : V) :
    vbg_exp (ghsLAgreementProb G beta h)
        (fun q => ghsLFibreUU G beta h i j q * vbg_coordUp k q) =
      isingExp2 G beta h (fun a b =>
        (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) := by
  rw [ghsL_isIngExp2_fibre]
  unfold vbg_exp
  apply Finset.sum_congr rfl
  intro q _
  change ghsLAgreementProb G beta h q *
      (ghsLFibreExpectation G beta h
        (fun a b => uvar a b i * uvar a b j) q * vbg_coordUp k q) = _
  rw [← ghsLFibreExpectation_mul_agree]

theorem grahamUUAgree_expansion
    (beta h : Real) (i j k : V) :
    isingExp2 G beta h (fun a b =>
        (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) =
      (cov2 G beta h i j +
        onePt G beta h k * eg_ursell3 G beta h i j k -
        cov2 G beta h i k * cov2 G beta h j k +
        cov2 G beta h i j * onePt G beta h k ^ 2) / 4 := by
  rw [show (fun a b : ConfigSpace V =>
      (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) =
      (fun a b =>
        (1 / 8 : Real) * (spin a i * spin a j) +
        (-1 / 8 : Real) * (spin a i * spin b j) +
        (-1 / 8 : Real) * (spin a j * spin b i) +
        (1 / 8 : Real) * (spin b i * spin b j) +
        (1 / 8 : Real) * ((spin a i * spin a j * spin a k) * spin b k) +
        (-1 / 8 : Real) * ((spin a i * spin a k) * (spin b j * spin b k)) +
        (-1 / 8 : Real) * ((spin a j * spin a k) * (spin b i * spin b k)) +
        (1 / 8 : Real) * (spin a k * (spin b i * spin b j * spin b k))) by
    funext a b
    rw [grahamReplicaAgree_eq_half]
    simp only [uvar]
    ring]
  simp only [isingExp2_add, isingExp2_const_mul, isingExp2_factor,
    isingExp2_factor_a, isingExp2_factor_b]
  unfold cov2 onePt eg_ursell3
  ring

theorem grahamAgreement_cov_fibreUU_agree
    (beta h : Real) (i j k : V) :
    vbg_cov (ghsLAgreementProb G beta h)
        (ghsLFibreUU G beta h i j) (vbg_coordUp k) =
      (onePt G beta h k * eg_ursell3 G beta h i j k -
        cov2 G beta h i k * cov2 G beta h j k) / 4 := by
  unfold vbg_cov
  rw [grahamAgreement_exp_fibreUU_mul_agree,
    grahamUUAgree_expansion, grahamAgreement_exp_fibreUU,
    grahamAgreement_exp_eq]
  ring

theorem grahamAgreement_cov_agree_fibreT
    (beta h : Real) (k : V) :
    vbg_cov (ghsLAgreementProb G beta h) (vbg_coordUp k)
        (ghsLFibreT G beta h k) =
      (1 - onePt G beta h k ^ 2) * onePt G beta h k / 2 := by
  unfold vbg_cov
  rw [grahamAgreement_exp_mul_fibreT,
    grahamAgreement_exp_eq, grahamAgreement_exp_fibreT]
  ring

theorem grahamAgreement_var_agree
    (beta h : Real) (k : V) :
    vbg_var (ghsLAgreementProb G beta h) (vbg_coordUp k) =
      (1 - onePt G beta h k ^ 4) / 4 := by
  unfold vbg_var vbg_cov
  have hsquare : (fun q : ConfigSpace V => vbg_coordUp k q * vbg_coordUp k q) =
      vbg_coordUp k := by
    funext q
    unfold vbg_coordUp
    by_cases hq : q k <;> simp [hq]
  rw [hsquare, grahamAgreement_exp_eq]
  ring

theorem grahamAgreement_coord_pos_lt_one
    (beta h : Real) (k : V) :
    0 < vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) /\
      vbg_exp (ghsLAgreementProb G beta h) (vbg_coordUp k) < 1 := by
  let qT : ConfigSpace V := fun _ => true
  let qF : ConfigSpace V := fun _ => false
  have hprobpos : forall q : ConfigSpace V,
      0 < ghsLAgreementProb G beta h q := by
    intro q
    unfold ghsLAgreementProb
    exact div_pos (ghsLFibreMass_pos G beta h q)
      (sq_pos_of_pos (isingZ_pos G beta h))
  have hnonneg : forall q : ConfigSpace V,
      0 <= ghsLAgreementProb G beta h q * vbg_coordUp k q := by
    intro q
    exact mul_nonneg (hprobpos q).le (by
      unfold vbg_coordUp
      by_cases hq : q k <;> simp [hq])
  have hle : forall q : ConfigSpace V,
      ghsLAgreementProb G beta h q * vbg_coordUp k q <=
        ghsLAgreementProb G beta h q := by
    intro q
    unfold vbg_coordUp
    by_cases hq : q k <;> simp [hq, (hprobpos q).le]
  constructor
  · unfold vbg_exp
    exact Finset.sum_pos' (fun q _ => hnonneg q)
      ⟨qT, Finset.mem_univ qT, by
        rw [show vbg_coordUp k qT = 1 by simp [vbg_coordUp, qT], mul_one]
        exact hprobpos qT⟩
  · unfold vbg_exp
    have hlt :
        (∑ q : ConfigSpace V,
          ghsLAgreementProb G beta h q * vbg_coordUp k q) <
          ∑ q : ConfigSpace V, ghsLAgreementProb G beta h q := by
      apply Finset.sum_lt_sum (fun q _ => hle q)
      exact ⟨qF, Finset.mem_univ qF, by
        rw [show vbg_coordUp k qF = 0 by simp [vbg_coordUp, qF], mul_zero]
        exact hprobpos qF⟩
    rwa [ghsLAgreementProb_sum_eq_one] at hlt



theorem grahamImprovedGHS_agreement_strong
    (beta h : Real) (hbeta : 0 <= beta) (hh : 0 <= h)
    (i j k : V) :
    (1 - onePt G beta h k ^ 2) * (-eg_ursell3 G beta h i j k) >=
      2 * onePt G beta h k * cov2 G beta h i k * cov2 G beta h j k := by
  let pi := ghsLAgreementProb G beta h
  let F := ghsLFibreUU G beta h i j
  let T := ghsLFibreT G beta h k
  let Y := vbg_coordUp k
  have hpi0 : (0 : ConfigSpace V -> Real) <= pi :=
    ghsLAgreementProb_nonneg G beta h
  have hpi1 : ∑ q, pi q = 1 := ghsLAgreementProb_sum_eq_one G beta h
  have hpifkg : FKGLatticeCondition pi :=
    ghsLAgreementProb_fkg G beta h hbeta hh
  have hFanti : Antitone F := by
    by_cases hij : i = j
    · subst j
      intro q r hqr
      change ghsLFibreUU G beta h i i r <= ghsLFibreUU G beta h i i q
      rw [ghsLFibreUU_self_eq, ghsLFibreUU_self_eq]
      exact sub_le_sub_left (vbg_coordUp_monotone_local i hqr) 1
    · exact ghsLFibreUU_antitone_of_eq G beta h hbeta i j
        (fun q => ghsLFibreUU_eq_disagreementCorr G beta h i j hij q)
  have hnegF : Monotone (fun q => -F q) :=
    fun q r hqr => neg_le_neg (hFanti hqr)
  have hTmono : Monotone T := by
    exact ghsLFibreT_monotone_of_eq G beta h hbeta hh k
      (fun q => ghsLFibreT_eq_agreementMag G beta h k q)
  obtain ⟨hp0, hp1⟩ := grahamAgreement_coord_pos_lt_one G beta h k
  have htri := vbg_thm1_configSpace hpi0 hpi1 hpifkg k
    (X := fun q => -F q) (Z := T) hnegF hTmono hp0 hp1
  have hcovNeg : vbg_cov pi (fun q => -F q) Y =
      -vbg_cov pi F Y := by
    rw [show (fun q => -F q) = fun q => (-1 : Real) * F q + 0 by
      funext q; ring]
    rw [vbg_cov_affine_left pi hpi1 F Y (-1) 0]
    ring
  have hcovNegT : vbg_cov pi (fun q => -F q) T =
      -vbg_cov pi F T := by
    rw [show (fun q => -F q) = fun q => (-1 : Real) * F q + 0 by
      funext q; ring]
    rw [vbg_cov_affine_left pi hpi1 F T (-1) 0]
    ring
  rw [hcovNeg, hcovNegT,
    grahamAgreement_cov_fibreUU_agree,
    grahamAgreement_cov_agree_fibreT,
    grahamAgreement_var_agree,
    grahamAgreement_cov_fibreUU_fibreT] at htri
  have hm0 : 0 <= onePt G beta h k :=
    expectation_spin_nonneg G beta h hbeta hh k
  have hm1 : onePt G beta h k <= 1 := expectation_spin_le_one G beta h k
  have hmSqLt : onePt G beta h k ^ 2 < 1 := by
    rw [grahamAgreement_exp_eq G beta h k] at hp1
    nlinarith
  let D := (1 - onePt G beta h k ^ 2) *
      (-eg_ursell3 G beta h i j k) -
        2 * onePt G beta h k * cov2 G beta h i k * cov2 G beta h j k
  have hprod : 0 <= (1 - onePt G beta h k ^ 2) * D := by
    dsimp [D]
    nlinarith [htri]
  have hfactor : 0 < 1 - onePt G beta h k ^ 2 := by linarith
  have hD : 0 <= D := nonneg_of_mul_nonneg_right hprod hfactor
  simpa [D] using hD



theorem grahamImprovedGHS_agreement
    (beta h : Real) (hbeta : 0 <= beta) (hh : 0 <= h)
    (i j k : V) :
    eg_ursell3 G beta h i j k <=
      -2 * cov2 G beta h i k * cov2 G beta h j k * onePt G beta h k := by
  have hs := grahamImprovedGHS_agreement_strong G beta h hbeta hh i j k
  have hu : eg_ursell3 G beta h i j k <= 0 := by
    exact gc_ursell_nonpos_of_signDominance G beta h hbeta hh i
      (ghs_signDominance G beta h hbeta hh i) j k
  have hm0 : 0 <= onePt G beta h k :=
    expectation_spin_nonneg G beta h hbeta hh k
  have hm1 : onePt G beta h k <= 1 := expectation_spin_le_one G beta h k
  have hcik := grahamCov2_nonneg G beta h hbeta hh i k
  have hcjk := grahamCov2_nonneg G beta h hbeta hh j k
  nlinarith [mul_nonneg (mul_nonneg hcik hcjk) hm0]



theorem grahamImprovedGHS_all
    (beta h : Real) (hbeta : 0 <= beta) (hh : 0 <= h)
    (i j k : V) :
    eg_ursell3 G beta h i j k <= grahamImprovedGHSRHS G beta h i j k := by
  simpa [grahamImprovedGHSRHS] using
    grahamImprovedGHS_agreement G beta h hbeta hh i j k



theorem grahamGhostCorrectedBound_all
    (beta h : Real) (hbeta : 0 <= beta) (hh : 0 <= h)
    (i j k : V) :
    gc_lebowitzU4 G beta h i j k <= grahamGhostCorrectedRHS G beta h i j k := by
  rw [grahamGhostFourPoint_iff_improvedGHS]
  exact grahamImprovedGHS_all G beta h hbeta hh i j k

end StatMech.FrontierA
