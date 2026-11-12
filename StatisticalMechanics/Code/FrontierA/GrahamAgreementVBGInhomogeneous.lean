/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamAgreementVBG
import Code.Ising.GHSInhomogeneous









open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness
open StatMech.Walls StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def grahamInhomOne (K : Sym2 V -> Real) (hf : V -> Real)
    (x : V) : Real :=
  expJ G.edgeFinset K hf (fun s => spin s x)


theorem ghsiFibreExpectation_mul_agree
    (K : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real)
    (k : V) (q : ConfigSpace V) :
    ghsiFibreExpectation G K hf
        (fun a b => F a b * grahamReplicaAgree a b k) q =
      ghsiFibreExpectation G K hf F q * vbg_coordUp k q := by
  unfold ghsiFibreExpectation ghsiFibreNumerator
  have hagree : forall a : ConfigSpace V,
      grahamReplicaAgree a (ghsLMate q a) k = vbg_coordUp k q :=
    fun a => grahamReplicaAgree_mate q a k
  simp_rw [hagree]
  rw [div_mul_eq_mul_div]
  congr 1
  change Finset.univ.sum (fun a =>
      ghsiFibreWeight G K hf q a *
        (F a (ghsLMate q a) * vbg_coordUp k q)) = _
  calc
    _ = Finset.univ.sum (fun a =>
        (ghsiFibreWeight G K hf q a * F a (ghsLMate q a)) *
          vbg_coordUp k q) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := (Finset.sum_mul Finset.univ
      (fun a => ghsiFibreWeight G K hf q a * F a (ghsLMate q a))
      (vbg_coordUp k q)).symm

theorem ghsiFibreExpectation_eq_of_fixed
    (K : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real)
    (q : ConfigSpace V) (r : Real)
    (hF : forall a, F a (ghsLMate q a) = r) :
    ghsiFibreExpectation G K hf F q = r := by
  unfold ghsiFibreExpectation ghsiFibreNumerator ghsiFibreMass
  simp_rw [hF]
  have hm : (∑ a : ConfigSpace V, ghsiFibreWeight G K hf q a) ≠ 0 :=
    (ghsiFibreMass_pos G K hf q).ne'
  change (Finset.univ.sum (fun a => ghsiFibreWeight G K hf q a * r)) /
      Finset.univ.sum (fun a => ghsiFibreWeight G K hf q a) = r
  rw [← Finset.sum_mul]
  field_simp [hm]

theorem ghsiFibreUU_self_eq
    (K : Sym2 V -> Real) (hf : V -> Real) (i : V) (q : ConfigSpace V) :
    ghsiFibreUU G K hf i i q = 1 - vbg_coordUp i q := by
  unfold ghsiFibreUU
  apply ghsiFibreExpectation_eq_of_fixed
  intro a
  rw [ghsL_uvar_mate]
  unfold vbg_coordUp
  by_cases hq : q i
  · simp [hq]
  · simp [hq, spin_sq]

theorem grahamInhomOne_nonneg
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x) (x : V) :
    0 <= grahamInhomOne G K hf x := by
  have h := ghsvp_expJ_nonneg G.edgeFinset K hf
    (fun e _ => hK e) hhf ({x} : Finset V)
  rw [show spinProd ({x} : Finset V) = (fun s => spin s x) by
    funext s
    simp [spinProd]] at h
  exact h

theorem grahamInhomOne_le_one
    (K : Sym2 V -> Real) (hf : V -> Real) (x : V) :
    grahamInhomOne G K hf x <= 1 := by
  unfold grahamInhomOne expJ ZJ
  have hZ : 0 < ∑ s : ConfigSpace V, wJ G.edgeFinset K hf s :=
    Finset.sum_pos (fun s _ => wJ_pos G.edgeFinset K hf s)
      Finset.univ_nonempty
  rw [div_le_one hZ]
  apply Finset.sum_le_sum
  intro s _
  have hw := (wJ_pos G.edgeFinset K hf s).le
  cases hs : s x <;> simp [spin, hs, hw]

theorem grahamInhomCov_nonneg
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j : V) :
    0 <= ghsiCovariance G K hf i j := by
  have h := gks_second_J G.edgeFinset K hf
    (fun e _ => hK e) hhf ({i} : Finset V) ({j} : Finset V)
  rw [show spinProd ({i} : Finset V) = (fun s => spin s i) by
      funext s; simp [spinProd],
    show spinProd ({j} : Finset V) = (fun s => spin s j) by
      funext s; simp [spinProd],
    show spinProd (({i} : Finset V) ∆ {j}) =
        (fun s => spin s i * spin s j) by
      funext s
      simpa [grahamPairSupport] using spinProd_grahamPairSupport s i j] at h
  unfold ghsiCovariance
  linarith

theorem grahamInhomAgreement_exp_eq
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) =
      (1 + grahamInhomOne G K hf k ^ 2) / 2 := by
  rw [show vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) =
      ghsiExp2 G K hf (fun a b => grahamReplicaAgree a b k) by
    rw [ghsiExp2_fibre]
    unfold vbg_exp
    apply Finset.sum_congr rfl
    intro q _
    rw [show ghsiFibreExpectation G K hf
        (fun a b => grahamReplicaAgree a b k) q = vbg_coordUp k q by
      have hmul := ghsiFibreExpectation_mul_agree G K hf
        (fun _ _ => (1 : Real)) k q
      rw [ghsiFibreExpectation_eq_of_fixed G K hf
        (fun _ _ => (1 : Real)) q 1 (by intro a; rfl)] at hmul
      simpa using hmul]]
  rw [show (fun a b : ConfigSpace V => grahamReplicaAgree a b k) =
      (fun a b => (1 / 2 : Real) * 1 +
        (1 / 2 : Real) * (spin a k * spin b k)) by
    funext a b
    rw [grahamReplicaAgree_eq_half]
    ring]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor]
  have hone : expJ G.edgeFinset K hf (fun _ : ConfigSpace V => (1 : Real)) = 1 :=
    expJ_one G K hf
  have hone2 : ghsiExp2 G K hf (fun _ _ => (1 : Real)) = 1 := by
    rw [show (fun _ _ : ConfigSpace V => (1 : Real)) =
        (fun a b => (fun _ => (1 : Real)) a * (fun _ => (1 : Real)) b) by
      funext a b; ring]
    rw [ghsiExp2_factor, hone]
    ring
  rw [hone2]
  unfold grahamInhomOne
  ring

theorem grahamInhomAgreement_exp_mul_fibreT
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    vbg_exp (ghsiAgreementProb G K hf)
        (fun q => vbg_coordUp k q * ghsiFibreT G K hf k q) =
      grahamInhomOne G K hf k := by
  rw [show vbg_exp (ghsiAgreementProb G K hf)
        (fun q => vbg_coordUp k q * ghsiFibreT G K hf k q) =
      ghsiExp2 G K hf
        (fun a b => grahamReplicaAgree a b k * tvar a b k) by
    rw [ghsiExp2_fibre]
    unfold vbg_exp
    apply Finset.sum_congr rfl
    intro q _
    rw [show ghsiFibreExpectation G K hf
        (fun a b => grahamReplicaAgree a b k * tvar a b k) q =
          vbg_coordUp k q * ghsiFibreT G K hf k q by
      rw [show (fun a b => grahamReplicaAgree a b k * tvar a b k) =
          (fun a b => tvar a b k * grahamReplicaAgree a b k) by
        funext a b; ring]
      rw [ghsiFibreExpectation_mul_agree]
      unfold ghsiFibreT
      ring]]
  simp_rw [grahamReplicaAgree_mul_tvar]
  unfold grahamInhomOne
  have hexp : (fun a b : ConfigSpace V => tvar a b k) =
      (fun a b => (1 / 2 : Real) * spin a k + (1 / 2 : Real) * spin b k) := by
    funext a b
    simp only [tvar]
    ring
  rw [hexp]
  simp only [ghsiExp2_add, ghsiExp2_const_mul,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  ring

theorem grahamInhomAgreement_exp_fibreT
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    vbg_exp (ghsiAgreementProb G K hf) (ghsiFibreT G K hf k) =
      grahamInhomOne G K hf k := by
  unfold vbg_exp ghsiFibreT
  rw [← ghsiExp2_fibre]
  unfold grahamInhomOne
  have hexp : (fun a b : ConfigSpace V => tvar a b k) =
      (fun a b => (1 / 2 : Real) * spin a k + (1 / 2 : Real) * spin b k) := by
    funext a b
    simp only [tvar]
    ring
  rw [hexp]
  simp only [ghsiExp2_add, ghsiExp2_const_mul,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  ring

theorem grahamInhomAgreement_exp_fibreUU
    (K : Sym2 V -> Real) (hf : V -> Real) (i j : V) :
    vbg_exp (ghsiAgreementProb G K hf) (ghsiFibreUU G K hf i j) =
      ghsiCovariance G K hf i j / 2 := by
  unfold vbg_exp ghsiFibreUU
  rw [← ghsiExp2_fibre]
  have hexp : (fun a b : ConfigSpace V => uvar a b i * uvar a b j) =
      (fun a b =>
        (1 / 4 : Real) * (spin a i * spin a j) +
        (-1 / 4 : Real) * (spin a i * spin b j) +
        (-1 / 4 : Real) * (spin a j * spin b i) +
        (1 / 4 : Real) * (spin b i * spin b j)) := by
    funext a b
    simp only [uvar]
    ring
  rw [hexp]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  unfold ghsiCovariance
  ring

theorem grahamInhomAgreement_exp_fibreUU_mul_fibreT
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    vbg_exp (ghsiAgreementProb G K hf)
        (fun q => ghsiFibreUU G K hf i j q * ghsiFibreT G K hf k q) =
      ghsiExp2 G K hf
        (fun a b => uvar a b i * uvar a b j * tvar a b k) := by
  rw [ghsiExp2_fibre]
  unfold vbg_exp
  apply Finset.sum_congr rfl
  intro q _
  rw [ghsi_fibreFactorization G K hf i j k q]

theorem grahamInhomAgreement_cov_fibreUU_fibreT
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    vbg_cov (ghsiAgreementProb G K hf)
        (ghsiFibreUU G K hf i j) (ghsiFibreT G K hf k) =
      ghsiUrsell3 G K hf i j k / 4 := by
  have huu : ghsiExp2 G K hf (fun a b => uvar a b i * uvar a b j) =
      ghsiCovariance G K hf i j / 2 := by
    rw [ghsiExp2_fibre]
    exact grahamInhomAgreement_exp_fibreUU G K hf i j
  have ht : ghsiExp2 G K hf (fun a b => tvar a b k) =
      grahamInhomOne G K hf k := by
    rw [ghsiExp2_fibre]
    exact grahamInhomAgreement_exp_fibreT G K hf k
  unfold vbg_cov
  rw [grahamInhomAgreement_exp_fibreUU_mul_fibreT,
    grahamInhomAgreement_exp_fibreUU, grahamInhomAgreement_exp_fibreT]
  rw [show ghsiUrsell3 G K hf i j k =
      4 * (ghsiExp2 G K hf
          (fun a b => uvar a b i * uvar a b j * tvar a b k) -
        ghsiExp2 G K hf (fun a b => uvar a b i * uvar a b j) *
          ghsiExp2 G K hf (fun a b => tvar a b k)) by
    exact ghsi_ursell_eq_four_duplicate_cov G K hf i j k]
  rw [huu, ht]
  ring

theorem grahamInhomAgreement_exp_fibreUU_mul_agree
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    vbg_exp (ghsiAgreementProb G K hf)
        (fun q => ghsiFibreUU G K hf i j q * vbg_coordUp k q) =
      ghsiExp2 G K hf (fun a b =>
        (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) := by
  rw [ghsiExp2_fibre]
  unfold vbg_exp
  apply Finset.sum_congr rfl
  intro q _
  change ghsiAgreementProb G K hf q *
      (ghsiFibreExpectation G K hf
        (fun a b => uvar a b i * uvar a b j) q * vbg_coordUp k q) = _
  rw [← ghsiFibreExpectation_mul_agree]

theorem grahamInhomUUAgree_expansion
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    ghsiExp2 G K hf (fun a b =>
        (uvar a b i * uvar a b j) * grahamReplicaAgree a b k) =
      (ghsiCovariance G K hf i j +
        grahamInhomOne G K hf k * ghsiUrsell3 G K hf i j k -
        ghsiCovariance G K hf i k * ghsiCovariance G K hf j k +
        ghsiCovariance G K hf i j * grahamInhomOne G K hf k ^ 2) / 4 := by
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
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  unfold ghsiCovariance ghsiUrsell3 grahamInhomOne
  ring

theorem grahamInhomAgreement_cov_fibreUU_agree
    (K : Sym2 V -> Real) (hf : V -> Real) (i j k : V) :
    vbg_cov (ghsiAgreementProb G K hf)
        (ghsiFibreUU G K hf i j) (vbg_coordUp k) =
      (grahamInhomOne G K hf k * ghsiUrsell3 G K hf i j k -
        ghsiCovariance G K hf i k * ghsiCovariance G K hf j k) / 4 := by
  unfold vbg_cov
  rw [grahamInhomAgreement_exp_fibreUU_mul_agree,
    grahamInhomUUAgree_expansion, grahamInhomAgreement_exp_fibreUU,
    grahamInhomAgreement_exp_eq]
  ring

theorem grahamInhomAgreement_cov_agree_fibreT
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    vbg_cov (ghsiAgreementProb G K hf) (vbg_coordUp k)
        (ghsiFibreT G K hf k) =
      (1 - grahamInhomOne G K hf k ^ 2) *
        grahamInhomOne G K hf k / 2 := by
  unfold vbg_cov
  rw [grahamInhomAgreement_exp_mul_fibreT,
    grahamInhomAgreement_exp_eq, grahamInhomAgreement_exp_fibreT]
  ring

theorem grahamInhomAgreement_var_agree
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    vbg_var (ghsiAgreementProb G K hf) (vbg_coordUp k) =
      (1 - grahamInhomOne G K hf k ^ 4) / 4 := by
  unfold vbg_var vbg_cov
  have hsquare : (fun q : ConfigSpace V => vbg_coordUp k q * vbg_coordUp k q) =
      vbg_coordUp k := by
    funext q
    unfold vbg_coordUp
    by_cases hq : q k <;> simp [hq]
  rw [hsquare, grahamInhomAgreement_exp_eq]
  ring

theorem grahamInhomAgreement_coord_pos_lt_one
    (K : Sym2 V -> Real) (hf : V -> Real) (k : V) :
    0 < vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) /\
      vbg_exp (ghsiAgreementProb G K hf) (vbg_coordUp k) < 1 := by
  let qT : ConfigSpace V := fun _ => true
  let qF : ConfigSpace V := fun _ => false
  have hprobpos : forall q : ConfigSpace V, 0 < ghsiAgreementProb G K hf q := by
    intro q
    unfold ghsiAgreementProb
    exact div_pos (ghsiFibreMass_pos G K hf q) (sq_pos_of_pos (ZJ_pos _ _ _))
  have hnonneg : forall q : ConfigSpace V,
      0 <= ghsiAgreementProb G K hf q * vbg_coordUp k q := by
    intro q
    exact mul_nonneg (hprobpos q).le (by
      unfold vbg_coordUp
      by_cases hq : q k <;> simp [hq])
  have hle : forall q : ConfigSpace V,
      ghsiAgreementProb G K hf q * vbg_coordUp k q <=
        ghsiAgreementProb G K hf q := by
    intro q
    unfold vbg_coordUp
    by_cases hq : q k <;> simp [hq, (hprobpos q).le]
  constructor
  · unfold vbg_exp
    exact Finset.sum_pos' (fun q _ => hnonneg q)
      <| by
        refine ⟨qT, Finset.mem_univ qT, ?_⟩
        rw [show vbg_coordUp k qT = 1 by simp [vbg_coordUp, qT], mul_one]
        exact hprobpos qT
  · unfold vbg_exp
    have hlt :
        (∑ q : ConfigSpace V, ghsiAgreementProb G K hf q * vbg_coordUp k q) <
          ∑ q : ConfigSpace V, ghsiAgreementProb G K hf q := by
      apply Finset.sum_lt_sum (fun q _ => hle q)
      refine ⟨qF, Finset.mem_univ qF, ?_⟩
      rw [show vbg_coordUp k qF = 0 by simp [vbg_coordUp, qF], mul_zero]
      exact hprobpos qF
    rwa [ghsiAgreementProb_sum_eq_one] at hlt



theorem ghsiFibreUU_antitone_all
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (i j : V) :
    Antitone (ghsiFibreUU G K hf i j) := by
  by_cases hij : i = j
  · subst j
    intro q r hqr
    rw [ghsiFibreUU_self_eq, ghsiFibreUU_self_eq]
    exact sub_le_sub_left (vbg_coordUp_monotone_local i hqr) 1
  · have hmono := ghsiDisagreementCorr_antitone G K hK i j
    intro q r hqr
    rw [ghsiFibreUU_eq_disagreementCorr G K hf i j hij,
      ghsiFibreUU_eq_disagreementCorr G K hf i j hij]
    exact hmono (ghsLAgreeFinset_monotone hqr)




theorem grahamAgreement_disagreement_product_lower
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    ghsiCovariance G K hf i k * ghsiCovariance G K hf j k <=
      4 * vbg_exp (ghsiAgreementProb G K hf)
        (fun q => ghsiFibreUU G K hf i k q *
          ghsiFibreUU G K hf j k q) := by
  let pi := ghsiAgreementProb G K hf
  let F := ghsiFibreUU G K hf i k
  let H := ghsiFibreUU G K hf j k
  have hFanti : Antitone F := ghsiFibreUU_antitone_all G K hf hK i k
  have hHanti : Antitone H := ghsiFibreUU_antitone_all G K hf hK j k
  have hnegF : Monotone (fun q => -F q) :=
    fun q r hqr => neg_le_neg (hFanti hqr)
  have hnegH : Monotone (fun q => -H q) :=
    fun q r hqr => neg_le_neg (hHanti hqr)
  have hfkg := fkg_inequality
    (ghsiAgreementProb_nonneg G K hf)
    (ghsiAgreementProb_sum_eq_one G K hf)
    (ghsiAgreementProb_fkg G K hf hK hhf) hnegF hnegH
  have hFexp : vbg_exp pi F = ghsiCovariance G K hf i k / 2 :=
    grahamInhomAgreement_exp_fibreUU G K hf i k
  have hHexp : vbg_exp pi H = ghsiCovariance G K hf j k / 2 :=
    grahamInhomAgreement_exp_fibreUU G K hf j k
  have hfkg' : vbg_exp pi F * vbg_exp pi H <=
      vbg_exp pi (fun q => F q * H q) := by
    unfold vbg_exp at hfkg ⊢
    have hnegFexp : (∑ q, pi q * -F q) = -(∑ q, pi q * F q) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hnegHexp : (∑ q, pi q * -H q) = -(∑ q, pi q * H q) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hprodexp : (∑ q, pi q * (-F q * -H q)) =
        ∑ q, pi q * (F q * H q) := by
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hnegFexp, hnegHexp, hprodexp] at hfkg
    nlinarith
  rw [hFexp, hHexp] at hfkg'
  change ghsiCovariance G K hf i k * ghsiCovariance G K hf j k <=
    4 * vbg_exp pi (fun q => F q * H q)
  nlinarith



theorem grahamImprovedGHS_inhomogeneous_strong
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    (1 - grahamInhomOne G K hf k ^ 2) *
        (-ghsiUrsell3 G K hf i j k) >=
      2 * grahamInhomOne G K hf k *
        ghsiCovariance G K hf i k * ghsiCovariance G K hf j k := by
  let pi := ghsiAgreementProb G K hf
  let F := ghsiFibreUU G K hf i j
  let T := ghsiFibreT G K hf k
  let Y := vbg_coordUp k
  have hpi0 : (0 : ConfigSpace V -> Real) <= pi :=
    ghsiAgreementProb_nonneg G K hf
  have hpi1 : ∑ q, pi q = 1 := ghsiAgreementProb_sum_eq_one G K hf
  have hpifkg : FKGLatticeCondition pi := ghsiAgreementProb_fkg G K hf hK hhf
  have hFanti : Antitone F := ghsiFibreUU_antitone_all G K hf hK i j
  have hnegF : Monotone (fun q => -F q) :=
    fun q r hqr => neg_le_neg (hFanti hqr)
  have hTmono : Monotone T := by
    intro q r hqr
    change ghsiFibreT G K hf k q <= ghsiFibreT G K hf k r
    rw [ghsiFibreT_eq_agreementMag G K hf k,
      ghsiFibreT_eq_agreementMag G K hf k]
    exact ghsiAgreementMag_monotone G K hf hK hhf k
      (ghsLAgreeFinset_monotone hqr)
  obtain ⟨hp0, hp1⟩ := grahamInhomAgreement_coord_pos_lt_one G K hf k
  have htri := vbg_thm1_configSpace hpi0 hpi1 hpifkg k
    (X := fun q => -F q) (Z := T) hnegF hTmono hp0 hp1
  have hcovNeg : vbg_cov pi (fun q => -F q) Y = -vbg_cov pi F Y := by
    rw [show (fun q => -F q) = fun q => (-1 : Real) * F q + 0 by
      funext q; ring]
    rw [vbg_cov_affine_left pi hpi1 F Y (-1) 0]
    ring
  have hcovNegT : vbg_cov pi (fun q => -F q) T = -vbg_cov pi F T := by
    rw [show (fun q => -F q) = fun q => (-1 : Real) * F q + 0 by
      funext q; ring]
    rw [vbg_cov_affine_left pi hpi1 F T (-1) 0]
    ring
  rw [hcovNeg, hcovNegT,
    grahamInhomAgreement_cov_fibreUU_agree,
    grahamInhomAgreement_cov_agree_fibreT,
    grahamInhomAgreement_var_agree,
    grahamInhomAgreement_cov_fibreUU_fibreT] at htri
  have hm0 := grahamInhomOne_nonneg G K hf hK hhf k
  have hm1 := grahamInhomOne_le_one G K hf k
  have hmSqLt : grahamInhomOne G K hf k ^ 2 < 1 := by
    rw [grahamInhomAgreement_exp_eq G K hf k] at hp1
    nlinarith
  let D := (1 - grahamInhomOne G K hf k ^ 2) *
      (-ghsiUrsell3 G K hf i j k) -
        2 * grahamInhomOne G K hf k *
          ghsiCovariance G K hf i k * ghsiCovariance G K hf j k
  have hprod : 0 <= (1 - grahamInhomOne G K hf k ^ 2) * D := by
    dsimp [D]
    nlinarith [htri]
  have hfactor : 0 < 1 - grahamInhomOne G K hf k ^ 2 := by linarith
  have hD : 0 <= D := nonneg_of_mul_nonneg_right hprod hfactor
  simpa [D] using hD



theorem grahamImprovedGHS_inhomogeneous
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall x, 0 <= hf x)
    (i j k : V) :
    ghsiUrsell3 G K hf i j k <=
      -2 * ghsiCovariance G K hf i k *
        ghsiCovariance G K hf j k * grahamInhomOne G K hf k := by
  have hs := grahamImprovedGHS_inhomogeneous_strong G K hf hK hhf i j k
  have hm0 := grahamInhomOne_nonneg G K hf hK hhf k
  have hm1 := grahamInhomOne_le_one G K hf k
  have hcik := grahamInhomCov_nonneg G K hf hK hhf i k
  have hcjk := grahamInhomCov_nonneg G K hf hK hhf j k
  have hp := mul_nonneg (mul_nonneg hcik hcjk) hm0
  have hneg : 0 <= -ghsiUrsell3 G K hf i j k := by
    have hfac : 0 < 1 - grahamInhomOne G K hf k ^ 2 := by
      have hp1 := (grahamInhomAgreement_coord_pos_lt_one G K hf k).2
      rw [grahamInhomAgreement_exp_eq G K hf k] at hp1
      nlinarith
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg (grahamInhomOne G K hf k)) hneg]

end StatMech.FrontierA
