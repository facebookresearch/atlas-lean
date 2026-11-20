/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationMiddleCancellation









namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_matrixBucketE
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → E ↦
        (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
    ons_loopWeight M loop

noncomputable def ons_matrixBucketN
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → E ↦
        ¬ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
    ons_loopWeight M loop

theorem ons_matrixLoopSum_orientation_symm_of_loopRev
    {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} [NeZero n]
    (rev : E → E) (hrev : Function.Involutive rev)
    (M : Matrix E E ℂ)
    (hloopRev : ∀ loop : Fin n → E,
      ons_loopWeight M (ons_involutiveLoopRev rev loop) =
        ons_loopWeight M loop)
    (e : E) :
    (∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → E ↦
          (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = rev e),
      ons_loopWeight M loop) =
      ∑ loop ∈ Finset.univ.filter
        (fun loop : Fin n → E ↦
          (∃ i, loop i = rev e) ∧ ¬ ∃ j, loop j = e),
        ons_loopWeight M loop := by
  refine Finset.sum_nbij'
    (ons_involutiveLoopRev rev) (ons_involutiveLoopRev rev)
    ?_ ?_ ?_ ?_ ?_
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_involutiveLoopRev rev hrev,
        hrev e]
      exact ⟨i, hie⟩
    · rwa [ons_visits_involutiveLoopRev rev hrev]
  · intro loop hloop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop ⊢
    obtain ⟨⟨i, hie⟩, hne⟩ := hloop
    constructor
    · rw [ons_visits_involutiveLoopRev rev hrev]
      exact ⟨i, hie⟩
    · rwa [ons_visits_involutiveLoopRev rev hrev, hrev e]
  · exact fun loop _ ↦ ons_involutiveLoopRev_involutive rev hrev loop
  · exact fun loop _ ↦ ons_involutiveLoopRev_involutive rev hrev loop
  · intro loop hloop
    exact (hloopRev loop).symm

theorem ons_matrixLoopSum_two_bucket
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (n : ℕ)
    (hboth :
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r,
        ons_loopWeight M loop) = 0)
    (hsymm :
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
        ons_loopWeight M loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e),
          ons_loopWeight M loop) :
    (∑ loop : Fin (n + 1) → E, ons_loopWeight M loop) =
      2 * ons_matrixBucketE M e r n +
        ons_matrixBucketN M e r n := by
  let P : (Fin (n + 1) → E) → Prop := fun loop ↦ ∃ i, loop i = e
  let Q : (Fin (n + 1) → E) → Prop := fun loop ↦ ∃ j, loop j = r
  have hsplit := ons_sum_split_by_two P Q (fun loop ↦ ons_loopWeight M loop)
  have hbothset :
      Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = e) ∧ ∃ j, loop j = r) =
        ons_loopSetBoth (n := n + 1) e r := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ons_mem_loopSetBoth]
  rw [← hbothset] at hboth
  have hset :
      Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e) =
        Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            ¬ (∃ i, loop i = e) ∧ ∃ j, loop j = r) := by
    ext loop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hset] at hsymm
  simp only [P, Q] at hsplit
  unfold ons_matrixBucketE ons_matrixBucketN
  linear_combination hsplit + hboth - hsymm


theorem ons_detWalkRoot_matrix_delete_pair
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (e r : E) (her : e ≠ r)
    (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ x y, ‖M x y‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹)
    (hcard : (Fintype.card E : ℝ) * q < 1)
    (hboth : ∀ n : ℕ,
      (∑ loop ∈ ons_loopSetBoth (n := n + 1) e r,
        ons_loopWeight M loop) = 0)
    (hsymm : ∀ n : ℕ,
      (∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r),
        ons_loopWeight M loop) =
        ∑ loop ∈ Finset.univ.filter
          (fun loop : Fin (n + 1) → E ↦
            (∃ i, loop i = r) ∧ ¬ ∃ j, loop j = e),
          ons_loopWeight M loop) :
    ons_detWalkRoot M =
      ons_detWalkRoot
          (ons_maskMatrix ({e, r} : Finset E) M) *
        (1 - ∑' s, ons_firstReturnWeight M e r s) := by
  let pair : Finset E := {e, r}
  have hfirst :
      Summable (fun s ↦ ‖ons_firstReturnWeight M e r s‖) ∧
      (∑' s, ‖ons_firstReturnWeight M e r s‖) < 1 :=
    ons_firstReturnWeight_small M e r q hq hentry hsmall
  have hB : Summable fun n : ℕ ↦
      ons_matrixBucketE M e r n / ((n : ℂ) + 1) := by
    simpa only [ons_matrixBucketE, not_exists] using
      ons_summable_loopBucketSeries M e r her hfirst.1 hfirst.2
  have hN : Summable fun n : ℕ ↦
      ons_matrixBucketN M e r n / ((n : ℂ) + 1) := by
    let P : (n : ℕ) → (Fin (n + 1) → E) → Prop :=
      fun _ loop ↦ ¬ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r
    have hs := ons_summable_filteredLoopSeries M q hq hentry hcard P
    simpa only [ons_matrixBucketN, P] using hs
  have hseries :
      (∑' n : ℕ,
        (∑ loop : Fin (n + 1) → E,
          ons_loopWeight M loop) / ((n : ℂ) + 1)) =
      2 * (∑' n : ℕ,
        ons_matrixBucketE M e r n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_matrixBucketN M e r n / ((n : ℂ) + 1)) := by
    rw [tsum_congr (fun n : ℕ ↦ congrArg (· / ((n : ℂ) + 1))
      (ons_matrixLoopSum_two_bucket M e r n (hboth n) (hsymm n)))]
    have heq : (fun n : ℕ ↦
        (2 * ons_matrixBucketE M e r n +
          ons_matrixBucketN M e r n) / ((n : ℂ) + 1)) =
        (fun n : ℕ ↦ 2 *
          (ons_matrixBucketE M e r n / ((n : ℂ) + 1)) +
          ons_matrixBucketN M e r n / ((n : ℂ) + 1)) := by
      funext n
      ring
    rw [heq, (hB.mul_left 2).tsum_add hN, tsum_mul_left]
  have hlam :
      Complex.exp (-(∑' n : ℕ,
        ons_matrixBucketE M e r n / ((n : ℂ) + 1))) =
      1 - ∑' s, ons_firstReturnWeight M e r s := by
    let z := ∑' s, ons_firstReturnWeight M e r s
    have hz : ‖z‖ < 1 :=
      lt_of_le_of_lt (norm_tsum_le_tsum_norm hfirst.1) hfirst.2
    have hgeom := ons_loopBucketSeries_eq_geometric
      M e r her hfirst.1 hfirst.2
    rw [show (∑' n : ℕ,
        ons_matrixBucketE M e r n / ((n : ℂ) + 1)) =
        ∑' k : ℕ, z ^ (k + 1) / (k + 1) by
      simpa only [ons_matrixBucketE, not_exists, z] using hgeom]
    exact ons_lemma4_exp hz
  have hNroot :
      Complex.exp (-(∑' n : ℕ,
        ons_matrixBucketN M e r n / ((n : ℂ) + 1)) / 2) =
      ons_detWalkRoot (ons_maskMatrix pair M) := by
    unfold ons_detWalkRoot
    apply congrArg Complex.exp
    congr 1
    apply congrArg Neg.neg
    apply tsum_congr
    intro n
    apply congrArg (· / ((n : ℂ) + 1))
    have hsum := ons_loopSum_maskMatrix (n := n + 1) pair M
    have hset :
        Finset.univ.filter
            (fun loop : Fin (n + 1) → E ↦
              ¬ ∃ k, loop k ∈ pair) =
          Finset.univ.filter
            (fun loop : Fin (n + 1) → E ↦
              ¬ (∃ i, loop i = e) ∧ ¬ ∃ j, loop j = r) := by
      ext loop
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        pair, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset] at hsum
    simpa only [ons_loopWeight, ons_matrixBucketN] using hsum.symm
  change Complex.exp (-(∑' n : ℕ,
      (∑ loop : Fin (n + 1) → E,
        ∏ k : Fin (n + 1), M (loop k) (loop (k + 1))) /
          ((n : ℂ) + 1)) / 2) =
    ons_detWalkRoot (ons_maskMatrix pair M) *
      (1 - ∑' s, ons_firstReturnWeight M e r s)
  simp only [ons_loopWeight] at hseries
  rw [hseries]
  rw [show -(2 * (∑' n : ℕ,
        ons_matrixBucketE M e r n / ((n : ℂ) + 1)) +
      (∑' n : ℕ,
        ons_matrixBucketN M e r n / ((n : ℂ) + 1))) / 2 =
      (-(∑' n : ℕ,
        ons_matrixBucketN M e r n / ((n : ℂ) + 1)) / 2) +
      (-(∑' n : ℕ,
        ons_matrixBucketE M e r n / ((n : ℂ) + 1))) by ring,
    Complex.exp_add, hNroot, hlam]



theorem ons_detWalkRoot_norm_sub_one_lt_one
    {E : Type*} [Fintype E] [DecidableEq E]
    (M : Matrix E E ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ x y, ‖M x y‖ ≤ q)
    (hcard : (Fintype.card E : ℝ) * q < 1)
    (hgeom : (∑' n : ℕ,
      ((Fintype.card E : ℝ) * q) ^ (n + 1)) < 1) :
    ‖ons_detWalkRoot M - 1‖ < 1 := by
  let rho : ℝ := (Fintype.card E : ℝ) * q
  let term : ℕ → ℂ := fun n ↦
    (∑ loop : Fin (n + 1) → E,
      ons_loopWeight M loop) / ((n : ℂ) + 1)
  have hrho0 : 0 ≤ rho := mul_nonneg (by positivity) hq
  have hgeomSummable : Summable fun n : ℕ ↦ rho ^ (n + 1) := by
    have hrhoNorm : ‖rho‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hrho0]
      exact hcard
    exact (summable_nat_add_iff 1).2
      (summable_geometric_of_norm_lt_one hrhoNorm)
  have htermNorm : ∀ n, ‖term n‖ ≤ rho ^ (n + 1) := by
    intro n
    calc
      ‖term n‖ =
          ‖∑ loop : Fin (n + 1) → E,
            ons_loopWeight M loop‖ / (n + 1 : ℝ) := by
        unfold term
        rw [norm_div]
        congr 1
        rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by norm_num,
          norm_natCast]
        norm_num
      _ ≤ ‖∑ loop : Fin (n + 1) → E,
          ons_loopWeight M loop‖ := by
        apply div_le_self (norm_nonneg _)
        norm_num
      _ ≤ rho ^ (n + 1) := by
        simpa only [rho, Finset.filter_true]
          using norm_filtered_loopSum_le M q hq hentry n
            (fun _ : Fin (n + 1) → E ↦ True)
  have hnormSummable : Summable fun n ↦ ‖term n‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _)
      htermNorm hgeomSummable
  have hsumNorm : ‖∑' n, term n‖ < 1 := by
    calc
      ‖∑' n, term n‖ ≤ ∑' n, ‖term n‖ :=
        norm_tsum_le_tsum_norm hnormSummable
      _ ≤ ∑' n, rho ^ (n + 1) :=
        Summable.tsum_le_tsum htermNorm hnormSummable hgeomSummable
      _ < 1 := by simpa only [rho] using hgeom
  let z : ℂ := -(∑' n, term n) / 2
  have hz : ‖z‖ < 1 / 2 := by
    dsimp only [z]
    rw [norm_div, norm_neg]
    norm_num
    nlinarith
  have hzle : ‖z‖ ≤ 1 := le_of_lt (hz.trans_le (by norm_num))
  have hexp := Complex.norm_exp_sub_one_le hzle
  change ‖Complex.exp z - 1‖ < 1
  exact hexp.trans_lt (by nlinarith)

theorem ons_geom_sum_lt_one_of_Sherman_small
    {E : Type*} [Fintype E] [Nonempty E]
    (q : ℝ) (hq : 0 ≤ q)
    (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
    (∑' n : ℕ, ((Fintype.card E : ℝ) * q) ^ (n + 1)) < 1 := by
  let C : ℝ := Fintype.card E
  let rho : ℝ := C * q
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact_mod_cast Fintype.card_pos
  have hden : 0 < 2 * C ^ 2 := by positivity
  have hqbound : q * (2 * C ^ 2) < 1 := by
    rw [inv_eq_one_div] at hsmall
    exact (lt_div_iff₀ hden).mp hsmall
  have hrho0 : 0 ≤ rho := mul_nonneg (by positivity) hq
  have hrhoHalf : rho < 1 / 2 := by
    dsimp only [rho]
    nlinarith
  have hrhoOne : rho < 1 := hrhoHalf.trans (by norm_num)
  have hsum : (∑' n : ℕ, rho ^ (n + 1)) =
      (1 - rho)⁻¹ * rho := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hrho0 hrhoOne]
  rw [show (Fintype.card E : ℝ) * q = rho from rfl, hsum,
    inv_mul_eq_div]
  exact (div_lt_one (by nlinarith : 0 < 1 - rho)).2 (by nlinarith)

theorem ons_eq_of_sq_eq_sq_of_norm_sub_one_lt_one
    (x y : ℂ) (hsq : x ^ 2 = y ^ 2)
    (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    x = y := by
  have hfac : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfac with hxy | hsum
  · exact sub_eq_zero.mp hxy
  · exfalso
    have hnorm : ‖(x - 1) + (y - 1)‖ < 2 :=
      (norm_add_le _ _).trans_lt (by nlinarith)
    have heq : (x - 1) + (y - 1) = -2 := by
      linear_combination hsum
    rw [heq] at hnorm
    norm_num at hnorm



theorem ons_detWalkRoot_eq_of_det_eq_of_small
    {E F : Type*}
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (M : Matrix E E ℂ) (N : Matrix F F ℂ)
    (qM qN : ℝ) (hqM : 0 ≤ qM) (hqN : 0 ≤ qN)
    (hentryM : ∀ x y, ‖M x y‖ ≤ qM)
    (hentryN : ∀ x y, ‖N x y‖ ≤ qN)
    (hcardM : (Fintype.card E : ℝ) * qM < 1)
    (hcardN : (Fintype.card F : ℝ) * qN < 1)
    (hgeomM : (∑' n : ℕ,
      ((Fintype.card E : ℝ) * qM) ^ (n + 1)) < 1)
    (hgeomN : (∑' n : ℕ,
      ((Fintype.card F : ℝ) * qN) ^ (n + 1)) < 1)
    (hdet : (1 - M).det = (1 - N).det) :
    ons_detWalkRoot M = ons_detWalkRoot N := by
  have hspecM := ons_spectral_lt_one_of_entry
    M qM hqM hentryM hcardM
  have hspecN := ons_spectral_lt_one_of_entry
    N qN hqN hentryN hcardN
  apply ons_eq_of_sq_eq_sq_of_norm_sub_one_lt_one
  · rw [ons_detWalkRoot_sq M hspecM,
      ons_detWalkRoot_sq N hspecN, hdet]
  · exact ons_detWalkRoot_norm_sub_one_lt_one
      M qM hqM hentryM hcardM hgeomM
  · exact ons_detWalkRoot_norm_sub_one_lt_one
      N qN hqN hentryN hcardN hgeomN

end StatMech.Onsager
