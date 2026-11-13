/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheZeroPhaseCancellation

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheL_add_M {c : Real} {z : Complex} (hz : z ≠ 1) :
    sixVertexBetheL c z + sixVertexBetheM c z = 2 - c ^ 2 := by
  unfold sixVertexBetheL sixVertexBetheM
  push_cast
  field_simp [sub_ne_zero.mpr (Ne.symm hz)]
  ring

theorem sixVertexBetheL_mul_one_sub_pow {c : Real} {z : Complex}
    (hz : z ≠ 1) (N : Nat) :
    sixVertexBetheL c z * (1 - z ^ N) =
      (1 - z ^ N) + (c : Complex) ^ 2 * z *
        ∑ k ∈ Finset.range N, z ^ k := by
  have hgeom := geom_sum_mul_neg z N
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hquot :
      (1 - z ^ N) / (1 - z) = ∑ k ∈ Finset.range N, z ^ k := by
    apply (div_eq_iff hden).2
    exact hgeom.symm
  unfold sixVertexBetheL
  rw [show (1 + (c : Complex) ^ 2 * z / (1 - z)) * (1 - z ^ N) =
      (1 - z ^ N) + (c : Complex) ^ 2 * z *
        ((1 - z ^ N) / (1 - z)) by field_simp [hden] <;> ring]
  rw [hquot]

theorem sixVertexBetheM_mul_one_sub_pow {c : Real} {z : Complex}
    (hz : z ≠ 1) (N : Nat) :
    sixVertexBetheM c z * (1 - z ^ N) =
      (1 - z ^ N) - (c : Complex) ^ 2 *
        ∑ k ∈ Finset.range N, z ^ k := by
  have hgeom := geom_sum_mul_neg z N
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hquot :
      (1 - z ^ N) / (1 - z) = ∑ k ∈ Finset.range N, z ^ k := by
    apply (div_eq_iff hden).2
    exact hgeom.symm
  unfold sixVertexBetheM
  rw [show (1 - (c : Complex) ^ 2 / (1 - z)) * (1 - z ^ N) =
      (1 - z ^ N) - (c : Complex) ^ 2 *
        ((1 - z ^ N) / (1 - z)) by field_simp [hden] <;> ring]
  rw [hquot]

theorem sixVertexBetheL_phase_mul_one_sub_pow_tendsto
    (c : Real) (N : Nat) :
    Tendsto (fun eps : Real =>
      sixVertexBetheL c (sixVertexBethePhase eps) *
        (1 - sixVertexBethePhase eps ^ N))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * N)) := by
  let F : Real → Complex := fun eps =>
    (1 - sixVertexBethePhase eps ^ N) + (c : Complex) ^ 2 *
      sixVertexBethePhase eps *
        ∑ k ∈ Finset.range N, sixVertexBethePhase eps ^ k
  have hF : Continuous F := by
    unfold F sixVertexBethePhase
    fun_prop
  have hlim : Tendsto F
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * N)) := by
    have h : Tendsto F
        (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
        (nhds (F 0)) :=
      hF.continuousAt.mono_left inf_le_left
    convert h using 1
    simp [F, sixVertexBethePhase]
  apply hlim.congr'
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  filter_upwards [hne, mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)] with eps hneps heps
  rw [sixVertexBetheL_mul_one_sub_pow
    (sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero heps hneps)]

theorem sixVertexBetheM_phase_mul_one_sub_pow_tendsto
    (c : Real) (N : Nat) :
    Tendsto (fun eps : Real =>
      sixVertexBetheM c (sixVertexBethePhase eps) *
        (1 - sixVertexBethePhase eps ^ N))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (-((c : Complex) ^ 2 * N))) := by
  let F : Real → Complex := fun eps =>
    (1 - sixVertexBethePhase eps ^ N) - (c : Complex) ^ 2 *
      ∑ k ∈ Finset.range N, sixVertexBethePhase eps ^ k
  have hF : Continuous F := by
    unfold F sixVertexBethePhase
    fun_prop
  have hlim : Tendsto F
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (-((c : Complex) ^ 2 * N))) := by
    have h : Tendsto F
        (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
        (nhds (F 0)) :=
      hF.continuousAt.mono_left inf_le_left
    convert h using 1
    simp [F, sixVertexBethePhase]
  apply hlim.congr'
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  filter_upwards [hne, mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)] with eps hneps heps
  rw [sixVertexBetheM_mul_one_sub_pow
    (sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero heps hneps)]



theorem sixVertexTheta_zero_exp_eq_neg_L_div_M
    {c : Real} (hc : 2 < c) {y : Real}
    (hy : sixVertexBethePhase y ≠ 1) :
    Complex.exp (Complex.I * sixVertexTheta c 0 y) =
      -sixVertexBetheL c (sixVertexBethePhase y) /
        sixVertexBetheM c (sixVertexBethePhase y) := by
  let z := sixVertexBethePhase y
  have hpair := sixVertexBethePairFactor_exchange hc y 0
  have hden : sixVertexBethePairFactor c 1 z ≠ 0 := by
    simpa [z, sixVertexBethePhase] using
      sixVertexBethePairFactor_phase_ne_zero hc 0 y
  have hexp : Complex.exp (Complex.I * sixVertexTheta c 0 y) =
      sixVertexBethePairFactor c z 1 /
        sixVertexBethePairFactor c 1 z := by
    apply (eq_div_iff hden).2
    simpa [z, sixVertexBethePhase, sixVertexTheta_antisymm c y 0] using hpair
  rw [hexp]
  have hM := sixVertexBetheM_phase_ne_zero hc y
  apply (div_eq_div_iff hden hM).2
  unfold sixVertexBethePairFactor sixVertexBetheL sixVertexBetheM
    sixVertexDelta
  dsimp [z]
  push_cast
  field_simp [sub_ne_zero.mpr (Ne.symm hy)]
  ring



theorem SixVertexSatisfiesMultiplicativeBetheEquations.puncturedLProduct_eq_MProduct
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheL c (sixVertexBethePhase (p j))) =
      ∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j)) := by
  let S : Complex := ∑ j, sixVertexTheta c (p ell) (p j)
  let s : Complex := (-1 : Complex) ^ n
  have hbethe := hp ell
  have hbethe' : (1 : Complex) = s * Complex.exp (-Complex.I * S) := by
    simpa [S, s, hell] using hbethe
  have hexpcancel :
      Complex.exp (-Complex.I * S) * Complex.exp (Complex.I * S) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hsignsq : s * s = 1 := by
    dsimp [s]
    rw [← mul_pow]
    norm_num
  have hpositive : Complex.exp (Complex.I * S) = s := by
    calc
      Complex.exp (Complex.I * S) = 1 * Complex.exp (Complex.I * S) := by
        rw [one_mul]
      _ = (s * Complex.exp (-Complex.I * S)) *
          Complex.exp (Complex.I * S) := by rw [← hbethe']
      _ = s := by rw [mul_assoc, hexpcancel, mul_one]
  have hphaseProduct :
      (∏ j ∈ (Finset.univ.erase ell),
        Complex.exp (Complex.I * sixVertexTheta c (p ell) (p j))) = s := by
    rw [← Complex.exp_sum]
    have hsum :
        (∑ j ∈ (Finset.univ.erase ell),
          Complex.I * sixVertexTheta c (p ell) (p j)) = Complex.I * S := by
      rw [← Finset.mul_sum]
      congr 1
      have herase := Finset.sum_erase_add Finset.univ
        (fun j => (sixVertexTheta c (p ell) (p j) : Complex))
        (Finset.mem_univ ell)
      dsimp [S]
      simpa using herase
    rw [hsum, hpositive]
  have hproduct :
      s * (∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j))) =
      s * (∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheL c (sixVertexBethePhase (p j))) := by
    calc
      s * (∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheM c (sixVertexBethePhase (p j))) =
        (∏ j ∈ (Finset.univ.erase ell),
          Complex.exp (Complex.I * sixVertexTheta c (p ell) (p j))) *
          (∏ j ∈ (Finset.univ.erase ell),
            sixVertexBetheM c (sixVertexBethePhase (p j))) := by
              rw [hphaseProduct]
      _ = ∏ j ∈ (Finset.univ.erase ell),
          (Complex.exp (Complex.I * sixVertexTheta c (p ell) (p j)) *
            sixVertexBetheM c (sixVertexBethePhase (p j))) := by
              rw [Finset.prod_mul_distrib]
      _ = ∏ j ∈ (Finset.univ.erase ell),
          -sixVertexBetheL c (sixVertexBethePhase (p j)) := by
              apply Finset.prod_congr rfl
              intro j hj
              have hjell : j ≠ ell := (Finset.mem_erase.mp hj).1
              rw [hell]
              exact (eq_div_iff (sixVertexBetheM_phase_ne_zero hc (p j))).mp
                (sixVertexTheta_zero_exp_eq_neg_L_div_M hc
                  (hother j hjell))
      _ = s * (∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheL c (sixVertexBethePhase (p j))) := by
              rw [Finset.prod_neg]
              rw [Finset.card_erase_of_mem (Finset.mem_univ ell),
                Finset.card_univ, Fintype.card_fin]
              simp [s]
  exact (mul_left_cancel₀ (by dsimp [s]; exact pow_ne_zero _ (by norm_num))
    hproduct).symm




theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedMonomial_shift_sum
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (eps : Real) (x : Fin (n + 1) → Int) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
          sigma (sixVertexBetheShiftCoordinates N x)) =
      ∑ sigma : Equiv.Perm (Fin (n + 1)),
        (sixVertexBethePhase (p (sigma (Fin.last n))) /
          sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps (sigma (Fin.last n)))) ^ N *
        sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
          sigma x := by
  let r : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  let q := sixVertexBethePerturbRoot p ell eps
  let F : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    sixVertexBetheAmplitude c p sigma *
      sixVertexBetheIntMonomial q sigma
        (sixVertexBetheShiftCoordinates N x)
  calc
    (∑ sigma, sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntMonomial q sigma
          (sixVertexBetheShiftCoordinates N x)) =
      ∑ sigma, F (sigma * r.symm) := by
        change (∑ sigma, F sigma) = _
        simpa using (Equiv.sum_comp (Equiv.mulRight r.symm) F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      let tau := sigma * r.symm
      have htau : tau * r = sigma := by
        dsimp [tau]
        change sigma * r⁻¹ * r = sigma
        rw [mul_assoc, inv_mul_cancel, mul_one]
      have hslot : tau 0 = sigma (Fin.last n) := by
        dsimp [tau, r, Equiv.Perm.mul_def]
        rw [finRotate_symm_apply]
        congr 1
        apply Fin.ext
        simp
      have hamp := hp.amplitude_rotate hc tau
      rw [htau] at hamp
      have hmono := sixVertexBetheIntMonomial_rotate
        (N := N) q tau x
      rw [htau] at hmono
      dsimp [F]
      rw [show sigma * r.symm = tau by rfl]
      rw [hmono, ← hslot]
      have hratio :
          (sixVertexBethePhase (p (tau 0)) /
              sixVertexBethePhase (q (tau 0))) ^ N *
              sixVertexBetheAmplitude c p sigma *
              (sixVertexBethePhase (q (tau 0)) ^ N *
                sixVertexBetheIntMonomial q tau
                  (sixVertexBetheShiftCoordinates N x)) =
            (sixVertexBethePhase (p (tau 0)) ^ N *
              sixVertexBetheAmplitude c p sigma) *
                sixVertexBetheIntMonomial q tau
                  (sixVertexBetheShiftCoordinates N x) := by
        rw [div_pow]
        have hqpow : sixVertexBethePhase (q (tau 0)) ^ N ≠ 0 :=
          pow_ne_zero _ (Complex.exp_ne_zero _)
        calc
          _ = (sixVertexBethePhase (p (tau 0)) ^ N *
                sixVertexBetheAmplitude c p sigma *
                sixVertexBetheIntMonomial q tau
                  (sixVertexBetheShiftCoordinates N x)) *
              (sixVertexBethePhase (q (tau 0)) ^ N /
                sixVertexBethePhase (q (tau 0)) ^ N) := by ring
          _ = _ := by rw [div_self hqpow, mul_one]
      rw [hratio, hamp]

def sixVertexBethePerturbedConstantWordTotal
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) (eps : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (n + 1)), (
    sixVertexBethePerturbedWordTerm N c p ell eps x ∅ sigma +
      sixVertexBethePerturbedWordTerm N c p ell eps x Finset.univ sigma)

theorem sixVertexBethePerturbedMProduct_eq
    {n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) :
    (∏ j, sixVertexBetheM c (sixVertexBethePhase
      (sixVertexBethePerturbRoot p ell eps j))) =
      sixVertexBetheM c (sixVertexBethePhase eps) *
        ∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheM c (sixVertexBethePhase (p j)) := by
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j => sixVertexBetheM c (sixVertexBethePhase
      (sixVertexBethePerturbRoot p ell eps j))) (Finset.mem_univ ell)]
  rw [sixVertexBethePerturbRoot_same]
  have herase :
      (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c
        (sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j))) =
      ∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [sixVertexBethePerturbRoot_ne p ell j (Finset.mem_erase.mp hj).1]
  rw [herase]
  ring

theorem sixVertexBethePerturbedLProduct_eq
    {n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real) :
    (∏ j, sixVertexBetheL c (sixVertexBethePhase
      (sixVertexBethePerturbRoot p ell eps j))) =
      sixVertexBetheL c (sixVertexBethePhase eps) *
        ∏ j ∈ (Finset.univ.erase ell),
          sixVertexBetheL c (sixVertexBethePhase (p j)) := by
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j => sixVertexBetheL c (sixVertexBethePhase
      (sixVertexBethePerturbRoot p ell eps j))) (Finset.mem_univ ell)]
  rw [sixVertexBethePerturbRoot_same]
  have herase :
      (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheL c
        (sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j))) =
      ∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheL c (sixVertexBethePhase (p j)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [sixVertexBethePerturbRoot_ne p ell j (Finset.mem_erase.mp hj).1]
  rw [herase]
  ring

theorem sixVertexBethePerturbedBoundaryRatio_sum
    {n : Nat} {N : Nat} (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (hell : p ell = 0) (eps : Real)
    (F : Equiv.Perm (Fin (n + 1)) → Complex) :
    (∑ sigma,
      (sixVertexBethePhase (p (sigma (Fin.last n))) /
        sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps
          (sigma (Fin.last n)))) ^ N * F sigma) =
      (∑ sigma, F sigma) +
        (sixVertexBethePhase eps ^ (-(N : Int)) - 1) *
          ∑ sigma with sigma (Fin.last n) = ell, F sigma := by
  calc
    _ = ∑ sigma, (F sigma +
        (sixVertexBethePhase eps ^ (-(N : Int)) - 1) *
          (if sigma (Fin.last n) = ell then F sigma else 0)) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      by_cases hslot : sigma (Fin.last n) = ell
      · rw [if_pos hslot, hslot, hell]
        simp only [sixVertexBethePerturbRoot_same, sixVertexBethePhase,
          Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div, one_pow]
        rw [zpow_neg, inv_pow, zpow_natCast]
        ring
      · rw [if_neg hslot,
          sixVertexBethePerturbRoot_ne p ell _ hslot]
        have hz : sixVertexBethePhase (p (sigma (Fin.last n))) ≠ 0 :=
          Complex.exp_ne_zero _
        rw [div_self hz, one_pow, one_mul]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      rw [← Finset.sum_filter]


theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_eq
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 1) → Int) (eps : Real) :
    sixVertexBethePerturbedConstantWordTotal N c p ell x eps =
      (∏ j ∈ (Finset.univ.erase ell),
        sixVertexBetheM c (sixVertexBethePhase (p j))) *
      ((sixVertexBetheM c (sixVertexBethePhase eps) +
          sixVertexBetheL c (sixVertexBethePhase eps)) *
        (∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
            sigma x) +
        sixVertexBetheL c (sixVertexBethePhase eps) *
          (sixVertexBethePhase eps ^ (-(N : Int)) - 1) *
          ∑ sigma with sigma (Fin.last n) = ell,
            sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial
                (sixVertexBethePerturbRoot p ell eps) sigma x) := by
  let q := sixVertexBethePerturbRoot p ell eps
  let MP := ∏ j ∈ (Finset.univ.erase ell),
    sixVertexBetheM c (sixVertexBethePhase (p j))
  let W : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    sixVertexBetheAmplitude c p sigma *
      sixVertexBetheIntMonomial q sigma x
  unfold sixVertexBethePerturbedConstantWordTotal
    sixVertexBethePerturbedWordTerm
  simp only [sixVertexBetheWordCoefficient_empty,
    sixVertexBetheWordCoefficient_univ,
    sixVertexBetheWordMonomial_empty,
    sixVertexBetheWordMonomial_univ]
  have hM (sigma : Equiv.Perm (Fin (n + 1))) :
      (∏ i, sixVertexBetheM c (sixVertexBethePhase (q (sigma i)))) =
        sixVertexBetheM c (sixVertexBethePhase eps) * MP := by
    calc
      _ = ∏ i, sixVertexBetheM c (sixVertexBethePhase (q i)) :=
        Equiv.prod_comp sigma _
      _ = _ := by
        simpa only [q, MP] using
          sixVertexBethePerturbedMProduct_eq c p ell eps
  have hL (sigma : Equiv.Perm (Fin (n + 1))) :
      (∏ i, sixVertexBetheL c (sixVertexBethePhase (q (sigma i)))) =
        sixVertexBetheL c (sixVertexBethePhase eps) * MP := by
    calc
      _ = ∏ i, sixVertexBetheL c (sixVertexBethePhase (q i)) :=
        Equiv.prod_comp sigma _
      _ = sixVertexBetheL c (sixVertexBethePhase eps) *
          ∏ j ∈ (Finset.univ.erase ell),
            sixVertexBetheL c (sixVertexBethePhase (p j)) := by
          simpa only [q] using sixVertexBethePerturbedLProduct_eq c p ell eps
      _ = _ := by
        rw [hp.puncturedLProduct_eq_MProduct hc p ell hell hother]
  change (∑ sigma, (
      sixVertexBetheAmplitude c p sigma *
          (∏ i, sixVertexBetheM c (sixVertexBethePhase (q (sigma i)))) *
            sixVertexBetheIntMonomial q sigma x +
      sixVertexBetheAmplitude c p sigma *
          (∏ i, sixVertexBetheL c (sixVertexBethePhase (q (sigma i)))) *
            sixVertexBetheIntMonomial q sigma
              (sixVertexBetheShiftCoordinates N x))) = _
  simp_rw [hM, hL]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ sigma, sixVertexBetheAmplitude c p sigma *
          (sixVertexBetheM c (sixVertexBethePhase eps) * MP) *
          sixVertexBetheIntMonomial q sigma x) =
        (sixVertexBetheM c (sixVertexBethePhase eps) * MP) *
          ∑ sigma, sixVertexBetheAmplitude c p sigma *
            sixVertexBetheIntMonomial q sigma x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    ring
  have hsecond :
      (∑ sigma, sixVertexBetheAmplitude c p sigma *
          (sixVertexBetheL c (sixVertexBethePhase eps) * MP) *
          sixVertexBetheIntMonomial q sigma
            (sixVertexBetheShiftCoordinates N x)) =
        (sixVertexBetheL c (sixVertexBethePhase eps) * MP) *
          ∑ sigma, sixVertexBetheAmplitude c p sigma *
            sixVertexBetheIntMonomial q sigma
              (sixVertexBetheShiftCoordinates N x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    ring
  rw [hfirst, hsecond]
  have hshift := hp.perturbedMonomial_shift_sum hc p ell eps x
  rw [hshift]
  let B : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial q sigma x
  have hratio := sixVertexBethePerturbedBoundaryRatio_sum
    (N := N) p ell hell eps B
  dsimp only [B] at hratio
  have hratio' :
      (∑ sigma,
        (sixVertexBethePhase (p (sigma (Fin.last n))) /
          sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps
            (sigma (Fin.last n)))) ^ N *
          sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial q sigma x) =
        (∑ sigma, sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial q sigma x) +
        (sixVertexBethePhase eps ^ (-(N : Int)) - 1) *
          ∑ sigma with sigma (Fin.last n) = ell,
            sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial q sigma x := by
    calc
      _ = ∑ sigma,
          (sixVertexBethePhase (p (sigma (Fin.last n))) /
            sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps
              (sigma (Fin.last n)))) ^ N *
            (sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial q sigma x) := by
                apply Finset.sum_congr rfl
                intro sigma hsigma
                ring
      _ = _ := hratio
  rw [hratio']
  dsimp only [MP, W, q]
  ring

theorem continuous_sixVertexBethePerturbedIntMonomial
    {n : Nat} (p : Fin n → Real) (ell : Fin n)
    (sigma : Equiv.Perm (Fin n)) (x : Fin n → Int) :
    Continuous (fun eps : Real =>
      sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
        sigma x) := by
  unfold sixVertexBetheIntMonomial
  apply continuous_finsetProd
  intro i hi
  let f : Real → Complex := fun eps => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps (sigma i))
  have hf : Continuous f := by
    unfold f sixVertexBethePhase
    exact Complex.continuous_exp.comp
      (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_apply (sigma i)).comp
          (continuous_sixVertexBethePerturbRoot p ell))))
  exact hf.zpow₀ (x i) (fun eps => Or.inl (Complex.exp_ne_zero _))

theorem sixVertexBetheL_phase_mul_zpow_neg_sub_one_tendsto
    (c : Real) (N : Nat) :
    Tendsto (fun eps : Real =>
      sixVertexBetheL c (sixVertexBethePhase eps) *
        (sixVertexBethePhase eps ^ (-(N : Int)) - 1))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * N)) := by
  have hzpow : Tendsto (fun eps : Real =>
      sixVertexBethePhase eps ^ (-(N : Int)))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (1 : Complex)) := by
    have hcont : Continuous (fun eps : Real =>
        sixVertexBethePhase eps ^ (-(N : Int))) := by
      unfold sixVertexBethePhase
      apply Continuous.zpow₀
      · fun_prop
      · exact fun eps => Or.inl (Complex.exp_ne_zero _)
    have h := hcont.continuousAt.mono_left
      (inf_le_left : nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ ≤
        nhds (0 : Real))
    convert h using 1
    simp [sixVertexBethePhase]
  have hprod := (sixVertexBetheL_phase_mul_one_sub_pow_tendsto c N).mul hzpow
  have hprod' : Tendsto (fun eps : Real =>
      sixVertexBetheL c (sixVertexBethePhase eps) *
        (1 - sixVertexBethePhase eps ^ N) *
        sixVertexBethePhase eps ^ (-(N : Int)))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * N)) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [] with eps
  have hz : sixVertexBethePhase eps ≠ 0 := Complex.exp_ne_zero _
  rw [zpow_neg, zpow_natCast]
  field_simp [pow_ne_zero N hz]

theorem continuous_sixVertexBethePerturbedWaveSum
    {n : Nat} (c : Real) (p : Fin n → Real) (ell : Fin n)
    (x : Fin n → Int) :
    Continuous (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin n), sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
          sigma x) := by
  apply continuous_finsetSum
  intro sigma hsigma
  exact continuous_const.mul
    (continuous_sixVertexBethePerturbedIntMonomial p ell sigma x)

theorem continuous_sixVertexBethePerturbedBoundarySum
    {n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (x : Fin (n + 1) → Int) :
    Continuous (fun eps : Real =>
      ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma (Fin.last n) = ell,
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps)
            sigma x) := by
  apply continuous_finsetSum
  intro sigma hsigma
  exact continuous_const.mul
    (continuous_sixVertexBethePerturbedIntMonomial p ell sigma x)



theorem SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_tendsto
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1)
    (x : Fin (n + 1) → Int) :
    Tendsto (sixVertexBethePerturbedConstantWordTotal N c p ell x)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (
        ((2 : Complex) - (c : Complex) ^ 2) *
          (∏ j ∈ (Finset.univ.erase ell),
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          sixVertexCoordinateBetheIntWave c p x +
        (c : Complex) ^ 2 * N *
          (∏ j ∈ (Finset.univ.erase ell),
            sixVertexBetheM c (sixVertexBethePhase (p j))) *
          ∑ sigma with sigma (Fin.last n) = ell,
            sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial p sigma x)) := by
  let MP : Complex := ∏ j ∈ (Finset.univ.erase ell),
    sixVertexBetheM c (sixVertexBethePhase (p j))
  let W : Real → Complex := fun eps =>
    ∑ sigma, sixVertexBetheAmplitude c p sigma *
      sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x
  let B : Real → Complex := fun eps =>
    ∑ sigma with sigma (Fin.last n) = ell,
      sixVertexBetheAmplitude c p sigma *
        sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x
  have hW : Tendsto W
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (sixVertexCoordinateBetheIntWave c p x)) := by
    have h := (continuous_sixVertexBethePerturbedWaveSum c p ell x).continuousAt
      |>.mono_left (inf_le_left : nhdsWithin (0 : Real)
        (Set.singleton (0 : Real))ᶜ ≤ nhds (0 : Real))
    change Tendsto W (nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ) (nhds (W 0)) at h
    have hzero : W 0 = sixVertexCoordinateBetheIntWave c p x := by
      dsimp [W]
      rw [sixVertexBethePerturbRoot_zero p ell hell]
      rfl
    rwa [hzero] at h
  have hB : Tendsto B
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (∑ sigma with sigma (Fin.last n) = ell,
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial p sigma x)) := by
    have h := (continuous_sixVertexBethePerturbedBoundarySum c p ell x).continuousAt
      |>.mono_left (inf_le_left : nhdsWithin (0 : Real)
        (Set.singleton (0 : Real))ᶜ ≤ nhds (0 : Real))
    change Tendsto B (nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ) (nhds (B 0)) at h
    have hzero : B 0 = ∑ sigma with sigma (Fin.last n) = ell,
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntMonomial p sigma x := by
      dsimp [B]
      rw [sixVertexBethePerturbRoot_zero p ell hell]
    rwa [hzero] at h
  have hG := sixVertexBetheL_phase_mul_zpow_neg_sub_one_tendsto c N
  have hnormal : Tendsto (fun eps : Real => MP *
      (((2 : Complex) - (c : Complex) ^ 2) * W eps +
        (sixVertexBetheL c (sixVertexBethePhase eps) *
          (sixVertexBethePhase eps ^ (-(N : Int)) - 1)) * B eps))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (((2 : Complex) - (c : Complex) ^ 2) * MP *
        sixVertexCoordinateBetheIntWave c p x +
        (c : Complex) ^ 2 * N * MP *
          ∑ sigma with sigma (Fin.last n) = ell,
            sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial p sigma x)) := by
    convert tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul hW).add (hG.mul hB)) using 1 <;> ring
  apply hnormal.congr'
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  have hinter : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ∈ Set.Ioo (-Real.pi) Real.pi :=
    mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  filter_upwards [hne, hinter] with eps hneps heps
  rw [hp.perturbedConstantWordTotal_eq hc p ell hell hother x eps]
  have hadd := sixVertexBetheL_add_M (c := c)
    (sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero heps hneps)
  rw [show sixVertexBetheM c (sixVertexBethePhase eps) +
      sixVertexBetheL c (sixVertexBethePhase eps) =
      (2 : Complex) - (c : Complex) ^ 2 by
        rw [add_comm]
        exact hadd]

end

end StatMech.FrontierD
