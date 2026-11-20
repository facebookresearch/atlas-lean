/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheAmplitudeExchange

namespace StatMech.FrontierD

noncomputable section



theorem sum_perm_eq_zero_of_mul_neg {n : ℕ} (τ : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℂ) (hmul : ∀ σ, f (σ * τ) = -f σ) :
    ∑ σ, f σ = 0 := by
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := Equiv.mulRight τ
  have hreindex : (∑ σ, f σ) = ∑ σ, f (σ * τ) := by
    simpa [e] using (Equiv.sum_comp e f).symm
  have hneg : (∑ σ, f (σ * τ)) = -(∑ σ, f σ) := by
    calc
      (∑ σ, f (σ * τ)) = ∑ σ, -f σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hmul σ
      _ = -(∑ σ, f σ) := by rw [Finset.sum_neg_distrib]
  have hself : (∑ σ, f σ) = -(∑ σ, f σ) := hreindex.trans hneg
  linear_combination (1 / 2 : ℂ) * hself



theorem sum_perm_eq_zero_of_swap_neg {n : ℕ} (i j : Fin n)
    (f : Equiv.Perm (Fin n) → ℂ)
    (hswap : ∀ σ, f (σ * Equiv.swap i j) = -f σ) :
    ∑ σ, f σ = 0 := by
  exact sum_perm_eq_zero_of_mul_neg (Equiv.swap i j) f hswap



theorem sixVertexBetheM_mul_L_sub_one {c : ℝ} (hc : 2 < c)
    {z w : ℂ} (hz : z ≠ 1) (hw : w ≠ 1) :
    sixVertexBetheM c z * sixVertexBetheL c w - 1 =
      -((c : ℂ) ^ 2) * sixVertexBethePairFactor c w z /
        ((1 - z) * (1 - w)) := by
  have hcz : (c : ℂ) ^ 2 ≠ 0 := by
    norm_cast
    positivity
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hw' : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  unfold sixVertexBetheM sixVertexBetheL sixVertexBethePairFactor
    sixVertexDelta
  push_cast
  field_simp
  ring



theorem sixVertexBethe_geometricInterval
    (c : ℝ) {z : ℂ} (hz : z ≠ 1) {a b : ℕ} (hab : a < b) :
    z ^ a + (c : ℂ) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  rw [← Finset.Ico_succ_left_eq_Ioo]
  rw [Nat.succ_eq_succ]
  rw [geom_sum_Ico' hz (Nat.succ_le_iff.mpr hab)]
  unfold sixVertexBetheL sixVertexBetheM
  simp only [pow_succ]
  field_simp [sub_ne_zero.mpr (Ne.symm hz)]
  ring




theorem sixVertexBethe_relaxedWordExpansion
    (c : ℝ) {n : ℕ} (z : Fin n → ℂ) (a b : Fin n → ℕ)
    (hz : ∀ k, z k ≠ 1) (hab : ∀ k, a k < b k) :
    (∏ k, ((z k) ^ (a k) + (c : ℂ) ^ 2 *
        (∑ y ∈ Finset.Ioo (a k) (b k), (z k) ^ y) + (z k) ^ (b k))) =
      ∑ w : Finset (Fin n),
        (∏ k ∈ w, sixVertexBetheL c (z k) * (z k) ^ (a k)) *
          ∏ k ∈ wᶜ, sixVertexBetheM c (z k) * (z k) ^ (b k) := by
  calc
    (∏ k, ((z k) ^ (a k) + (c : ℂ) ^ 2 *
        (∑ y ∈ Finset.Ioo (a k) (b k), (z k) ^ y) + (z k) ^ (b k))) =
      ∏ k, (sixVertexBetheL c (z k) * (z k) ^ (a k) +
        sixVertexBetheM c (z k) * (z k) ^ (b k)) := by
      apply Finset.prod_congr rfl
      intro k _
      exact sixVertexBethe_geometricInterval c (hz k) (hab k)
    _ = _ := Fintype.prod_add _ _



def sixVertexBetheIntMonomial {n : ℕ} (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) : ℂ :=
  ∏ k, sixVertexBethePhase (p (σ k)) ^ (x k)



def sixVertexBetheShiftCoordinates {n : ℕ} (N : ℕ)
    (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  Fin.cases (x (Fin.last n) - N) fun i => x i.castSucc

theorem sixVertexBetheIntMonomial_rotate
    {N n : ℕ} (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ) :
    sixVertexBetheIntMonomial p (σ * finRotate (n + 1)) x =
      sixVertexBethePhase (p (σ 0)) ^ N *
        sixVertexBetheIntMonomial p σ
          (sixVertexBetheShiftCoordinates N x) := by
  let z : Fin (n + 1) → ℂ := fun k => sixVertexBethePhase (p (σ k))
  have hz (k : Fin (n + 1)) : z k ≠ 0 := Complex.exp_ne_zero _
  have hrotate :
      (∏ k, z (finRotate (n + 1) k) ^ (x k)) =
        ∏ k, z k ^ (x ((finRotate (n + 1)).symm k)) := by
    simpa using (Equiv.prod_comp (finRotate (n + 1)).symm
      (fun k => z (finRotate (n + 1) k) ^ (x k))).symm
  unfold sixVertexBetheIntMonomial
  change (∏ k, z (finRotate (n + 1) k) ^ (x k)) = _
  rw [hrotate]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [sixVertexBetheShiftCoordinates, Fin.cases_zero, Fin.cases_succ]
  have hr0 : (finRotate (n + 1)).symm 0 = Fin.last n := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hrsucc (i : Fin n) :
      (finRotate (n + 1)).symm i.succ = i.castSucc := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp [Fin.coe_sub_one]
  rw [hr0]
  simp_rw [hrsucc]
  have hpow : z 0 ^ (N : ℤ) * z 0 ^ (x (Fin.last n) - N) =
      z 0 ^ x (Fin.last n) := by
    rw [← zpow_add₀ (hz 0)]
    congr 1
    omega
  change z 0 ^ x (Fin.last n) * ∏ i : Fin n, z i.succ ^ x i.castSucc =
    z 0 ^ N * (z 0 ^ (x (Fin.last n) - N) *
      ∏ i : Fin n, z i.succ ^ x i.castSucc)
  rw [← zpow_natCast, ← mul_assoc, hpow]



theorem SixVertexSatisfiesMultiplicativeBetheEquations.changeVariables
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (f : Equiv.Perm (Fin (n + 1)) → ℂ) (x : Fin (n + 1) → ℤ) :
    ∑ σ, sixVertexBetheAmplitude c p σ * f σ *
        sixVertexBetheIntMonomial p σ x =
      ∑ σ, sixVertexBetheAmplitude c p σ *
        f (σ * finRotate (n + 1)) *
          sixVertexBetheIntMonomial p σ
            (sixVertexBetheShiftCoordinates N x) := by
  let r : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  calc
    (∑ σ, sixVertexBetheAmplitude c p σ * f σ *
        sixVertexBetheIntMonomial p σ x) =
      ∑ σ, sixVertexBetheAmplitude c p (σ * r) * f (σ * r) *
        sixVertexBetheIntMonomial p (σ * r) x := by
      simpa [r] using
        (Equiv.sum_comp (Equiv.mulRight r)
          (fun σ => sixVertexBetheAmplitude c p σ * f σ *
            sixVertexBetheIntMonomial p σ x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [sixVertexBetheIntMonomial_rotate (N := N)]
      calc
        _ = (sixVertexBethePhase (p (σ 0)) ^ N *
              sixVertexBetheAmplitude c p (σ * r)) *
            f (σ * r) * sixVertexBetheIntMonomial p σ
              (sixVertexBetheShiftCoordinates N x) := by ring
        _ = _ := by rw [show r = finRotate (n + 1) by rfl,
          hp.amplitude_rotate hc]


def sixVertexCoordinateBetheIntWave {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) (x : Fin n → ℤ) : ℂ :=
  ∑ σ, sixVertexBetheAmplitude c p σ *
    sixVertexBetheIntMonomial p σ x



def sixVertexBetheWordEdgeFactor {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℂ :=
  if i ∈ w then
    if finRotate (n + 1) i ∈ w then
      sixVertexBetheL c (z (σ (finRotate (n + 1) i)))
    else 1
  else if finRotate (n + 1) i ∈ w then
    sixVertexBetheM c (z (σ i)) *
      sixVertexBetheL c (z (σ (finRotate (n + 1) i))) - 1
  else sixVertexBetheM c (z (σ i))


def sixVertexBetheWordCoefficient {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) : ℂ :=
  ∏ i, sixVertexBetheWordEdgeFactor c z σ w i


def sixVertexBetheWordCoefficientRemainder {n : ℕ} (c : ℝ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1)) : ℂ :=
  ∏ i ∈ Finset.univ.erase a, sixVertexBetheWordEdgeFactor c z σ w i


def sixVertexBetheWordMonomial {n : ℕ} (N : ℕ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℤ) (w : Finset (Fin (n + 1))) : ℂ :=
  ∏ i, if i ∈ w then
    z (σ i) ^ (sixVertexBetheShiftCoordinates N x i)
  else z (σ i) ^ (x i)

@[simp] theorem sixVertexBetheWordCoefficient_empty {n : ℕ}
    (c : ℝ) (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    sixVertexBetheWordCoefficient c z σ ∅ =
      ∏ i, sixVertexBetheM c (z (σ i)) := by
  simp [sixVertexBetheWordCoefficient, sixVertexBetheWordEdgeFactor]

@[simp] theorem sixVertexBetheWordCoefficient_univ {n : ℕ}
    (c : ℝ) (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1))) :
    sixVertexBetheWordCoefficient c z σ Finset.univ =
      ∏ i, sixVertexBetheL c (z (σ i)) := by
  unfold sixVertexBetheWordCoefficient sixVertexBetheWordEdgeFactor
  simp only [Finset.mem_univ, if_true]
  exact Equiv.prod_comp (finRotate (n + 1))
    (fun i => sixVertexBetheL c (z (σ i)))

@[simp] theorem sixVertexBetheWordMonomial_empty {n : ℕ} (N : ℕ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℤ) :
    sixVertexBetheWordMonomial N z σ x ∅ = ∏ i, z (σ i) ^ x i := by
  simp [sixVertexBetheWordMonomial]

@[simp] theorem sixVertexBetheWordMonomial_univ {n : ℕ} (N : ℕ)
    (z : Fin (n + 1) → ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℤ) :
    sixVertexBetheWordMonomial N z σ x Finset.univ =
      ∏ i, z (σ i) ^ (sixVertexBetheShiftCoordinates N x i) := by
  simp [sixVertexBetheWordMonomial]

theorem sixVertexBetheWordCoefficientRemainder_swap_invariant
    {n : ℕ} (c : ℝ) (z : Fin (n + 1) → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Finset (Fin (n + 1)))
    {a b : Fin (n + 1)} (haM : a ∉ w) (hbL : b ∈ w)
    (hab : finRotate (n + 1) a = b) :
    sixVertexBetheWordCoefficientRemainder c z
        (σ * Equiv.swap a b) w a =
      sixVertexBetheWordCoefficientRemainder c z σ w a := by
  unfold sixVertexBetheWordCoefficientRemainder
  apply Finset.prod_congr rfl
  intro k hk
  have hka : k ≠ a := by
    simpa using (Finset.mem_erase.mp hk).1
  by_cases hkw : k ∈ w
  · by_cases hrw : finRotate (n + 1) k ∈ w
    · have hrka : finRotate (n + 1) k ≠ a := fun h => haM (h ▸ hrw)
      have hrkb : finRotate (n + 1) k ≠ b := by
        intro h
        apply hka
        exact (finRotate (n + 1)).injective (h.trans hab.symm)
      unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_true, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hrka hrkb]
    · unfold sixVertexBetheWordEdgeFactor
      rw [if_pos hkw, if_neg hrw, if_pos hkw, if_neg hrw]
  · have hkb : k ≠ b := by
      intro h
      apply hkw
      exact h.symm ▸ hbL
    by_cases hrw : finRotate (n + 1) k ∈ w
    · have hrka : finRotate (n + 1) k ≠ a := fun h => haM (h ▸ hrw)
      have hrkb : finRotate (n + 1) k ≠ b := by
        intro h
        apply hka
        exact (finRotate (n + 1)).injective (h.trans hab.symm)
      unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_false, if_true, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb,
        Equiv.swap_apply_of_ne_of_ne hrka hrkb]
    · unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_false, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

theorem sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
    {n : ℕ} (c : ℝ) (z : Fin (n + 1) → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Finset (Fin (n + 1)))
    {a b : Fin (n + 1)} (haM : a ∉ w) (hbL : b ∈ w)
    (hab : finRotate (n + 1) a = b) :
    sixVertexBetheWordCoefficient c z σ w =
      (sixVertexBetheM c (z (σ a)) *
          sixVertexBetheL c (z (σ b)) - 1) *
        sixVertexBetheWordCoefficientRemainder c z σ w a := by
  unfold sixVertexBetheWordCoefficient
    sixVertexBetheWordCoefficientRemainder
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  unfold sixVertexBetheWordEdgeFactor
  rw [if_neg haM, if_pos (by simpa [hab] using hbL), hab]
  ring

theorem sixVertexBetheWordCoefficientRemainder_adjacent_invariant
    {n : ℕ} (c : ℝ) (z : Fin (n + 1) → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w) :
    sixVertexBetheWordCoefficientRemainder c z
        (σ * Equiv.swap i.castSucc i.succ) w i.castSucc =
      sixVertexBetheWordCoefficientRemainder c z σ w i.castSucc := by
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  have hiMa : a ∉ w := by simpa [a] using hiM
  have hiLb : b ∈ w := by simpa [b] using hiL
  have hab : finRotate (n + 1) a = b := by
    apply Fin.ext
    simp [a, b]
  unfold sixVertexBetheWordCoefficientRemainder
  apply Finset.prod_congr rfl
  intro k hk
  have hka : k ≠ a := by
    simpa [a] using (Finset.mem_erase.mp hk).1
  by_cases hkw : k ∈ w
  · by_cases hrw : finRotate (n + 1) k ∈ w
    · have hrka : finRotate (n + 1) k ≠ a := fun h => hiMa (h ▸ hrw)
      have hrkb : finRotate (n + 1) k ≠ b := by
        intro h
        apply hka
        exact (finRotate (n + 1)).injective (h.trans hab.symm)
      unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_true, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hrka hrkb]
    · unfold sixVertexBetheWordEdgeFactor
      rw [if_pos hkw, if_neg hrw, if_pos hkw, if_neg hrw]
  · have hkb : k ≠ b := by
      intro h
      apply hkw
      exact h.symm ▸ hiLb
    by_cases hrw : finRotate (n + 1) k ∈ w
    · have hrka : finRotate (n + 1) k ≠ a := fun h => hiMa (h ▸ hrw)
      have hrkb : finRotate (n + 1) k ≠ b := by
        intro h
        apply hka
        exact (finRotate (n + 1)).injective (h.trans hab.symm)
      unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_false, if_true, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb,
        Equiv.swap_apply_of_ne_of_ne hrka hrkb]
    · unfold sixVertexBetheWordEdgeFactor
      simp only [hkw, hrw, if_false, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

theorem sixVertexBetheWordCoefficient_eq_ML_mul_remainder
    {n : ℕ} (c : ℝ) (z : Fin (n + 1) → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w) :
    sixVertexBetheWordCoefficient c z σ w =
      (sixVertexBetheM c (z (σ i.castSucc)) *
          sixVertexBetheL c (z (σ i.succ)) - 1) *
        sixVertexBetheWordCoefficientRemainder c z σ w i.castSucc := by
  unfold sixVertexBetheWordCoefficient
    sixVertexBetheWordCoefficientRemainder
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i.castSucc)]
  unfold sixVertexBetheWordEdgeFactor
  rw [if_neg hiM, if_pos (by simpa using hiL)]
  rw [show finRotate (n + 1) i.castSucc = i.succ by
    apply Fin.ext
    simp]
  ring

theorem SixVertexSatisfiesMultiplicativeBetheEquations.intWave_shift
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : Fin (n + 1) → ℤ) :
    sixVertexCoordinateBetheIntWave c p x =
      sixVertexCoordinateBetheIntWave c p
        (sixVertexBetheShiftCoordinates N x) := by
  simpa [sixVertexCoordinateBetheIntWave] using hp.changeVariables hc (fun _ => 1) x



theorem SixVertexSatisfiesMultiplicativeBetheEquations.constantWordContribution
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : Fin (n + 1) → ℤ) :
    (∑ σ, sixVertexBetheAmplitude c p σ *
      (((∏ k, sixVertexBetheL c (sixVertexBethePhase (p (σ k)))) *
          sixVertexBetheIntMonomial p σ
            (sixVertexBetheShiftCoordinates N x)) +
        ((∏ k, sixVertexBetheM c (sixVertexBethePhase (p (σ k)))) *
          sixVertexBetheIntMonomial p σ x))) =
      sixVertexBetheEigenvalueCandidate c p *
        sixVertexCoordinateBetheIntWave c p x := by
  have hL (σ : Equiv.Perm (Fin (n + 1))) :
      (∏ k, sixVertexBetheL c (sixVertexBethePhase (p (σ k)))) =
        ∏ k, sixVertexBetheL c (sixVertexBethePhase (p k)) := by
    exact Equiv.prod_comp σ
      (fun k => sixVertexBetheL c (sixVertexBethePhase (p k)))
  have hM (σ : Equiv.Perm (Fin (n + 1))) :
      (∏ k, sixVertexBetheM c (sixVertexBethePhase (p (σ k)))) =
        ∏ k, sixVertexBetheM c (sixVertexBethePhase (p k)) := by
    exact Equiv.prod_comp σ
      (fun k => sixVertexBetheM c (sixVertexBethePhase (p k)))
  let LP := ∏ k, sixVertexBetheL c (sixVertexBethePhase (p k))
  let MP := ∏ k, sixVertexBetheM c (sixVertexBethePhase (p k))
  calc
    (∑ σ, sixVertexBetheAmplitude c p σ *
      (((∏ k, sixVertexBetheL c (sixVertexBethePhase (p (σ k)))) *
          sixVertexBetheIntMonomial p σ
            (sixVertexBetheShiftCoordinates N x)) +
        ((∏ k, sixVertexBetheM c (sixVertexBethePhase (p (σ k)))) *
          sixVertexBetheIntMonomial p σ x))) =
      LP * (∑ σ, sixVertexBetheAmplitude c p σ *
          sixVertexBetheIntMonomial p σ
            (sixVertexBetheShiftCoordinates N x)) +
        MP * (∑ σ, sixVertexBetheAmplitude c p σ *
          sixVertexBetheIntMonomial p σ x) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro σ _
        rw [hL]
        dsimp [LP]
        ring
      · apply Finset.sum_congr rfl
        intro σ _
        rw [hM]
        dsimp [MP]
        ring
    _ = LP * sixVertexCoordinateBetheIntWave c p
          (sixVertexBetheShiftCoordinates N x) +
        MP * sixVertexCoordinateBetheIntWave c p x := by
      rfl
    _ = LP * sixVertexCoordinateBetheIntWave c p x +
        MP * sixVertexCoordinateBetheIntWave c p x := by
      rw [← hp.intWave_shift hc x]
    _ = _ := by
      unfold sixVertexBetheEigenvalueCandidate
      dsimp [LP, MP]
      ring



theorem sixVertexBetheM_mul_L_sub_one_ne_zero {c : ℝ} (hc : 2 < c)
    {p q : ℝ} (hp : sixVertexBethePhase p ≠ 1)
    (hq : sixVertexBethePhase q ≠ 1) :
    sixVertexBetheM c (sixVertexBethePhase q) *
        sixVertexBetheL c (sixVertexBethePhase p) - 1 ≠ 0 := by
  rw [sixVertexBetheM_mul_L_sub_one hc hq hp]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact neg_ne_zero.mpr (pow_ne_zero 2 (by
        exact_mod_cast (show c ≠ 0 by nlinarith)))
    · exact sixVertexBethePairFactor_phase_ne_zero hc p q
  · exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hq))
      (sub_ne_zero.mpr (Ne.symm hp))



theorem sixVertexTheta_exp_eq_ML_ratio {c : ℝ} (hc : 2 < c)
    {p q : ℝ} (hp : sixVertexBethePhase p ≠ 1)
    (hq : sixVertexBethePhase q ≠ 1) :
    Complex.exp (Complex.I * sixVertexTheta c p q) =
      (sixVertexBetheM c (sixVertexBethePhase p) *
          sixVertexBetheL c (sixVertexBethePhase q) - 1) /
        (sixVertexBetheM c (sixVertexBethePhase q) *
          sixVertexBetheL c (sixVertexBethePhase p) - 1) := by
  have hphase :
      Complex.exp (Complex.I * sixVertexTheta c p q) *
          sixVertexBethePairFactor c (sixVertexBethePhase p)
            (sixVertexBethePhase q) =
        sixVertexBethePairFactor c (sixVertexBethePhase q)
          (sixVertexBethePhase p) := by
    simpa [sixVertexTheta_antisymm c q p] using
      sixVertexBethePairFactor_exchange hc q p
  apply (eq_div_iff
    (sixVertexBetheM_mul_L_sub_one_ne_zero hc hp hq)).2
  rw [sixVertexBetheM_mul_L_sub_one hc hp hq,
    sixVertexBetheM_mul_L_sub_one hc hq hp]
  calc
    Complex.exp (Complex.I * sixVertexTheta c p q) *
        (-((c : ℂ) ^ 2) *
          sixVertexBethePairFactor c (sixVertexBethePhase p)
            (sixVertexBethePhase q) /
          ((1 - sixVertexBethePhase q) *
            (1 - sixVertexBethePhase p))) =
      (-((c : ℂ) ^ 2) /
          ((1 - sixVertexBethePhase q) *
            (1 - sixVertexBethePhase p))) *
        (Complex.exp (Complex.I * sixVertexTheta c p q) *
          sixVertexBethePairFactor c (sixVertexBethePhase p)
            (sixVertexBethePhase q)) := by ring
    _ = (-((c : ℂ) ^ 2) /
          ((1 - sixVertexBethePhase q) *
            (1 - sixVertexBethePhase p))) *
        sixVertexBethePairFactor c (sixVertexBethePhase q)
          (sixVertexBethePhase p) := by rw [hphase]
    _ = -((c : ℂ) ^ 2) *
          sixVertexBethePairFactor c (sixVertexBethePhase q)
            (sixVertexBethePhase p) /
        ((1 - sixVertexBethePhase p) *
          (1 - sixVertexBethePhase q)) := by ring




theorem sixVertexBetheAmplitude_adjacent_ML_cancel
    {c : ℝ} (hc : 2 < c) {n : ℕ} (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (ha : sixVertexBethePhase (p (σ i.castSucc)) ≠ 1)
    (hb : sixVertexBethePhase (p (σ i.succ)) ≠ 1) :
    sixVertexBetheAmplitude c p
          (σ * Equiv.swap i.castSucc i.succ) *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.succ))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.castSucc))) - 1) =
      -sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1) := by
  let θ := sixVertexTheta c (p (σ i.castSucc)) (p (σ i.succ))
  have hswap := sixVertexBetheAmplitude_adjacent_exchange hc p σ i
  have hphase : Complex.exp (Complex.I * θ) *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.succ))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.castSucc))) - 1) =
      sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) *
          sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1 := by
    apply (eq_div_iff
      (sixVertexBetheM_mul_L_sub_one_ne_zero hc ha hb)).mp
    exact sixVertexTheta_exp_eq_ML_ratio hc ha hb
  have hexp : Complex.exp (Complex.I * θ) *
      Complex.exp (-Complex.I * θ) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hamp : sixVertexBetheAmplitude c p
        (σ * Equiv.swap i.castSucc i.succ) =
      -Complex.exp (Complex.I * θ) * sixVertexBetheAmplitude c p σ := by
    calc
      sixVertexBetheAmplitude c p
          (σ * Equiv.swap i.castSucc i.succ) =
          (Complex.exp (Complex.I * θ) *
            Complex.exp (-Complex.I * θ)) *
              sixVertexBetheAmplitude c p
                (σ * Equiv.swap i.castSucc i.succ) := by rw [hexp, one_mul]
      _ = Complex.exp (Complex.I * θ) *
          (Complex.exp (-Complex.I * θ) *
            sixVertexBetheAmplitude c p
              (σ * Equiv.swap i.castSucc i.succ)) := by ring
      _ = Complex.exp (Complex.I * θ) *
          (-sixVertexBetheAmplitude c p σ) := by
            rw [show θ = sixVertexTheta c (p (σ i.castSucc))
              (p (σ i.succ)) by rfl, hswap]
      _ = _ := by ring
  rw [hamp]
  rw [← hphase]
  ring




theorem sum_sixVertexBetheAmplitude_adjacent_ML_eq_zero
    {c : ℝ} (hc : 2 < c) {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin n) (B : Equiv.Perm (Fin (n + 1)) → ℂ)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1)
    (hB : ∀ σ, B (σ * Equiv.swap i.castSucc i.succ) = B σ) :
    ∑ σ, sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1) *
          B σ = 0 := by
  apply sum_perm_eq_zero_of_swap_neg i.castSucc i.succ
  intro σ
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [hB]
  have hlocal := sixVertexBetheAmplitude_adjacent_ML_cancel hc p σ i
    (hphase _) (hphase _)
  calc
    sixVertexBetheAmplitude c p
          (σ * Equiv.swap i.castSucc i.succ) *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.succ))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.castSucc))) - 1) *
          B σ =
      (-sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1)) *
          B σ := by rw [hlocal]
    _ = _ := by ring

theorem sixVertexBetheAmplitude_wordCoefficient_adjacent_cancel
    {c : ℝ} (hc : 2 < c) {n : ℕ} (p : Fin (n + 1) → ℝ)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    sixVertexBetheAmplitude c p
        (σ * Equiv.swap i.castSucc i.succ) *
        sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j))
          (σ * Equiv.swap i.castSucc i.succ) w =
      -(sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w) := by
  let z : Fin (n + 1) → ℂ := fun j => sixVertexBethePhase (p j)
  have hrem := sixVertexBetheWordCoefficientRemainder_adjacent_invariant
    c z σ w i hiM hiL
  rw [sixVertexBetheWordCoefficient_eq_ML_mul_remainder c z _ w i hiM hiL,
    sixVertexBetheWordCoefficient_eq_ML_mul_remainder c z σ w i hiM hiL]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [hrem]
  have hlocal := sixVertexBetheAmplitude_adjacent_ML_cancel hc p σ i
    (hphase _) (hphase _)
  dsimp [z] at hlocal ⊢
  calc
    _ = (sixVertexBetheAmplitude c p
          (σ * Equiv.swap i.castSucc i.succ) *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.succ))) *
          sixVertexBetheL c (sixVertexBethePhase (p (σ i.castSucc))) - 1)) *
        sixVertexBetheWordCoefficientRemainder c
          (fun j => sixVertexBethePhase (p j)) σ w i.castSucc := by ring
    _ = (-sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) *
          sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1)) *
        sixVertexBetheWordCoefficientRemainder c
          (fun j => sixVertexBethePhase (p j)) σ w i.castSucc := by rw [hlocal]
    _ = _ := by ring

theorem sixVertexBetheWordMonomial_adjacent_invariant
    {N n : ℕ} (z : Fin (n + 1) → ℂ)
    (σ : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → ℤ)
    (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w) :
    sixVertexBetheWordMonomial N z
        (σ * Equiv.swap i.castSucc i.succ) x w =
      sixVertexBetheWordMonomial N z σ x w := by
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  let e : Fin (n + 1) → ℤ := fun k =>
    if k ∈ w then sixVertexBetheShiftCoordinates N x k else x k
  have hiMa : a ∉ w := by simpa [a] using hiM
  have hiLb : b ∈ w := by simpa [b] using hiL
  have hshift : sixVertexBetheShiftCoordinates N x b = x a := by
    simp [sixVertexBetheShiftCoordinates, a, b]
  have he (k : Fin (n + 1)) :
      e (Equiv.swap a b k) = e k := by
    by_cases hka : k = a
    · subst k
      simp [e, hiMa, hiLb, hshift]
    · by_cases hkb : k = b
      · subst k
        simp [e, hiMa, hiLb, hshift]
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
  have hfactor (tau : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
      (if k ∈ w then
          z (tau k) ^ sixVertexBetheShiftCoordinates N x k
        else z (tau k) ^ x k) = z (tau k) ^ e k := by
    simp [e]
  unfold sixVertexBetheWordMonomial
  simp_rw [hfactor]
  change (∏ k, z ((σ * Equiv.swap a b) k) ^ e k) =
    ∏ k, z (σ k) ^ e k
  calc
    (∏ k, z ((σ * Equiv.swap a b) k) ^ e k) =
        ∏ k, z ((σ * Equiv.swap a b) (Equiv.swap a b k)) ^
          e (Equiv.swap a b k) := by
      exact (Equiv.prod_comp (Equiv.swap a b)
        (fun k => z ((σ * Equiv.swap a b) k) ^ e k)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k _
      rw [he]
      simp [Equiv.Perm.mul_apply]

theorem sixVertexBetheWordMonomial_boundary_covariant
    {N n : ℕ} (z : Fin (n + 2) → ℂ) (hz : ∀ k, z k ≠ 0)
    (σ : Equiv.Perm (Fin (n + 2))) (x : Fin (n + 2) → ℤ)
    (w : Finset (Fin (n + 2)))
    (haM : Fin.last (n + 1) ∉ w) (hbL : (0 : Fin (n + 2)) ∈ w) :
    z (σ (Fin.last (n + 1))) ^ N *
        sixVertexBetheWordMonomial N z
          (σ * Equiv.swap (Fin.last (n + 1)) 0) x w =
      z (σ 0) ^ N * sixVertexBetheWordMonomial N z σ x w := by
  let a : Fin (n + 2) := Fin.last (n + 1)
  let b : Fin (n + 2) := 0
  let e : Fin (n + 2) → ℤ := fun k =>
    if k ∈ w then sixVertexBetheShiftCoordinates N x k else x k
  let A : Fin (n + 2) → ℂ := fun k =>
    if k = a then z (σ k) ^ N else 1
  let B : Fin (n + 2) → ℂ := fun k =>
    if k = b then z (σ k) ^ N else 1
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hea : e a = x a := by simp [e, haM, a]
  have heb : e b = x a - N := by
    simp [e, hbL, sixVertexBetheShiftCoordinates, a, b]
  have hfactor (tau : Equiv.Perm (Fin (n + 2))) (k : Fin (n + 2)) :
      (if k ∈ w then
          z (tau k) ^ sixVertexBetheShiftCoordinates N x k
        else z (tau k) ^ x k) = z (tau k) ^ e k := by
    simp [e]
  have hmon : sixVertexBetheWordMonomial N z
        (σ * Equiv.swap a b) x w =
      ∏ k, z (σ k) ^ e (Equiv.swap a b k) := by
    unfold sixVertexBetheWordMonomial
    simp_rw [hfactor]
    calc
      (∏ k, z ((σ * Equiv.swap a b) k) ^ e k) =
          ∏ k, z ((σ * Equiv.swap a b) (Equiv.swap a b k)) ^
            e (Equiv.swap a b k) := by
        exact (Equiv.prod_comp (Equiv.swap a b)
          (fun k => z ((σ * Equiv.swap a b) k) ^ e k)).symm
      _ = _ := by
        apply Fintype.prod_congr
        intro k
        simp [Equiv.Perm.mul_apply]
  have hmon' : sixVertexBetheWordMonomial N z σ x w =
      ∏ k, z (σ k) ^ e k := by
    unfold sixVertexBetheWordMonomial
    simp_rw [hfactor]
  have hprodA : (∏ k, A k) = z (σ a) ^ N := by
    rw [Fintype.prod_eq_single a]
    · simp [A]
    · intro k hka
      simp [A, hka]
  have hprodB : (∏ k, B k) = z (σ b) ^ N := by
    rw [Fintype.prod_eq_single b]
    · simp [B]
    · intro k hkb
      simp [B, hkb]
  have hpoint (k : Fin (n + 2)) :
      A k * z (σ k) ^ e (Equiv.swap a b k) =
        B k * z (σ k) ^ e k := by
    by_cases hka : k = a
    · subst k
      simp only [A, B, if_pos, Equiv.swap_apply_left, hea]
      rw [if_neg hab, ← zpow_natCast, ← zpow_add₀ (hz (σ a)), heb]
      simp only [one_mul]
      congr 1
      omega
    · by_cases hkb : k = b
      · subst k
        simp only [A, B, if_pos, Equiv.swap_apply_right, heb]
        rw [if_neg (Ne.symm hab), ← zpow_natCast,
          ← zpow_add₀ (hz (σ b)), hea]
        simp only [one_mul]
        congr 1
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
        simp [A, B, hka, hkb]
  change z (σ a) ^ N * _ = z (σ b) ^ N * _
  rw [hmon, hmon', ← hprodA, ← hprodB]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Fintype.prod_congr _ _ hpoint

theorem sum_sixVertexBetheWordTerm_adjacent_eq_zero
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 1) → ℝ)
    (x : Fin (n + 1) → ℤ) (w : Finset (Fin (n + 1))) (i : Fin n)
    (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    ∑ σ, sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w *
          sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
  apply sum_perm_eq_zero_of_swap_neg i.castSucc i.succ
  intro σ
  rw [sixVertexBetheWordMonomial_adjacent_invariant
    (fun j => sixVertexBethePhase (p j)) σ x w i hiM hiL]
  rw [sixVertexBetheAmplitude_wordCoefficient_adjacent_cancel
    hc p σ w i hiM hiL hphase]
  ring



theorem sixVertexBetheAmplitude_boundary_ML_cancel
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 2) → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (σ : Equiv.Perm (Fin (n + 2)))
    (B : Equiv.Perm (Fin (n + 2)) → ℂ)
    (ha : sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ≠ 1)
    (hb : sixVertexBethePhase (p (σ 0)) ≠ 1)
    (hB : sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N *
        B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 *
          finRotate (n + 2))) =
      sixVertexBethePhase (p (σ 0)) ^ N * B σ) :
    sixVertexBetheAmplitude c p
          (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 *
            finRotate (n + 2))) *
        (sixVertexBetheM c (sixVertexBethePhase (p (σ 0))) *
            sixVertexBetheL c
              (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) - 1) *
          B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 *
            finRotate (n + 2))) =
      -sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c
              (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ 0))) - 1) *
          B σ := by
  let τ : Equiv.Perm (Fin (n + 2)) :=
    (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2)
  let za := sixVertexBethePhase (p (σ (Fin.last (n + 1))))
  let zb := sixVertexBethePhase (p (σ 0))
  let θ := sixVertexTheta c (p (σ (Fin.last (n + 1)))) (p (σ 0))
  let R := sixVertexBetheM c zb * sixVertexBetheL c za - 1
  let O := sixVertexBetheM c za * sixVertexBetheL c zb - 1
  have hamp := hp.amplitude_boundary_exchange hc σ
  change Complex.exp (-Complex.I * θ) * zb ^ N *
      sixVertexBetheAmplitude c p (σ * τ) =
    -(za ^ N * sixVertexBetheAmplitude c p σ) at hamp
  have hphase : Complex.exp (Complex.I * θ) * R = O := by
    apply (eq_div_iff (sixVertexBetheM_mul_L_sub_one_ne_zero hc ha hb)).mp
    exact sixVertexTheta_exp_eq_ML_ratio hc ha hb
  have hexp : Complex.exp (-Complex.I * θ) *
      Complex.exp (Complex.I * θ) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hza : za ^ N ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hzb : zb ^ N ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hs : Complex.exp (-Complex.I * θ) * za ^ N * zb ^ N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hza) hzb
  change sixVertexBetheAmplitude c p (σ * τ) * R * B (σ * τ) =
    -sixVertexBetheAmplitude c p σ * O * B σ
  apply mul_left_cancel₀ hs
  calc
    (Complex.exp (-Complex.I * θ) * za ^ N * zb ^ N) *
        (sixVertexBetheAmplitude c p (σ * τ) * R * B (σ * τ)) =
      (Complex.exp (-Complex.I * θ) * zb ^ N *
          sixVertexBetheAmplitude c p (σ * τ)) * R *
        (za ^ N * B (σ * τ)) := by ring
    _ = (-(za ^ N * sixVertexBetheAmplitude c p σ)) * R *
        (zb ^ N * B σ) := by rw [hamp, hB]
    _ = -(za ^ N * zb ^ N * sixVertexBetheAmplitude c p σ * R * B σ) := by
      ring
    _ = (Complex.exp (-Complex.I * θ) * Complex.exp (Complex.I * θ)) *
        (-(za ^ N * zb ^ N * sixVertexBetheAmplitude c p σ * R * B σ)) := by
      rw [hexp, one_mul]
    _ = (Complex.exp (-Complex.I * θ) * za ^ N * zb ^ N) *
        (-sixVertexBetheAmplitude c p σ *
          (Complex.exp (Complex.I * θ) * R) * B σ) := by
      ring
    _ = (Complex.exp (-Complex.I * θ) * za ^ N * zb ^ N) *
        (-sixVertexBetheAmplitude c p σ * O * B σ) := by rw [hphase]


theorem sum_sixVertexBetheAmplitude_boundary_ML_eq_zero
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 2) → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (B : Equiv.Perm (Fin (n + 2)) → ℂ)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1)
    (hB : ∀ σ, sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N *
        B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 *
          finRotate (n + 2))) =
      sixVertexBethePhase (p (σ 0)) ^ N * B σ) :
    ∑ σ, sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c
              (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) *
            sixVertexBetheL c (sixVertexBethePhase (p (σ 0))) - 1) *
          B σ = 0 := by
  let τ : Equiv.Perm (Fin (n + 2)) :=
    (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2)
  have hr0 : (finRotate (n + 2)).symm 0 = Fin.last (n + 1) := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hr1 : (finRotate (n + 2)).symm 1 = 0 := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hτ0 : τ 0 = Fin.last (n + 1) := by
    simp [τ, Equiv.Perm.mul_apply, hr0]
  have hτlast : τ (Fin.last (n + 1)) = 0 := by
    simp [τ, Equiv.Perm.mul_apply, hr1]
  apply sum_perm_eq_zero_of_mul_neg τ
  intro σ
  have hlocal := sixVertexBetheAmplitude_boundary_ML_cancel hc p hp σ B
    (hphase _) (hphase _) (hB σ)
  change sixVertexBetheAmplitude c p (σ * τ) *
      (sixVertexBetheM c (sixVertexBethePhase (p (σ 0))) *
          sixVertexBetheL c
            (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) - 1) *
      B (σ * τ) = _ at hlocal
  simpa [Equiv.Perm.mul_apply, hτ0, hτlast] using hlocal

theorem sixVertexBetheBoundaryPermutation_eq_swap (n : ℕ) :
    (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2) =
      Equiv.swap (Fin.last (n + 1)) 0 := by
  have h0 : (finRotate (n + 2)).symm 0 = Fin.last (n + 1) := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have h1 : (finRotate (n + 2)).symm 1 = 0 := by
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  change ((finRotate (n + 2)).trans (Equiv.swap 0 1)).trans
      (finRotate (n + 2)).symm = _
  rw [Equiv.trans_swap_trans_symm, h0, h1]

theorem sum_sixVertexBetheWordTerm_boundary_eq_zero
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 2) → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (x : Fin (n + 2) → ℤ) (w : Finset (Fin (n + 2)))
    (haM : Fin.last (n + 1) ∉ w) (hbL : (0 : Fin (n + 2)) ∈ w)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    ∑ σ, sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase (p j)) σ w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
  let z : Fin (n + 2) → ℂ := fun j => sixVertexBethePhase (p j)
  let a : Fin (n + 2) := Fin.last (n + 1)
  let tau : Equiv.Perm (Fin (n + 2)) :=
    (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2)
  have hz (j : Fin (n + 2)) : z j ≠ 0 := Complex.exp_ne_zero _
  have hrot : finRotate (n + 2) a = 0 := by
    apply Fin.ext
    simp [a]
  have htau : tau = Equiv.swap a 0 := by
    simpa [tau, a] using sixVertexBetheBoundaryPermutation_eq_swap n
  let B : Equiv.Perm (Fin (n + 2)) → ℂ := fun σ =>
    sixVertexBetheWordCoefficientRemainder c z σ w a *
      sixVertexBetheWordMonomial N z σ x w
  have hB (σ : Equiv.Perm (Fin (n + 2))) :
      z (σ a) ^ N * B (σ * tau) = z (σ 0) ^ N * B σ := by
    have hrem := sixVertexBetheWordCoefficientRemainder_swap_invariant
      c z σ w haM hbL hrot
    have hmon := sixVertexBetheWordMonomial_boundary_covariant (N := N)
      z hz σ x w haM hbL
    dsimp [B]
    rw [htau, hrem]
    dsimp [a] at hmon ⊢
    calc
      z (σ (Fin.last (n + 1))) ^ N *
          (sixVertexBetheWordCoefficientRemainder c z σ w
              (Fin.last (n + 1)) *
            sixVertexBetheWordMonomial N z
              (σ * Equiv.swap (Fin.last (n + 1)) 0) x w) =
        sixVertexBetheWordCoefficientRemainder c z σ w
            (Fin.last (n + 1)) *
          (z (σ (Fin.last (n + 1))) ^ N *
            sixVertexBetheWordMonomial N z
              (σ * Equiv.swap (Fin.last (n + 1)) 0) x w) := by ring
      _ = sixVertexBetheWordCoefficientRemainder c z σ w
            (Fin.last (n + 1)) *
          (z (σ 0) ^ N * sixVertexBetheWordMonomial N z σ x w) := by
        rw [hmon]
      _ = _ := by ring
  have hsum := sum_sixVertexBetheAmplitude_boundary_ML_eq_zero
    hc p hp B hphase (by
      intro σ
      simpa [z, a, tau] using hB σ)
  calc
    (∑ σ, sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c z σ w *
          sixVertexBetheWordMonomial N z σ x w) =
      ∑ σ, sixVertexBetheAmplitude c p σ *
        (sixVertexBetheM c (z (σ a)) *
          sixVertexBetheL c (z (σ 0)) - 1) * B σ := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder
          c z σ w haM hbL hrot]
        dsimp [B]
        ring
    _ = 0 := by
      simpa [z, a] using hsum

theorem exists_sixVertexBetheCyclic_ML_of_nonconstant
    {n : ℕ} (w : Finset (Fin (n + 1)))
    (hne : w ≠ ∅) (hnu : w ≠ Finset.univ) :
    (∃ i : Fin n, i.castSucc ∉ w ∧ i.succ ∈ w) ∨
      (Fin.last n ∉ w ∧ (0 : Fin (n + 1)) ∈ w) := by
  by_contra h
  have hadj (i : Fin n) (hsucc : i.succ ∈ w) : i.castSucc ∈ w := by
    by_contra hprev
    exact h (Or.inl ⟨i, hprev, hsucc⟩)
  have hwne : w.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨j, hj⟩ := hwne
  have htozero (k : Fin (n + 1)) :
      k ∈ w → (0 : Fin (n + 1)) ∈ w := by
    induction k using Fin.induction with
    | zero => exact id
    | succ i ih =>
        intro hs
        exact ih (hadj i hs)
  have hzero : (0 : Fin (n + 1)) ∈ w := htozero j hj
  have hlast : Fin.last n ∈ w := by
    by_contra hl
    exact h (Or.inr ⟨hl, hzero⟩)
  have hall (k : Fin (n + 1)) : k ∈ w := by
    induction k using Fin.reverseInduction with
    | last => exact hlast
    | cast i ih => exact hadj i ih
  apply hnu
  exact Finset.eq_univ_iff_forall.mpr hall


theorem sum_sixVertexBetheWordTerm_eq_zero_of_nonconstant
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : Fin (n + 1) → ℤ) (w : Finset (Fin (n + 1)))
    (hne : w ≠ ∅) (hnu : w ≠ Finset.univ)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    ∑ σ, sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase (p j)) σ w *
          sixVertexBetheWordMonomial N
            (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
  rcases exists_sixVertexBetheCyclic_ML_of_nonconstant w hne hnu with
    ⟨i, hiM, hiL⟩ | ⟨hlast, hzero⟩
  · exact sum_sixVertexBetheWordTerm_adjacent_eq_zero
      hc p x w i hiM hiL hphase
  · cases n with
    | zero =>
        exact False.elim (hlast (by simpa using hzero))
    | succ m =>
        exact sum_sixVertexBetheWordTerm_boundary_eq_zero
          hc p hp x w hlast hzero hphase




theorem SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue
    {c : ℝ} (hc : 2 < c) {N n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (x : Fin (n + 1) → ℤ)
    (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
    (∑ w : Finset (Fin (n + 1)),
      ∑ σ, sixVertexBetheAmplitude c p σ *
        sixVertexBetheWordCoefficient c
          (fun j => sixVertexBethePhase (p j)) σ w *
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase (p j)) σ x w) =
      sixVertexBetheEigenvalueCandidate c p *
        sixVertexCoordinateBetheIntWave c p x := by
  let F : Finset (Fin (n + 1)) → ℂ := fun w =>
    ∑ σ, sixVertexBetheAmplitude c p σ *
      sixVertexBetheWordCoefficient c
        (fun j => sixVertexBethePhase (p j)) σ w *
      sixVertexBetheWordMonomial N
        (fun j => sixVertexBethePhase (p j)) σ x w
  have hnon (w : Finset (Fin (n + 1))) (hne : w ≠ ∅)
      (hnu : w ≠ Finset.univ) : F w = 0 := by
    exact sum_sixVertexBetheWordTerm_eq_zero_of_nonconstant
      hc p hp x w hne hnu hphase
  have hempty_ne_univ :
      (∅ : Finset (Fin (n + 1))) ≠ Finset.univ := by
    intro h
    have hz : (0 : Fin (n + 1)) ∈
        (∅ : Finset (Fin (n + 1))) := by
      rw [h]
      simp
    simp at hz
  have hsplit : (∑ w, F w) = F ∅ + F Finset.univ := by
    calc
      (∑ w, F w) =
          ∑ w ∈ ({∅, Finset.univ} : Finset (Finset (Fin (n + 1)))),
            F w := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hw
        apply hnon w
        · intro he
          apply hw
          simp [he]
        · intro hu
          apply hw
          simp [hu]
      _ = F ∅ + F Finset.univ := by simp [hempty_ne_univ]
  change (∑ w, F w) = _
  rw [hsplit]
  have hconstants : F ∅ + F Finset.univ =
      ∑ σ, sixVertexBetheAmplitude c p σ *
        (((∏ k, sixVertexBetheL c (sixVertexBethePhase (p (σ k)))) *
            sixVertexBetheIntMonomial p σ
              (sixVertexBetheShiftCoordinates N x)) +
          ((∏ k, sixVertexBetheM c (sixVertexBethePhase (p (σ k)))) *
            sixVertexBetheIntMonomial p σ x)) := by
    dsimp [F]
    simp only [sixVertexBetheWordCoefficient_empty,
      sixVertexBetheWordCoefficient_univ,
      sixVertexBetheWordMonomial_empty,
      sixVertexBetheWordMonomial_univ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    unfold sixVertexBetheIntMonomial
    ring
  rw [hconstants]
  exact hp.constantWordContribution hc x

end

end StatMech.FrontierD
