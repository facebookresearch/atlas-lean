/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedTopWitness

namespace StatMech.Universality

open HexWalk

noncomputable section



structure HexAsymmetricHighestCut (K : ℝ) where
  D : Type
  B₁ : Type
  B₂ : Type
  wtγ : D → ℝ
  wtB₁ : B₁ → ℝ
  wtB₂ : B₂ → ℝ
  wtγ_nn : ∀ d, 0 ≤ wtγ d
  wtB₁_nn : ∀ b, 0 ≤ wtB₁ b
  wtB₂_nn : ∀ b, 0 ≤ wtB₂ b
  split : D → B₁ × B₂
  split_injective : Function.Injective split
  weight_bound : ∀ d,
    wtγ d ≤ K * (wtB₁ (split d).1 * wtB₂ (split d).2)
  D_summable : Summable wtγ
  B₁_summable : Summable wtB₁
  B₂_summable : Summable wtB₂

namespace HexAsymmetricHighestCut

variable {K : ℝ}



theorem recursion_bound (H : HexAsymmetricHighestCut K) (hK : 0 ≤ K) :
    (∑' d, H.wtγ d) ≤
      K * ((∑' b, H.wtB₁ b) * (∑' b, H.wtB₂ b)) := by
  have hprodSumm : Summable
      (fun p : H.B₁ × H.B₂ => H.wtB₁ p.1 * H.wtB₂ p.2) :=
    H.B₁_summable.mul_of_nonneg H.B₂_summable
      H.wtB₁_nn H.wtB₂_nn
  have hprodEq :
      (∑' p : H.B₁ × H.B₂, H.wtB₁ p.1 * H.wtB₂ p.2) =
        (∑' b, H.wtB₁ b) * (∑' b, H.wtB₂ b) := by
    rw [← H.B₁_summable.tsum_mul_tsum H.B₂_summable hprodSumm]
  have hcompSumm : Summable
      (fun d => H.wtB₁ (H.split d).1 * H.wtB₂ (H.split d).2) :=
    hprodSumm.comp_injective H.split_injective
  have hcompLe :
      (∑' d, H.wtB₁ (H.split d).1 * H.wtB₂ (H.split d).2) ≤
        ∑' p : H.B₁ × H.B₂, H.wtB₁ p.1 * H.wtB₂ p.2 := by
    exact Summable.tsum_le_tsum_of_inj H.split H.split_injective
      (fun p _ => mul_nonneg (H.wtB₁_nn p.1) (H.wtB₂_nn p.2))
      (fun _ => le_rfl) hcompSumm hprodSumm
  calc
    (∑' d, H.wtγ d) ≤
        ∑' d, K *
          (H.wtB₁ (H.split d).1 * H.wtB₂ (H.split d).2) :=
      H.D_summable.tsum_mono (hcompSumm.mul_left K) H.weight_bound
    _ = K * ∑' d,
        H.wtB₁ (H.split d).1 * H.wtB₂ (H.split d).2 := tsum_mul_left
    _ ≤ K * ∑' p : H.B₁ × H.B₂,
        H.wtB₁ p.1 * H.wtB₂ p.2 :=
      mul_le_mul_of_nonneg_left hcompLe hK
    _ = K * ((∑' b, H.wtB₁ b) * (∑' b, H.wtB₂ b)) := by
      rw [hprodEq]

end HexAsymmetricHighestCut





theorem hex_shifted_reciprocal_not_summable
    (K : ℝ) (hK : 0 < K)
    (shift₁ shift₂ : ℕ) (hshift₁ : 1 ≤ shift₁)
    (hshift₂ : 1 ≤ shift₂)
    (lam ups : ℕ → ℝ)
    (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + ups v = 1)
    (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
    (hupsnn : ∀ v, 0 ≤ ups v)
    (hupsOne : 0 < ups 1)
    (hrec : ∀ v, 1 ≤ v →
      lam (v + 1) - lam v ≤
        K * (ups (v + shift₁) * ups (v + shift₂))) :
    ¬ Summable ups := by
  have hupsMono : ∀ v, 1 ≤ v → ups (v + 1) ≤ ups v := by
    intro v hv
    have e1 := hbdry v hv
    have e2 := hbdry (v + 1) (by omega)
    have hm := mul_le_mul_of_nonneg_left (hlamMono v hv)
      (le_of_lt hexCl_pos)
    nlinarith
  have hupsAnti : ∀ a b, 1 ≤ a → a ≤ b → ups b ≤ ups a := by
    intro a b ha hab
    obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        have hstep := hupsMono (a + k) (by omega)
        exact (by simpa [Nat.add_assoc] using
          hstep.trans (ih (by omega)))
  have hupsPos : ∀ v, 1 ≤ v → 0 < ups v := by
    intro v hv
    obtain ⟨k, rfl⟩ : ∃ k, v = 1 + k := ⟨v - 1, by omega⟩
    induction k with
    | zero => simpa using hupsOne
    | succ k ih =>
        change 0 < ups ((1 + k) + 1)
        by_contra hnot
        have hzero : ups ((1 + k) + 1) = 0 :=
          le_antisymm (le_of_not_gt hnot) (hupsnn _)
        have hzeroShift : ups ((1 + k) + shift₁) = 0 := by
          have hm := hupsAnti ((1 + k) + 1) ((1 + k) + shift₁)
            (by omega) (by omega)
          rw [hzero] at hm
          exact le_antisymm hm (hupsnn _)
        have hr := hrec (1 + k) (by omega)
        rw [hzeroShift, zero_mul, mul_zero] at hr
        have hlam := hlamMono (1 + k) (by omega)
        have hlameq : lam ((1 + k) + 1) = lam (1 + k) :=
          le_antisymm (by linarith) hlam
        have e1 := hbdry (1 + k) (by omega)
        have e2 := hbdry ((1 + k) + 1) (by omega)
        rw [hlameq, hzero] at e2
        have hprev := ih (by omega)
        nlinarith
  have hrecNext : ∀ v, 1 ≤ v →
      lam (v + 1) - lam v ≤ K * (ups (v + 1)) ^ 2 := by
    intro v hv
    have hr := hrec v hv
    have hm₁ := hupsAnti (v + 1) (v + shift₁) (by omega) (by omega)
    have hm₂ := hupsAnti (v + 1) (v + shift₂) (by omega) (by omega)
    have hsquare : ups (v + shift₁) * ups (v + shift₂) ≤
        (ups (v + 1)) ^ 2 := by
      nlinarith [hupsnn (v + 1), hupsnn (v + shift₁),
        hupsnn (v + shift₂)]
    exact hr.trans (mul_le_mul_of_nonneg_left hsquare (le_of_lt hK))
  have hdefect : ∀ v, 1 ≤ v →
      ups v - ups (v + 1) ≤
        (hexCl * K) * (ups (v + 1)) ^ 2 := by
    intro v hv
    have e1 := hbdry v hv
    have e2 := hbdry (v + 1) (by omega)
    have hr := hrecNext v hv
    have hm := mul_le_mul_of_nonneg_left hr (le_of_lt hexCl_pos)
    nlinarith
  let C := hexCl * K
  have hC : 0 < C := mul_pos hexCl_pos hK
  have hrecip := hex_recip_induction ups C hC hupsPos hupsMono hdefect
  let m := min (ups 1) (1 / C)
  have hm : 0 < m := lt_min hupsOne (by positivity)
  have hlower : ∀ v, 1 ≤ v → m / v ≤ ups v := by
    intro v hv
    have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
    have huv := hupsPos v hv
    have h := hrecip v hv
    rw [div_le_div_iff₀ huv hm] at h
    rw [div_le_iff₀ hvpos]
    nlinarith
  exact hex_div_of_lower_bound ups m hm hupsnn hlower




theorem hexCS_critical_divergence_of_shifted_recurrence
    (K : ℝ) (hK : 0 < K)
    (shift₁ shift₂ : ℕ) (hshift₁ : 1 ≤ shift₁)
    (hshift₂ : 1 ≤ shift₂)
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) →
      ∀ T, 1 ≤ T →
        hexCSInfiniteSideMassAtWidth (T + 1) -
            hexCSInfiniteSideMassAtWidth T ≤
          K * (hexCSInfiniteTopMassAtWidth (T + shift₁) *
            hexCSInfiniteTopMassAtWidth (T + shift₂)))
    (htopOne : ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
  intro hcoeff
  have hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) :=
    (hexEndpoint_walk_summable_iff_hlc hexAWStart 1 hexChiE_pos).2 hcoeff
  obtain ⟨topOneTurns, htopOneTurns⟩ := htopOne
  have htopOnePos : 0 < hexCSInfiniteTopMassAtWidth 1 :=
    hexCSInfiniteTopMassAtWidth_one_pos_of_mem hwalk topOneTurns htopOneTurns
  let ups := hecd_columnSum hexAWStart 1 HexCSTopWalkAnyWidth
    hexCSTopWalkWidth
  have hbdry : ∀ T, 1 ≤ T →
      hexCl * hexCSInfiniteSideMassAtWidth T + ups T = 1 := by
    intro T hT
    have hid := hexCS_infinite_height_identity_atWidth T (by omega)
      hwalk (fun L => hlocal T L (by omega))
      (fun L => hwindow T L (by omega))
    dsimp only [ups]
    rw [hecd_correctedTop_columnSum_eq_atWidth T (by omega)]
    exact hid
  have hupsOne : 0 < ups 1 := by
    dsimp only [ups]
    rw [hecd_correctedTop_columnSum_eq_atWidth 1 (by norm_num)]
    exact htopOnePos
  have hrec' : ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        K * (ups (T + shift₁) * ups (T + shift₂)) := by
    intro T hT
    dsimp only [ups]
    rw [hecd_correctedTop_columnSum_eq_atWidth (T + shift₁) (by omega),
      hecd_correctedTop_columnSum_eq_atWidth (T + shift₂) (by omega)]
    exact hrec hwalk T hT
  have hnot : ¬ Summable ups :=
    hex_shifted_reciprocal_not_summable K hK
      shift₁ shift₂ hshift₁ hshift₂
      hexCSInfiniteSideMassAtWidth ups hbdry
      (hexCSInfiniteSideMassAtWidth_mono hwalk)
      (hecd_columnSum_nonneg hexAWStart 1 HexCSTopWalkAnyWidth
        hexCSTopWalkWidth)
      hupsOne hrec'
  exact hnot (hecd_correctedTop_columnSum_summable hwalk)

end

end StatMech.Universality
