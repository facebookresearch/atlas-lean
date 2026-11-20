/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










namespace StatMech
namespace Exact3D




structure CriticalModel (ι : Type*) where
  
  betaC : ℝ
  

  twoPoint : ℝ → ι → ι → ℝ


def TwoPointFunction {ι : Type*} (M : CriticalModel ι) : ℝ → ι → ι → ℝ :=
  M.twoPoint


def TwoPointAlongRay {ι : Type*} (M : CriticalModel ι) (β : ℝ) (origin : ι)
    (ray : ℕ → ι) (n : ℕ) : ℝ :=
  M.twoPoint β origin (ray n)




noncomputable def finiteDistanceDecayRate (G : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else -Real.log |G n| / (n : ℝ)


noncomputable def inverseDecayRate {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (n : ℕ) : ℝ :=
  finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) n


noncomputable def lowerInverseCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  Filter.liminf (inverseDecayRate M β origin ray) Filter.atTop


noncomputable def upperInverseCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  Filter.limsup (inverseDecayRate M β origin ray) Filter.atTop


def HasInverseCorrelationLength {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (m : ℝ) : Prop :=
  Filter.Tendsto (inverseDecayRate M β origin ray) Filter.atTop (nhds m)



structure HasCorrelationLength {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (ξ : ℝ) : Prop where
  xi_pos : 0 < ξ
  tendsto_inverse :
    HasInverseCorrelationLength M β origin ray ξ⁻¹




noncomputable def liminfCorrelationLength {ι : Type*} (M : CriticalModel ι)
    (β : ℝ) (origin : ι) (ray : ℕ → ι) : ℝ :=
  (lowerInverseCorrelationLength M β origin ray)⁻¹


noncomputable def logSlope {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (β : ℝ) : ℝ :=
  -Real.log (correlationLength β) / Real.log (M.betaC - β)



def HasCriticalNu {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (ν : ℝ) : Prop :=
  Filter.Tendsto (logSlope M correlationLength)
    (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds ν)

theorem logSlope_congr_betaC {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    (hβc : M.betaC = N.betaC) (correlationLength : ℝ → ℝ) (β : ℝ) :
    logSlope M correlationLength β = logSlope N correlationLength β := by
  simp [logSlope, hβc]



theorem HasCriticalNu.congr_betaC {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    {correlationLength : ℝ → ℝ} {ν : ℝ}
    (hν : HasCriticalNu M correlationLength ν) (hβc : M.betaC = N.betaC) :
    HasCriticalNu N correlationLength ν := by
  unfold HasCriticalNu at hν ⊢
  have hlog :
      logSlope N correlationLength = logSlope M correlationLength := by
    funext β
    simp [logSlope, hβc.symm]
  rw [hlog]
  simpa [hβc.symm] using hν



theorem HasCriticalNu.congr_betaC_iff {ι κ : Type*}
    {M : CriticalModel ι} {N : CriticalModel κ}
    {correlationLength : ℝ → ℝ} {ν : ℝ}
    (hβc : M.betaC = N.betaC) :
    HasCriticalNu M correlationLength ν ↔
      HasCriticalNu N correlationLength ν :=
  ⟨fun hν => hν.congr_betaC hβc,
    fun hν => hν.congr_betaC hβc.symm⟩



theorem HasCriticalNu.congr_eventually {ι : Type*}
    {M : CriticalModel ι} {correlationLength comparisonLength : ℝ → ℝ}
    {ν : ℝ}
    (hν : HasCriticalNu M correlationLength ν)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    HasCriticalNu M comparisonLength ν := by
  unfold HasCriticalNu at hν ⊢
  refine Filter.Tendsto.congr' ?_ hν
  filter_upwards [hEq] with β hβ
  simp [logSlope, hβ]



theorem HasCriticalNu.congr_eventually_iff {ι : Type*}
    {M : CriticalModel ι} {correlationLength comparisonLength : ℝ → ℝ}
    {ν : ℝ}
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        comparisonLength β = correlationLength β) :
    HasCriticalNu M correlationLength ν ↔
      HasCriticalNu M comparisonLength ν :=
  ⟨fun hν => hν.congr_eventually hEq,
    fun hν => hν.congr_eventually
      (hEq.mono (fun _ hβ => hβ.symm))⟩

theorem HasCorrelationLength.positive {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (hξ : HasCorrelationLength M β origin ray ξ) : 0 < ξ :=
  hξ.xi_pos

theorem HasInverseCorrelationLength.unique {ι : Type*} {M : CriticalModel ι}
    {β : ℝ} {origin : ι} {ray : ℕ → ι} {m₁ m₂ : ℝ}
    (h₁ : HasInverseCorrelationLength M β origin ray m₁)
    (h₂ : HasInverseCorrelationLength M β origin ray m₂) : m₁ = m₂ :=
  tendsto_nhds_unique h₁ h₂



theorem HasInverseCorrelationLength.lowerInverseCorrelationLength_eq
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (h : HasInverseCorrelationLength M β origin ray m) :
    lowerInverseCorrelationLength M β origin ray = m := by
  simpa [lowerInverseCorrelationLength, HasInverseCorrelationLength] using
    h.liminf_eq



theorem HasInverseCorrelationLength.upperInverseCorrelationLength_eq
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (h : HasInverseCorrelationLength M β origin ray m) :
    upperInverseCorrelationLength M β origin ray = m := by
  simpa [upperInverseCorrelationLength, HasInverseCorrelationLength] using
    h.limsup_eq



theorem HasInverseCorrelationLength.lower_eq_upper
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (h : HasInverseCorrelationLength M β origin ray m) :
    lowerInverseCorrelationLength M β origin ray =
      upperInverseCorrelationLength M β origin ray := by
  rw [h.lowerInverseCorrelationLength_eq, h.upperInverseCorrelationLength_eq]



theorem inverseDecayRate_congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    ∀ᶠ n in Filter.atTop,
      inverseDecayRate M β origin ray n =
        inverseDecayRate N β origin ray n := by
  filter_upwards [hEq] with n hn
  unfold inverseDecayRate
  by_cases hn0 : n = 0
  · simp only [finiteDistanceDecayRate, hn0, ↓reduceIte]
  · simp only [finiteDistanceDecayRate, hn0, ↓reduceIte]
    rw [congrArg (fun x : ℝ => Real.log |x|) hn]



theorem lowerInverseCorrelationLength_congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    lowerInverseCorrelationLength M β origin ray =
      lowerInverseCorrelationLength N β origin ray := by
  exact Filter.liminf_congr (inverseDecayRate_congr_eventually hEq)



theorem upperInverseCorrelationLength_congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    upperInverseCorrelationLength M β origin ray =
      upperInverseCorrelationLength N β origin ray := by
  exact Filter.limsup_congr (inverseDecayRate_congr_eventually hEq)



theorem liminfCorrelationLength_congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    liminfCorrelationLength M β origin ray =
      liminfCorrelationLength N β origin ray := by
  rw [liminfCorrelationLength, liminfCorrelationLength,
    lowerInverseCorrelationLength_congr_eventually hEq]




theorem HasCriticalNu.liminfCorrelationLength_congr_eventually_iff
    {ι : Type*} {M N : CriticalModel ι} {origin : ι} {ray : ℕ → ι}
    {ν : ℝ}
    (hβc : M.betaC = N.betaC)
    (hEq :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        ∀ᶠ n in Filter.atTop,
          TwoPointAlongRay M β origin ray n =
            TwoPointAlongRay N β origin ray n) :
    HasCriticalNu M
        (fun β => liminfCorrelationLength M β origin ray) ν ↔
      HasCriticalNu N
        (fun β => liminfCorrelationLength N β origin ray) ν := by
  have hObs :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        liminfCorrelationLength N β origin ray =
          liminfCorrelationLength M β origin ray := by
    filter_upwards [hEq] with β hβ
    exact (liminfCorrelationLength_congr_eventually hβ).symm
  exact
    (HasCriticalNu.congr_eventually_iff (M := M)
      (correlationLength :=
        fun β => liminfCorrelationLength M β origin ray)
      (comparisonLength :=
        fun β => liminfCorrelationLength N β origin ray)
      (ν := ν) hObs).trans
      (HasCriticalNu.congr_betaC_iff (M := M) (N := N)
        (correlationLength :=
          fun β => liminfCorrelationLength N β origin ray)
        (ν := ν) hβc)



theorem HasInverseCorrelationLength.congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (h : HasInverseCorrelationLength M β origin ray m)
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    HasInverseCorrelationLength N β origin ray m := by
  unfold HasInverseCorrelationLength inverseDecayRate at h ⊢
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [hEq] with n hn
  by_cases hn0 : n = 0
  · simp only [finiteDistanceDecayRate, hn0, ↓reduceIte]
  · simp only [finiteDistanceDecayRate, hn0, ↓reduceIte]
    rw [congrArg (fun x : ℝ => Real.log |x|) hn]



theorem HasInverseCorrelationLength.congr_eventually_iff {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    HasInverseCorrelationLength M β origin ray m ↔
      HasInverseCorrelationLength N β origin ray m :=
  ⟨fun h => h.congr_eventually hEq,
    fun h => h.congr_eventually
      (hEq.mono (fun _ hn => hn.symm))⟩



theorem HasInverseCorrelationLength.hasCorrelationLength_inv {ι : Type*}
    {M : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (h : HasInverseCorrelationLength M β origin ray m) (hm : 0 < m) :
    HasCorrelationLength M β origin ray m⁻¹ where
  xi_pos := inv_pos.mpr hm
  tendsto_inverse := by
    simpa using h

theorem HasCorrelationLength.unique {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ₁ ξ₂ : ℝ}
    (h₁ : HasCorrelationLength M β origin ray ξ₁)
    (h₂ : HasCorrelationLength M β origin ray ξ₂) : ξ₁ = ξ₂ := by
  have hinv : ξ₁⁻¹ = ξ₂⁻¹ :=
    HasInverseCorrelationLength.unique h₁.tendsto_inverse h₂.tendsto_inverse
  exact inv_injective hinv



theorem HasCorrelationLength.lowerInverseCorrelationLength_eq
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (h : HasCorrelationLength M β origin ray ξ) :
    lowerInverseCorrelationLength M β origin ray = ξ⁻¹ :=
  h.tendsto_inverse.lowerInverseCorrelationLength_eq



theorem HasCorrelationLength.upperInverseCorrelationLength_eq
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (h : HasCorrelationLength M β origin ray ξ) :
    upperInverseCorrelationLength M β origin ray = ξ⁻¹ :=
  h.tendsto_inverse.upperInverseCorrelationLength_eq



theorem HasCorrelationLength.lower_eq_upper
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (h : HasCorrelationLength M β origin ray ξ) :
    lowerInverseCorrelationLength M β origin ray =
      upperInverseCorrelationLength M β origin ray :=
  h.tendsto_inverse.lower_eq_upper



theorem HasCorrelationLength.liminfCorrelationLength_eq
    {ι : Type*} {M : CriticalModel ι} {β : ℝ}
    {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (h : HasCorrelationLength M β origin ray ξ) :
    liminfCorrelationLength M β origin ray = ξ := by
  simp [liminfCorrelationLength, h.lowerInverseCorrelationLength_eq]



theorem HasCorrelationLength.congr_eventually {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (h : HasCorrelationLength M β origin ray ξ)
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    HasCorrelationLength N β origin ray ξ where
  xi_pos := h.xi_pos
  tendsto_inverse := h.tendsto_inverse.congr_eventually hEq



theorem HasCorrelationLength.congr_eventually_iff {ι : Type*}
    {M N : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (hEq :
      ∀ᶠ n in Filter.atTop,
        TwoPointAlongRay M β origin ray n =
          TwoPointAlongRay N β origin ray n) :
    HasCorrelationLength M β origin ray ξ ↔
      HasCorrelationLength N β origin ray ξ :=
  ⟨fun h => h.congr_eventually hEq,
    fun h => h.congr_eventually
      (hEq.mono (fun _ hn => hn.symm))⟩

theorem finiteDistanceDecayRate_rescale (G : ℕ → ℝ) {L n : ℕ}
    (hL : L ≠ 0) (hn : n ≠ 0) :
    finiteDistanceDecayRate (fun k => G (L * k)) n =
      (L : ℝ) * finiteDistanceDecayRate G (L * n) := by
  have hLn : L * n ≠ 0 := Nat.mul_ne_zero hL hn
  have hLℝ : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [finiteDistanceDecayRate, hn, hLn, Nat.cast_mul]
  field_simp [hLℝ, hnℝ]


theorem tendsto_nat_mul_atTop {L : ℕ} (hL : L ≠ 0) :
    Filter.Tendsto (fun n : ℕ => L * n) Filter.atTop Filter.atTop := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hLone : 1 ≤ L := Nat.succ_le_of_lt hLpos
  refine Filter.tendsto_atTop_mono ?_ Filter.tendsto_id
  intro n
  calc
    n = 1 * n := by simp
    _ ≤ L * n := Nat.mul_le_mul_right n hLone



theorem HasInverseCorrelationLength.rescale_nat {ι : Type*}
    {M : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {m : ℝ}
    {L : ℕ} (hL : L ≠ 0)
    (h : HasInverseCorrelationLength M β origin ray m) :
    HasInverseCorrelationLength M β origin (fun n => ray (L * n))
      ((L : ℝ) * m) := by
  unfold HasInverseCorrelationLength inverseDecayRate at h ⊢
  have hcomp :
      Filter.Tendsto
        (fun n : ℕ =>
          finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) (L * n))
        Filter.atTop (nhds m) :=
    h.comp (tendsto_nat_mul_atTop hL)
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ =>
          (L : ℝ) *
            finiteDistanceDecayRate (TwoPointAlongRay M β origin ray) (L * n))
        Filter.atTop (nhds ((L : ℝ) * m)) :=
    tendsto_const_nhds.mul hcomp
  refine Filter.Tendsto.congr' ?_ hscaled
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  simpa [TwoPointAlongRay] using
    (finiteDistanceDecayRate_rescale
      (TwoPointAlongRay M β origin ray) (L := L) (n := n) hL hn).symm


theorem HasCorrelationLength.rescale_nat {ι : Type*}
    {M : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    {L : ℕ} (hL : L ≠ 0)
    (h : HasCorrelationLength M β origin ray ξ) :
    HasCorrelationLength M β origin (fun n => ray (L * n))
      (ξ / (L : ℝ)) where
  xi_pos := by
    exact div_pos h.xi_pos (by exact_mod_cast Nat.pos_of_ne_zero hL)
  tendsto_inverse := by
    have hξne : ξ ≠ 0 := ne_of_gt h.xi_pos
    have hLℝ : (L : ℝ) ≠ 0 := by exact_mod_cast hL
    have hrescaled := h.tendsto_inverse.rescale_nat hL
    have hinv : (ξ / (L : ℝ))⁻¹ = (L : ℝ) * ξ⁻¹ := by
      field_simp [hξne, hLℝ]
    simpa [hinv] using hrescaled



noncomputable def PlaceholderModel : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0

end Exact3D
end StatMech
