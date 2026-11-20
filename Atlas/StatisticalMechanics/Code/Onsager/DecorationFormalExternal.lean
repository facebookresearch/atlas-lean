/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalSurgery








namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decFormalRootedLogCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1))

noncomputable def ons_decFormalAvoidLogCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  -(∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1)) / 2

noncomputable def ons_decFormalRootedLog
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalRootedLogCoeff L a b d

noncomputable def ons_decFormalAvoidLog
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalAvoidLogCoeff L a b d

theorem ons_decFormalLogCoeff_eq_rooted_add_avoid
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) m =
      ons_decFormalRootedLogCoeff L a b d m +
        ons_decFormalAvoidLogCoeff L a b d m := by
  unfold ons_decFormalLogCoeff ons_decFormalRootedLogCoeff
    ons_decFormalAvoidLogCoeff
  have hsum :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ loop : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / ((r : ℂ) + 1)) =
        2 * (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
          ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1)) +
          ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
            ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1) := by
    calc
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        (∑ loop : Fin (r + 1) → ons_Dart L,
          if ons_decLoopExponent L loop = m then
            ons_decLoopScalar L ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b) loop
          else 0) / ((r : ℂ) + 1)) =
          ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
            (2 * ons_decFormalFixedBucketE L a b d r m +
              ons_decFormalFixedBucketN L a b d r m) / ((r : ℂ) + 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [ons_decLoopScalar_sum_fixedExponent_two_bucket]
      _ = _ := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib]
        have hE :
            (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
              2 * ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1)) =
              2 * ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
                ons_decFormalFixedBucketE L a b d r m / ((r : ℂ) + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        rw [hE]
  rw [hsum]
  ring

theorem ons_decFormalLog_eq_rooted_add_avoid
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_decFormalLog L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      ons_decFormalRootedLog L a b d + ons_decFormalAvoidLog L a b d := by
  ext m
  exact ons_decFormalLogCoeff_eq_rooted_add_avoid L a b d m

theorem ons_decFormalFixedBucketN_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (r : ℕ) (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    ons_decFormalFixedBucketN L a b d r m = 0 := by
  classical
  unfold ons_decFormalFixedBucketN
  apply Finset.sum_eq_zero
  intro loop hloop
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hloop
  push Not at hloop
  rw [if_neg]
  intro hexponent
  apply hmedge
  rw [← hexponent, ons_decLoopExponent_external_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [if_neg]
  exact not_or_intro (hloop.1 k) (hloop.2 k)

theorem ons_decFormalAvoidLogCoeff_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    ons_decFormalAvoidLogCoeff L a b d m = 0 := by
  unfold ons_decFormalAvoidLogCoeff
  have hsum :
      (∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
        ons_decFormalFixedBucketN L a b d r m / ((r : ℂ) + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [ons_decFormalFixedBucketN_eq_zero_of_external
      L a b d r m hmedge, zero_div]
  rw [hsum]
  ring

theorem ons_decFormalAvoidLog_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalAvoidLog L a b d) = 0 := by
  change ons_decFormalAvoidLogCoeff L a b d 0 = 0
  simp [ons_decFormalAvoidLogCoeff, ons_finsuppTotalDegree]

theorem ons_decFormalAvoidLog_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (ons_decFormalAvoidLog L a b d) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalAvoidLog_constantCoeff L a b d)

noncomputable def ons_decFormalAvoidRoot
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  PowerSeries.subst (ons_decFormalAvoidLog L a b d) (PowerSeries.exp ℂ)

theorem ons_decFormalAvoidRoot_coeff_eq_zero_of_external
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 0) :
    MvPowerSeries.coeff m (ons_decFormalAvoidRoot L a b d) = 0 := by
  classical
  unfold ons_decFormalAvoidRoot
  rw [PowerSeries.coeff_subst
    (ons_decFormalAvoidLog_hasSubst L a b d)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  apply smul_eq_zero.mpr
  right
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro g hg
  have hsum := congrArg (fun x : ons_DecEdge L →₀ ℕ ↦
    x s(d, ons_dartRev L d)) (Finset.mem_finsuppAntidiag.mp hg).1
  simp only [Finsupp.finsetSum_apply] at hsum
  have hexists : ∃ i ∈ Finset.range n,
      g i s(d, ons_dartRev L d) ≠ 0 := by
    by_contra hnone
    have hall : ∀ i ∈ Finset.range n,
        g i s(d, ons_dartRev L d) = 0 := by
      intro i hi
      exact not_ne_iff.mp (fun hne ↦ hnone ⟨i, hi, hne⟩)
    have hzero : ∑ i ∈ Finset.range n,
        g i s(d, ons_dartRev L d) = 0 := Finset.sum_eq_zero hall
    rw [hzero] at hsum
    exact hmedge hsum.symm
  obtain ⟨i, hi, hgi⟩ := hexists
  apply Finset.prod_eq_zero hi
  change ons_decFormalAvoidLogCoeff L a b d (g i) = 0
  exact ons_decFormalAvoidLogCoeff_eq_zero_of_external
    L a b d (g i) hgi

def ons_decIsFirstReturnLoop
    {L n : ℕ} [NeZero n] (d : ons_Dart L)
    (loop : Fin n → ons_Dart L) : Prop :=
  loop 0 = d ∧
    (∀ k, k ≠ 0 → loop k ≠ d) ∧
      ∀ k, loop k ≠ ons_dartRev L d

instance ons_decIsFirstReturnLoop_decidable
    {L n : ℕ} [NeZero n] (d : ons_Dart L)
    (loop : Fin n → ons_Dart L) :
    Decidable (ons_decIsFirstReturnLoop d loop) := by
  unfold ons_decIsFirstReturnLoop
  infer_instance

noncomputable def ons_decFormalFirstReturnCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : ℂ :=
  ∑ r ∈ Finset.range (ons_finsuppTotalDegree m),
    ∑ loop : Fin (r + 1) → ons_Dart L,
      if ons_decIsFirstReturnLoop d loop ∧
          ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0

noncomputable def ons_decFormalFirstReturn
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries (ons_DecEdge L) ℂ :=
  ons_decFormalFirstReturnCoeff L a b d

theorem ons_decLoopExponent_external_eq_one_of_firstReturn
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : ons_Dart L) (loop : Fin n → ons_Dart L)
    (hfirst : ons_decIsFirstReturnLoop d loop) :
    ons_decLoopExponent L loop s(d, ons_dartRev L d) = 1 := by
  rw [ons_decLoopExponent_external_apply]
  rw [Fintype.sum_eq_single (0 : Fin n)]
  · rw [if_pos (Or.inl hfirst.1)]
  · intro k hkzero
    rw [if_neg]
    exact not_or_intro (hfirst.2.1 k hkzero) (hfirst.2.2 k)

theorem ons_decFormalFirstReturnCoeff_eq_zero_unless_external_one
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ)
    (hmedge : m s(d, ons_dartRev L d) ≠ 1) :
    ons_decFormalFirstReturnCoeff L a b d m = 0 := by
  classical
  unfold ons_decFormalFirstReturnCoeff
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro loop hloop
  rw [if_neg]
  rintro ⟨hfirst, hexponent⟩
  apply hmedge
  rw [← hexponent]
  exact ons_decLoopExponent_external_eq_one_of_firstReturn
    L d loop hfirst

theorem ons_decFormalFirstReturn_constantCoeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    MvPowerSeries.constantCoeff (ons_decFormalFirstReturn L a b d) = 0 := by
  change ons_decFormalFirstReturnCoeff L a b d 0 = 0
  simp [ons_decFormalFirstReturnCoeff, ons_finsuppTotalDegree]

theorem ons_decFormalFirstReturn_hasSubst
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    PowerSeries.HasSubst (ons_decFormalFirstReturn L a b d) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (ons_decFormalFirstReturn_constantCoeff L a b d)

end StatMech.Onsager
