/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.FKSharpnessWeightedIntegration
import Code.OSSS.BetaThresholdBound
import Code.OSSS.BetaCMatch
import Code.OSSS.LogCesaroLimit

open scoped BigOperators Classical
open Finset Set Filter Topology
open MeasureTheory

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedThreshold

open Lattice FK
open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume
open FKSharpnessWeightedStrict FKSharpnessWeightedIntegration
open FKSharpnessWeightedCoherentLimit
open IntegrationSubcritical BetaThresholdBound
open BetaCMatch LogCesaroLimit

noncomputable def weightedPhaseSharpConstant
    (d : Nat) (Jmin Jmax beta0 : Real) : Real :=
  Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8

theorem weightedPhaseSharpConstant_pos
    (d : Nat) {Jmin Jmax beta0 : Real} (hJmin : 0 < Jmin) :
    0 < weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  unfold weightedPhaseSharpConstant
  positivity

noncomputable def weightedNormalizedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  weightedPhaseSum d phaseJ q beta n /
    weightedPhaseSharpConstant d Jmin Jmax beta0

noncomputable def weightedNormalizedPhaseSumPrime
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  deriv (fun b => weightedPhaseSum d phaseJ q b n) beta /
    weightedPhaseSharpConstant d Jmin Jmax beta0



noncomputable def weightedSelectedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta : Real) : Real :=
  ∑ a : P, weightedPhaseThetaProfile d phaseJ hJ q hq a beta

theorem weightedSelectedPhaseSum_nonneg
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta : Real) :
    0 <= weightedSelectedPhaseSum d phaseJ hJ q hq beta := by
  unfold weightedSelectedPhaseSum
  exact Finset.sum_nonneg fun a ha =>
    weightedPhaseThetaProfile_nonneg d phaseJ hJ q hq a beta



theorem weightedPhaseSum_tendsto_selectedPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => weightedPhaseSum d phaseJ q beta n) atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta)) := by
  unfold weightedPhaseSum weightedSelectedPhaseSum
  simp only [weightedPhaseThetaProfile, dif_pos hbeta]
  exact tendsto_finsetSum Finset.univ fun a ha =>
    weightedPhaseProfile_tendsto_infiniteTheta
      d phaseJ a (hJ a) q beta hq hbeta



theorem weightedNormalizedPhaseSum_tendsto
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun n => weightedNormalizedPhaseSum
        d phaseJ Jmin Jmax q beta0 n beta) atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta /
          weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
  exact (weightedPhaseSum_tendsto_selectedPhaseSum
    d phaseJ hJ q beta hq hbeta).div_const _



theorem weightedNormalizedPhaseSum_meanLogTerm_tendsto
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto
      (fun n => Integration.meanLogTerm
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta)
      atTop
      (nhds (weightedSelectedPhaseSum d phaseJ hJ q
        (zero_lt_one.trans_le hq) beta /
          weightedPhaseSharpConstant d Jmin Jmax beta0)) := by
  exact meanLogTerm_tendsto (weightedNormalizedPhaseSum_tendsto
    d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta)



noncomputable def weightedThresholdPhaseSum
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then (Fintype.card P : Real) /
      weightedPhaseSharpConstant d Jmin Jmax beta0 else 0
  else weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta

theorem weightedThresholdPhaseSum_of_pos
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) (hbeta : 0 < beta) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta =
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  simp [weightedThresholdPhaseSum, not_le.mpr hbeta]

theorem weightedNormalizedPhaseSumSig_eq
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) :
    Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta =
      weightedPhaseSumSig d n phaseJ q beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  unfold Sig weightedNormalizedPhaseSum weightedPhaseSumSig
  rw [Finset.sum_div]

theorem weightedPhaseSum_differentiableAt
    (d n : Nat) (hn : 1 <= n) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    DifferentiableAt Real (fun b => weightedPhaseSum d phaseJ q b n) beta := by
  unfold weightedPhaseSum
  exact DifferentiableAt.fun_sum fun a ha =>
    weightedPhaseProfile_differentiableAt d n hn phaseJ hJ a q beta hq hbeta

theorem weightedNormalizedPhaseSum_hasDerivAt
    (d n : Nat) (hn : 1 <= n) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt
      (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n)
      (weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta)
      beta := by
  have hd := weightedPhaseSum_differentiableAt
    d n hn phaseJ hJ q beta hq hbeta
  simpa [weightedNormalizedPhaseSum, weightedNormalizedPhaseSumPrime,
    div_eq_mul_inv, mul_comm] using hd.hasDerivAt.const_mul
      (weightedPhaseSharpConstant d Jmin Jmax beta0)⁻¹

theorem weightedNormalizedPhaseSum_differential
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (((n : Real) /
        Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) *
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta) <=
        weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta := by
  have hc := weightedPhaseSharpConstant_pos d
    (Jmax := Jmax) (beta0 := beta0) hJmin
  have hmain := weightedPhaseSum_differential_integration
    d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta beta0 hq hbeta hbeta0
  rw [weightedNormalizedPhaseSumSig_eq]
  unfold weightedNormalizedPhaseSum weightedNormalizedPhaseSumPrime
  rw [le_div_iff₀ hc]
  convert hmain using 1
  unfold weightedPhaseSharpConstant
  rw [Nat.mul_comm 2 d]
  field_simp

theorem weightedPhaseProfile_le_one
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseProfile d phaseJ a q beta n <= 1 := by
  by_cases hn0 : n = 0
  · simp [weightedPhaseProfile, hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  rw [weightedPhaseProfile, if_neg hn0,
    weightedPhaseWiredTheta_eq_finiteMeasure_double
      d n hn phaseJ a (hJ a) q beta hq hbeta]
  exact measureReal_le_one

@[simp] theorem weightedPhaseSum_zero
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) :
    weightedPhaseSum d phaseJ q beta 0 = Fintype.card P := by
  simp [weightedPhaseSum]

theorem weightedPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= weightedPhaseSum d phaseJ q beta n := by
  unfold weightedPhaseSum
  exact Finset.sum_nonneg fun a ha =>
    weightedPhaseProfile_nonneg d phaseJ hJ a q beta hq hbeta n

theorem weightedPhaseSum_le_card
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseSum d phaseJ q beta n <= Fintype.card P := by
  unfold weightedPhaseSum
  calc
    (∑ a : P, weightedPhaseProfile d phaseJ a q beta n) <=
        ∑ _a : P, (1 : Real) := Finset.sum_le_sum fun a ha =>
          weightedPhaseProfile_le_one d n phaseJ hJ a q beta hq hbeta
    _ = Fintype.card P := by simp

theorem weightedPhaseSumSig_pos
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < weightedPhaseSumSig d n phaseJ q beta := by
  have hzero : 0 < weightedPhaseSum d phaseJ q beta 0 := by
    rw [weightedPhaseSum_zero]
    exact_mod_cast Fintype.card_pos
  unfold weightedPhaseSumSig
  exact hzero.trans_le (Finset.single_le_sum
    (fun k hk => weightedPhaseSum_nonneg d k phaseJ hJ q beta hq hbeta)
    (Finset.mem_range.mpr hn))

theorem weightedNormalizedPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  exact div_nonneg (weightedPhaseSum_nonneg d n phaseJ hJ q beta hq hbeta)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSum_le_card_div
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta <=
      (Fintype.card P : Real) / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  unfold weightedNormalizedPhaseSum
  exact div_le_div_of_nonneg_right
    (weightedPhaseSum_le_card d n phaseJ hJ q beta hq hbeta)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSumPrime_nonneg
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) :
    0 <= weightedNormalizedPhaseSumPrime
      d phaseJ Jmin Jmax q beta0 n beta := by
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hSig := weightedPhaseSumSig_pos d n hn phaseJ hp q beta hq hbeta
  have hfnn := weightedPhaseSum_nonneg d n phaseJ hp q beta hq hbeta
  have hcBeta : 0 < weightedPhaseSharpConstant d Jmin Jmax beta :=
    weightedPhaseSharpConstant_pos d hJmin
  have hlhs : 0 <= weightedPhaseSharpConstant d Jmin Jmax beta *
      (((n : Real) / weightedPhaseSumSig d n phaseJ q beta) *
        weightedPhaseSum d phaseJ q beta n) :=
    mul_nonneg hcBeta.le
      (mul_nonneg (div_nonneg (Nat.cast_nonneg n) hSig.le) hfnn)
  have hraw := weightedPhaseSum_differential_integration
    d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta beta hq hbeta le_rfl
  unfold weightedNormalizedPhaseSumPrime
  exact div_nonneg (hlhs.trans hraw)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSum_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 y x : Real) (hq : 1 <= q)
    (hy : 0 < y) (hyx : y <= x) :
    weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n y <=
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n x := by
  by_cases hn0 : n = 0
  · subst n
    simp [weightedNormalizedPhaseSum]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let f := weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n
  let f' := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hd : forall z, z ∈ Icc y x -> HasDerivAt f (f' z) z := by
    intro z hz
    exact weightedNormalizedPhaseSum_hasDerivAt
      d n hn phaseJ hp Jmin Jmax q beta0 z hq (hy.trans_le hz.1)
  have hmono : MonotoneOn f (Icc y x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y x)
    · intro z hz
      exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (mem_Icc_of_Ioo hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (mem_Icc_of_Ioo hz)).deriv]
      exact weightedNormalizedPhaseSumPrime_nonneg
        d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q z beta0 hq (hy.trans hz.1)
  exact hmono (left_mem_Icc.mpr hyx) (right_mem_Icc.mpr hyx) hyx

theorem weightedThresholdPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    0 <= weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_pos hn0]
      exact div_nonneg (Nat.cast_nonneg _)
        (weightedPhaseSharpConstant_pos d hJmin).le
    · simp [weightedThresholdPhaseSum, hbeta, hn0]
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
      Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
    exact weightedNormalizedPhaseSum_nonneg d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq (lt_of_not_ge hbeta)

theorem weightedThresholdPhaseSum_le_card_div
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta <=
      (Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · simp [weightedThresholdPhaseSum, hbeta, hn0]
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_neg hn0]
      exact div_nonneg (Nat.cast_nonneg _) (weightedPhaseSharpConstant_pos
        d hJmin).le
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
      Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
    exact weightedNormalizedPhaseSum_le_card_div d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq (lt_of_not_ge hbeta)

theorem weightedThresholdPhaseSum_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 a b : Real) (hq : 1 <= q) (hab : a <= b) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n a <=
      weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n b := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  by_cases hb : b <= 0
  · have ha : a <= 0 := hab.trans hb
    simp [weightedThresholdPhaseSum, ha, hb]
  by_cases ha : a <= 0
  · by_cases hn0 : n = 0
    · subst n
      simp [weightedThresholdPhaseSum, ha, hb, weightedNormalizedPhaseSum]
    · rw [weightedThresholdPhaseSum, if_pos ha, if_neg hn0,
        weightedThresholdPhaseSum, if_neg hb]
      exact weightedNormalizedPhaseSum_nonneg d n phaseJ hp
        Jmin Jmax q beta0 b hJmin hq (lt_of_not_ge hb)
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
        Jmin Jmax q beta0 a (lt_of_not_ge ha),
      weightedThresholdPhaseSum_of_pos d n phaseJ
        Jmin Jmax q beta0 b (lt_of_not_ge hb)]
    exact weightedNormalizedPhaseSum_mono_beta
      d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 a b hq (lt_of_not_ge ha) hab

theorem weightedThresholdSig_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q) {a b : Real} (hab : a <= b) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n a <=
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b := by
  unfold Sig
  exact Finset.sum_le_sum fun k hk => weightedThresholdPhaseSum_mono_beta
    d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 a b hq hab

theorem weightedThresholdSig_pos
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    0 < Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
  have hzero : 0 < weightedThresholdPhaseSum
      d phaseJ Jmin Jmax q beta0 0 beta := by
    by_cases hbeta : beta <= 0
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_pos rfl]
      exact div_pos (by exact_mod_cast Fintype.card_pos)
        (weightedPhaseSharpConstant_pos d hJmin)
    · rw [weightedThresholdPhaseSum_of_pos d 0 phaseJ
        Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
      unfold weightedNormalizedPhaseSum
      rw [weightedPhaseSum_zero]
      exact div_pos (by exact_mod_cast Fintype.card_pos)
        (weightedPhaseSharpConstant_pos d hJmin)
  unfold Sig
  exact hzero.trans_le (Finset.single_le_sum
    (fun k hk => weightedThresholdPhaseSum_nonneg d k phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq) (Finset.mem_range.mpr hn))

theorem weightedThresholdSig_le_linear
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta <=
      ((Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0) * (n : Real) := by
  unfold Sig
  calc
    (∑ k ∈ Finset.range n,
      weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 k beta) <=
        ∑ _k ∈ Finset.range n, ((Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0) :=
      Finset.sum_le_sum fun k hk => weightedThresholdPhaseSum_le_card_div
        d k phaseJ hJ Jmin Jmax q beta0 beta hJmin hq
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem weightedThresholdSet_nonneg
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin)
    (beta : Real)
    (hmem : beta ∈ thresholdSet (fun b n =>
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    0 <= beta := by
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  let c := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := div_pos (by exact_mod_cast Fintype.card_pos)
    (weightedPhaseSharpConstant_pos d hJmin)
  have hsig : forall n, 1 <= n ->
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta = c := by
    intro n hn
    unfold Sig weightedThresholdPhaseSum
    simp only [if_pos (le_of_lt hbetaNeg)]
    rw [Finset.sum_eq_single 0]
    · simp [c]
    · intro k hk hk0
      simp [hk0]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hn)).elim
  have htend : Tendsto
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat => Real.log c / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [logRatio, hsig n hn]
  have hlimsup : Filter.limsup
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop = 0 := htend.limsup_eq
  change (1 : Real) <= Filter.limsup
    (logRatio (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop at hmem
  rw [hlimsup] at hmem
  norm_num at hmem

theorem weightedThresholdSet_bddBelow
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) :
    BddBelow (thresholdSet (fun b n =>
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) := by
  exact ⟨0, fun beta hmem => weightedThresholdSet_nonneg
    d phaseJ Jmin Jmax q beta0 hJmin beta hmem⟩

theorem weightedThresholdLogRatio_bddAbove
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Filter.IsBoundedUnder (fun x y : Real => x <= y) atTop
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
  let M := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  let C := max 1 M
  have hC : 1 <= C := le_max_left _ _
  have hMC : M <= C := le_max_right _ _
  apply btb_bddAbove_ratio_of_linear
    (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)
    C hC
  · intro n hn
    exact weightedThresholdSig_pos d n (by omega) phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq
  · intro n
    exact (weightedThresholdSig_le_linear d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq).trans
        (mul_le_mul_of_nonneg_right hMC (Nat.cast_nonneg n))

theorem weightedThresholdLogRatio_isCobounded
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Filter.IsCoboundedUnder (fun x y : Real => x <= y) atTop
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
  let c := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := div_pos (by exact_mod_cast Fintype.card_pos)
    (weightedPhaseSharpConstant_pos d hJmin)
  have hdiv : Tendsto (fun n : Nat => Real.log c / Real.log (n : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := logRatio (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
    (x := -1) atTop ?_
  have hev : ∀ᶠ n : Nat in atTop,
      -1 <= Real.log c / Real.log (n : Real) :=
    hdiv.eventually (Ici_mem_nhds (by norm_num : (-1 : Real) < 0))
  filter_upwards [eventually_ge_atTop 2, hev] with n hn hcn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig : c <= Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
    have hzero : weightedThresholdPhaseSum
        d phaseJ Jmin Jmax q beta0 0 beta = c := by
      by_cases hbeta : beta <= 0
      · simp [weightedThresholdPhaseSum, hbeta, c]
      · simp [weightedThresholdPhaseSum, hbeta, weightedNormalizedPhaseSum,
          weightedPhaseSum_zero, c]
    rw [← hzero]
    unfold Sig
    exact Finset.single_le_sum
      (fun k hk => weightedThresholdPhaseSum_nonneg d k phaseJ hJ
        Jmin Jmax q beta0 beta hJmin hq) (Finset.mem_range.mpr (by omega))
  exact hcn.trans ((div_le_div_iff_of_pos_right hlogn).2
    (Real.log_le_log hc hsig))



theorem weightedThresholdSet_mem_of_selectedPhaseSum_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta) :
    beta ∈ thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  have hc := weightedPhaseSharpConstant_pos d
    (Jmax := Jmax) (beta0 := beta0) hJmin
  have hconv := weightedNormalizedPhaseSum_tendsto
    d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta
  have hratio := logRatio_partialSum_tendsto_one hconv (div_pos hTheta hc)
  change 1 <= Filter.limsup (logRatio (fun n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) atTop
  have hsig : (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta) =
      (fun n => Sig
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) := by
    funext n
    unfold Sig
    apply Finset.sum_congr rfl
    intro k hk
    exact weightedThresholdPhaseSum_of_pos
      d k phaseJ Jmin Jmax q beta0 beta hbeta
  rw [hsig]
  unfold Sig
  rw [hratio.limsup_eq]

theorem weightedThresholdSet_nonempty_of_selectedPhaseSum_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta) :
    (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty :=
  ⟨beta, weightedThresholdSet_mem_of_selectedPhaseSum_pos
    d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta hTheta⟩






def weightedSelectedPhaseHighBetaWitness
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e) (q : Real) (hq : 0 < q)
    (beta0 : Real) : Prop :=
  exists betaStar : Real, 0 < betaStar /\ betaStar < beta0 /\
    0 < weightedSelectedPhaseSum d phaseJ hJ q hq betaStar



theorem weightedHighBetaWitness_threshold_member
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    exists betaStar : Real, 0 < betaStar /\ betaStar < beta0 /\
      betaStar ∈ thresholdSet (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  obtain ⟨betaStar, hbetaStar, hstar0, hTheta⟩ := hhigh
  exact ⟨betaStar, hbetaStar, hstar0,
    weightedThresholdSet_mem_of_selectedPhaseSum_pos
      d phaseJ hJ Jmin Jmax q beta0 betaStar
        hJmin hq hbetaStar hTheta⟩


theorem weightedHighBetaWitness_threshold_nonempty
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty := by
  obtain ⟨betaStar, _hbetaStar, _hstar0, hmem⟩ :=
    weightedHighBetaWitness_threshold_member
      d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh
  exact ⟨betaStar, hmem⟩



theorem weightedHighBetaWitness_strict_cutoff
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0 := by
  obtain ⟨betaStar, _hbetaStar, hstar0, hmem⟩ :=
    weightedHighBetaWitness_threshold_member
      d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh
  have hle : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) <=
      betaStar := by
    unfold beta1
    exact csInf_le
      (weightedThresholdSet_bddBelow
        d phaseJ Jmin Jmax q beta0 hJmin) hmem
  exact hle.trans_lt hstar0

theorem weightedThresholdSig_of_pos
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) (hbeta : 0 < beta) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta =
      Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
  unfold Sig
  apply Finset.sum_congr rfl
  intro k hk
  exact weightedThresholdPhaseSum_of_pos
    d k phaseJ Jmin Jmax q beta0 beta hbeta



theorem weightedSelectedPhaseSum_difference_lower
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta' beta : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcrit : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta')
    (hbeta : beta' <= beta) (hupper : beta <= beta0) :
    beta - beta' <=
      weightedSelectedPhaseSum d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0 -
      weightedSelectedPhaseSum d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) beta' /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let f := weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0
  let fp := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0
  let S := Sig f
  have hbeta1nn : 0 <= beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
    unfold beta1
    apply le_csInf hne
    intro x hx
    exact weightedThresholdSet_nonneg
      d phaseJ Jmin Jmax q beta0 hJmin x hx
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hf : forall i x, x ∈ Icc beta' beta ->
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => (Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0 := by
        funext z
        simp [f, weightedNormalizedPhaseSum]
      rw [hconst]
      simpa [fp, weightedNormalizedPhaseSumPrime, weightedPhaseSum] using
        (hasDerivAt_const x ((Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0))
    · exact weightedNormalizedPhaseSum_hasDerivAt
        d i (Nat.one_le_iff_ne_zero.mpr hi) phaseJ hp
          Jmin Jmax q beta0 x hq (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact weightedNormalizedPhaseSum_nonneg d i phaseJ hp
      Jmin Jmax q beta0 x hJmin hq (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Icc beta' beta -> 0 < S i x := by
    intro i x hi hx
    rw [show S i x = Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) i x by
      symm
      simpa [S, f] using weightedThresholdSig_of_pos
        d i phaseJ Jmin Jmax q beta0 x (hbeta'pos.trans_le hx.1)]
    exact weightedThresholdSig_pos d i hi phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Icc beta' beta ->
      ((i : Real) / S i x) * f i x <= fp i x := by
    intro i x hi hx
    exact weightedNormalizedPhaseSum_differential
      d i hi J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q x beta0 hq (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Icc beta' beta ->
      S n beta' <= S (n + 1) x := by
    intro n x hn hx
    have hmono : S n beta' <= S n x := by
      unfold S Sig
      exact Finset.sum_le_sum fun k hk =>
        weightedNormalizedPhaseSum_mono_beta
          d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta' x hq hbeta'pos hx.1
    rw [show S (n + 1) x = S n x + f n x by
      exact IntegrationSubcritical.isc_Sig_succ f n x]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : forall x, x ∈ Icc beta' beta ->
      S 1 x <= (Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
    intro x hx
    simp [S, f, Sig, weightedNormalizedPhaseSum]
  have hTbeta := weightedNormalizedPhaseSum_meanLogTerm_tendsto
    d phaseJ hp Jmin Jmax q beta0 beta hq hbetapos
  have hTbeta' := weightedNormalizedPhaseSum_meanLogTerm_tendsto
    d phaseJ hp Jmin Jmax q beta0 beta' hq hbeta'pos
  have hSigEq : (fun n => S n beta') = (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta') := by
    funext n
    symm
    simpa [S, f] using weightedThresholdSig_of_pos
      d n phaseJ Jmin Jmax q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (logRatio (fun n => S n beta')) := by
    rw [hSigEq]
    exact weightedThresholdLogRatio_isCobounded
      d phaseJ hp Jmin Jmax q beta0 beta' hJmin hq
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (logRatio (fun n => S n beta')) := by
    rw [hSigEq]
    exact weightedThresholdLogRatio_bddAbove
      d phaseJ hp Jmin Jmax q beta0 beta' hJmin hq
  have hm1 : 1 <= limsup (logRatio (fun n => S n beta')) atTop := by
    rw [hSigEq]
    exact one_le_limsup_of_beta1_lt hne
      (fun hab n => weightedThresholdSig_mono_beta
        d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 hq hab)
      (fun x n hn => weightedThresholdSig_pos d n (by omega) phaseJ hp
        Jmin Jmax q beta0 x hJmin hq)
      (fun x => weightedThresholdLogRatio_isCobounded
        d phaseJ hp Jmin Jmax q beta0 x hJmin hq)
      (fun x => weightedThresholdLogRatio_bddAbove
        d phaseJ hp Jmin Jmax q beta0 x hJmin hq)
      hcrit
  exact meanField_lower_of_threshold_rate f fp S beta' beta
    (weightedSelectedPhaseSum d phaseJ hp q
      (zero_lt_one.trans_le hq) beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0)
    (weightedSelectedPhaseSum d phaseJ hp q
      (zero_lt_one.trans_le hq) beta' /
        weightedPhaseSharpConstant d Jmin Jmax beta0)
    ((Fintype.card P : Real) /
      weightedPhaseSharpConstant d Jmin Jmax beta0)
    hbeta hf (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff
      hSmono hS1le hTbeta hTbeta' hcob hbdd hm1



theorem weightedSelectedPhaseSum_meanField_lower
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcrit : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta)
    (hupper : beta <= beta0) :
    weightedPhaseSharpConstant d Jmin Jmax beta0 *
        (beta - beta1 (fun b n => Sig
          (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <=
      weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) beta := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  let c := weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := weightedPhaseSharpConstant_pos d hJmin
  have hnormalized : beta - betaOne <=
      weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta / c := by
    apply meanField_lower_at_threshold
      (f := fun x => weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) x / c)
      (β₁ := betaOne) (β := beta) hcrit
    · intro x hx1 hxb
      exact div_nonneg (weightedSelectedPhaseSum_nonneg
        d phaseJ hp q (zero_lt_one.trans_le hq) x) hc.le
    · intro x hx1 hxb
      exact weightedSelectedPhaseSum_difference_lower
        d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 x beta hq hne hx1 hxb.le hupper
  simpa [betaOne, c, hp, mul_comm] using (le_div_iff₀ hc).mp hnormalized



theorem weightedSelectedPhaseSum_mono_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 a b : Real) (hq : 1 <= q) (ha : 0 < a) (hab : a <= b) :
    weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) a <=
      weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) b := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hc : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 :=
    weightedPhaseSharpConstant_pos d hJmin
  have hTa := weightedNormalizedPhaseSum_tendsto
    d phaseJ hp Jmin Jmax q beta0 a hq ha
  have hTb := weightedNormalizedPhaseSum_tendsto
    d phaseJ hp Jmin Jmax q beta0 b hq (ha.trans_le hab)
  have hle : weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) a /
        weightedPhaseSharpConstant d Jmin Jmax beta0 <=
      weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) b /
        weightedPhaseSharpConstant d Jmin Jmax beta0 :=
    le_of_tendsto_of_tendsto hTa hTb <| Eventually.of_forall fun n =>
      weightedNormalizedPhaseSum_mono_beta
        d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 a b hq ha hab
  exact (div_le_div_iff_of_pos_right hc).mp hle



theorem weightedPhaseSum_subcritical_decay_of_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0) (hdelta : 0 < delta)
    (hleft : 0 < beta - 2 * delta)
    (hlt : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n ->
      weightedPhaseSum d phaseJ q (beta - 2 * delta) n <=
        (Fintype.card P : Real) *
          Real.exp (-(((n : Real) / Q) * delta)) := by
  let f := weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0
  let f' := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0
  let c := weightedPhaseSharpConstant d Jmin Jmax beta0
  let M := (Fintype.card P : Real) / c
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hc : 0 < c := weightedPhaseSharpConstant_pos d hJmin
  have hM : 0 <= M := div_nonneg (Nat.cast_nonneg _) hc.le
  have hinterval : ∀ x, x ∈ Icc (beta - 2 * delta) beta -> 0 < x := by
    intro x hx
    exact hleft.trans_le hx.1
  have hd : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      HasDerivAt (f n) (f' n x) x := by
    intro n x hx
    by_cases hn0 : n = 0
    · subst n
      have hconst : f 0 = fun _ => M := by
        funext z
        simp [f, M, c, weightedThresholdPhaseSum,
          weightedNormalizedPhaseSum]
      rw [hconst]
      simpa [f', weightedNormalizedPhaseSumPrime,
        weightedPhaseSum] using (hasDerivAt_const x M)
    · have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnorm := weightedNormalizedPhaseSum_hasDerivAt
        d n hn phaseJ hp Jmin Jmax q beta0 x hq (hinterval x hx)
      refine hnorm.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (hinterval x hx)] with z hz
      have hz0 : 0 < z := hz
      simp [f, weightedThresholdPhaseSum, not_le.mpr hz0]
  have hfnn : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      0 <= f n x := by
    intro n x hx
    exact weightedThresholdPhaseSum_nonneg d n phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hfM : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      f n x <= M := by
    intro n x hx
    exact weightedThresholdPhaseSum_le_card_div d n phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hfmono : forall k : Nat, forall {y x},
      y ∈ Icc (beta - 2 * delta) beta ->
      x ∈ Icc (beta - 2 * delta) beta -> y <= x -> f k y <= f k x := by
    intro k y x hy hx hyx
    exact weightedThresholdPhaseSum_mono_beta
      d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 y x hq hyx
  have hSpos : forall n, 1 <= n -> forall x,
      x ∈ Icc (beta - 2 * delta) beta -> 0 < Sig f n x := by
    intro n hn x hx
    exact weightedThresholdSig_pos d n hn phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hdiff : forall n : Nat, 1 <= n -> forall x,
      x ∈ Icc (beta - 2 * delta) beta ->
        ((n : Real) / Sig f n x) * f n x <= f' n x := by
    intro n hn x hx
    rw [show Sig f n x = Sig
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n x by
      simpa [f] using weightedThresholdSig_of_pos
        d n phaseJ Jmin Jmax q beta0 x (hinterval x hx)]
    rw [show f n x = weightedNormalizedPhaseSum
        d phaseJ Jmin Jmax q beta0 n x by
      simp [f, weightedThresholdPhaseSum, not_le.mpr (hinterval x hx)]]
    exact weightedNormalizedPhaseSum_differential
      d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q x beta0 hq (hinterval x hx) (hx.2.trans hbeta0)
  have hSbeta : forall n, 2 <= n -> 0 < Sig f n beta := by
    intro n hn
    exact weightedThresholdSig_pos d n (by omega) phaseJ hp
      Jmin Jmax q beta0 beta hJmin hq
  have hbddSet : BddBelow (thresholdSet (fun b n => Sig f n b)) := by
    simpa [f] using weightedThresholdSet_bddBelow
      d phaseJ Jmin Jmax q beta0 hJmin
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (logRatio (fun n => Sig f n beta)) := by
    simpa [f] using weightedThresholdLogRatio_bddAbove
      d phaseJ hp Jmin Jmax q beta0 beta hJmin hq
  obtain ⟨Q, hQ, hdecay⟩ := btb_subcritical_decay_of_threshold
    f f' delta beta M hdelta hM hd hfnn hfM hfmono hSpos hdiff
      hSbeta hbddSet hbdd (by simpa [f] using hlt)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have h := hdecay n hn
  have hpos : 0 < beta - 2 * delta := hleft
  rw [show f n (beta - 2 * delta) =
      weightedPhaseSum d phaseJ q (beta - 2 * delta) n / c by
    simp [f, weightedThresholdPhaseSum, not_le.mpr hpos,
      weightedNormalizedPhaseSum, c]] at h
  have hrhs : M * Real.exp (-(((n : Real) / Q) * delta)) =
      ((Fintype.card P : Real) *
        Real.exp (-(((n : Real) / Q) * delta))) / c := by
    unfold M
    field_simp
  rw [hrhs] at h
  exact (div_le_div_iff_of_pos_right hc).mp h




theorem weightedPhasePhysical_subcritical_decay_of_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0) (hdelta : 0 < delta)
    (hleft : 0 < beta - 2 * delta)
    (hlt : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    exists Q : Real, 0 < Q ∧ forall a : P, forall n : Nat, 2 <= n ->
      ((weightedPhaseFiniteMeasure d n phaseJ a
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e)) a)
          q (beta - 2 * delta) (zero_lt_one.trans_le hq) hleft :
          ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <=
        (Fintype.card P : Real) *
          Real.exp (-((((n : Real) / (3 * Q)) * delta))) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  obtain ⟨Q, hQ, hdecay⟩ := weightedPhaseSum_subcritical_decay_of_threshold
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q delta beta beta0 hq hbeta0 hdelta hleft hlt
  refine ⟨Q, hQ, ?_⟩
  intro a n hn
  let k := n / 2
  have hk : 1 <= k := by dsimp [k]; omega
  have hnk : n <= 3 * k := by dsimp [k]; omega
  have hphysical := weightedPhasePhysical_le_localized_half
    d n hn phaseJ hp a q (beta - 2 * delta) hq hleft
  have hprofileSum : weightedPhaseProfile d phaseJ a q
      (beta - 2 * delta) k <=
      weightedPhaseSum d phaseJ q (beta - 2 * delta) k := by
    unfold weightedPhaseSum
    exact Finset.single_le_sum
      (fun b hb => weightedPhaseProfile_nonneg d phaseJ hp b q
        (beta - 2 * delta) hq hleft k) (Finset.mem_univ a)
  have hloc := hdecay k hk
  have hrate : (n : Real) / (3 * Q) <= (k : Real) / Q := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hQ) hQ]
    have hnkR : (n : Real) <= 3 * (k : Real) := by exact_mod_cast hnk
    nlinarith
  calc
    _ <= weightedPhaseProfile d phaseJ a q (beta - 2 * delta) k := by
      simpa [k] using hphysical
    _ <= weightedPhaseSum d phaseJ q (beta - 2 * delta) k := hprofileSum
    _ <= (Fintype.card P : Real) *
        Real.exp (-(((k : Real) / Q) * delta)) := hloc
    _ <= (Fintype.card P : Real) *
        Real.exp (-(((n : Real) / (3 * Q)) * delta)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith




theorem weightedSelectedPhaseSum_eq_zero_below_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta : Real) (hq : 1 <= q)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0)
    (hbelow : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    weightedSelectedPhaseSum d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta = 0 := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidCut : betaMid <= beta0 := (hmidUpper.trans hcut).le
    obtain ⟨Q, hQ, hdecay⟩ := weightedPhaseSum_subcritical_decay_of_threshold
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q delta betaMid beta0 hq hmidCut hdelta (hleft.symm ▸ hbeta) hmidUpper
    have hconv := weightedPhaseSum_tendsto_selectedPhaseSum
      d phaseJ hp q beta hq hbeta
    have hzero := bcm_expBound_tendsto_zero (Fintype.card P : Real) Q delta hQ hdelta
    have hle : weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero <| by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn
    exact le_antisymm hle (weightedSelectedPhaseSum_nonneg
      d phaseJ hp q (zero_lt_one.trans_le hq) beta)
  · unfold weightedSelectedPhaseSum weightedPhaseThetaProfile
    simp [hbeta]





theorem weightedThreshold_eq_selectedPhaseCritical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0)
    (a : P) :
    sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) a)) =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  have hbeta1nn : 0 <= betaOne := by
    dsimp [betaOne]
    unfold beta1
    apply le_csInf hne
    intro x hx
    exact weightedThresholdSet_nonneg
      d phaseJ Jmin Jmax q beta0 hJmin x hx
  have hbeta0pos : 0 < beta0 := hbeta1nn.trans_lt hcut
  have htransport :=
    FKSharpnessWeightedPhaseClose.covariantWeightedPhasePositivityTransport
      J phase phaseJ (fun e => hJmin.trans_le (hJlo e))
        hsurj hcov q hq
  apply bcm_betaC_eq_threshold _ betaOne
  · intro beta hbeta
    have hsumzero := weightedSelectedPhaseSum_eq_zero_below_threshold
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 beta hq hcut hbeta
    have hnonneg := weightedPhaseThetaProfile_nonneg
      d phaseJ hp q (zero_lt_one.trans_le hq) a beta
    have hle : weightedPhaseThetaProfile d phaseJ hp q
        (zero_lt_one.trans_le hq) a beta <=
        weightedSelectedPhaseSum d phaseJ hp q
          (zero_lt_one.trans_le hq) beta := by
      unfold weightedSelectedPhaseSum
      exact Finset.single_le_sum
        (fun b hb => weightedPhaseThetaProfile_nonneg
          d phaseJ hp q (zero_lt_one.trans_le hq) b beta)
        (Finset.mem_univ a)
    linarith
  · intro beta hbeta
    have hsumpos : 0 < weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta := by
      by_cases hupper : beta <= beta0
      · have hmf := weightedSelectedPhaseSum_meanField_lower
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta hq hne hbeta hupper
        have hgap : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
            (beta - betaOne) := mul_pos
          (weightedPhaseSharpConstant_pos d hJmin) (sub_pos.mpr hbeta)
        exact hgap.trans_le hmf
      · have hmf0 := weightedSelectedPhaseSum_meanField_lower
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta0 hq hne hcut le_rfl
        have hsum0 : 0 < weightedSelectedPhaseSum d phaseJ hp q
            (zero_lt_one.trans_le hq) beta0 := by
          have hgap0 : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
              (beta0 - betaOne) := mul_pos
            (weightedPhaseSharpConstant_pos d hJmin) (sub_pos.mpr hcut)
          exact hgap0.trans_le hmf0
        exact hsum0.trans_le (weightedSelectedPhaseSum_mono_pos
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta0 beta hq hbeta0pos (le_of_lt (lt_of_not_ge hupper)))
    change 0 < ∑ b : P, weightedPhaseThetaProfile d phaseJ hp q
      (zero_lt_one.trans_le hq) b beta at hsumpos
    obtain ⟨b, hb, hbpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun b hb => weightedPhaseThetaProfile_nonneg
        d phaseJ hp q (zero_lt_one.trans_le hq) b beta)).mp hsumpos
    exact (htransport b a beta).mp hbpos



theorem weightedThreshold_eq_selectedPhaseEnvelopeCritical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a beta) = 0} =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let a : P := Classical.choice (inferInstance : Nonempty P)
  exact (FKSharpnessWeightedPhaseClose.covariant_weighted_phase_common_critical
    J phase phaseJ (fun e => hJmin.trans_le (hJlo e))
      hsurj hcov q hq a).trans
    (weightedThreshold_eq_selectedPhaseCritical
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hne hcut a)




theorem weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta0)
    (a : P) :
    sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) a)) =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcut := weightedHighBetaWitness_strict_cutoff
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  exact weightedThreshold_eq_selectedPhaseCritical
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 hq hne hcut a


theorem weightedThreshold_eq_selectedPhaseEnvelopeCritical_of_highBetaWitness
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta0) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a beta) = 0} =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcut := weightedHighBetaWitness_strict_cutoff
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  exact weightedThreshold_eq_selectedPhaseEnvelopeCritical
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 hq hne hcut

end FKSharpnessWeightedThreshold
end OSSS
end StatMech
