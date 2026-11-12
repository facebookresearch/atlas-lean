/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFiniteRoots

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem tendsto_sixVertexThetaQuadraticDenominator :
    Tendsto (fun c : Real => c ^ 2 - 4) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 <= c := le_trans (le_max_left _ _) hc
    have hcb : b <= c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-4) hsq)

private theorem sixVertexTheta_ratio_abs_le
    {c x y : Real} (hc : 2 < c) :
    abs ((Real.sin x - Real.sin y) /
        sixVertexThetaDenominator c x y) <= 2 / (c ^ 2 - 4) := by
  have hbase : 0 < c ^ 2 - 4 := by nlinarith
  have hden : c ^ 2 - 4 <= sixVertexThetaDenominator c x y := by
    have hx := Real.neg_one_le_cos x
    have hy := Real.neg_one_le_cos y
    unfold sixVertexThetaDenominator sixVertexDelta
    nlinarith
  have hdenpos : 0 < sixVertexThetaDenominator c x y :=
    sixVertexThetaDenominator_pos hc x y
  have hnum : abs (Real.sin x - Real.sin y) <= 2 := by
    calc
      abs (Real.sin x - Real.sin y) <=
          abs (Real.sin x) + abs (Real.sin y) := abs_sub _ _
      _ <= 2 := by
        nlinarith [Real.abs_sin_le_one x, Real.abs_sin_le_one y]
  rw [abs_div, abs_of_pos hdenpos]
  exact (div_le_div_iff₀ hdenpos hbase).2 (by nlinarith)



theorem tendsto_sixVertexTheta_sub_linear_atTop (x y : Real -> Real) :
    Tendsto
      (fun c => sixVertexTheta c (x c) (y c) - (y c - x c))
      atTop (nhds 0) := by
  have hbound : Tendsto (fun c : Real => 2 / (c ^ 2 - 4))
      atTop (nhds 0) :=
    tendsto_sixVertexThetaQuadraticDenominator.const_div_atTop 2
  have hratio : Tendsto
      (fun c => (Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun c => norm_nonneg _)
    · filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
      change abs ((Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c)) <= 2 / (c ^ 2 - 4)
      exact sixVertexTheta_ratio_abs_le (x := x c) (y := y c) hc
    · exact hbound
  have harctan : Tendsto
      (fun c => Real.arctan
        ((Real.sin (x c) - Real.sin (y c)) /
          sixVertexThetaDenominator c (x c) (y c))) atTop (nhds 0) := by
    simpa using Real.continuousAt_arctan.tendsto.comp hratio
  have htwo := (tendsto_const_nhds.mul harctan :
    Tendsto (fun c => 2 * Real.arctan
      ((Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c))) atTop (nhds (2 * 0)))
  simpa [sixVertexTheta] using htwo



def sixVertexHalfFilledBetheRootAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) (c : Real) : Real :=
  if hc : 2 < c then sixVertexHalfFilledBetheRoots hc k j else 0

theorem sixVertexHalfFilledBetheRootAt_eq
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledBetheRootAt k j c =
      sixVertexHalfFilledBetheRoots hc k j := by
  simp only [sixVertexHalfFilledBetheRootAt, dif_pos hc]


def sixVertexHalfFilledLimitingRoot (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) : Real :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j) /
    (((k + 1) + (k + 1) : Nat) : Real)


def sixVertexHalfFilledLimitingPhase (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) : Complex :=
  sixVertexBethePhase (sixVertexHalfFilledLimitingRoot k j)

theorem sixVertexHalfFilledLimitingRoot_mem_Ioo (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledLimitingRoot k j ∈ Set.Ioo (-Real.pi) Real.pi := by
  let n : Nat := (k + 1) + (k + 1)
  have hn : (0 : Real) < n := by positivity
  have hj0 : (0 : Real) <= j.val := by positivity
  have hjlt : (j.val : Real) < n := by exact_mod_cast j.isLt
  have hjstep : (j.val : Real) + 1 <= n := by
    exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hIlower : -(n : Real) < 2 * sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [n] at hn hjlt hjstep ⊢
    nlinarith
  have hIupper : 2 * sixVertexCentralQuantumNumber j < (n : Real) := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [n] at hn hjlt ⊢
    nlinarith
  change -Real.pi <
      (2 * Real.pi * sixVertexCentralQuantumNumber j) / (n : Real) ∧
    (2 * Real.pi * sixVertexCentralQuantumNumber j) / (n : Real) < Real.pi
  constructor
  · rw [lt_div_iff₀ hn]
    have h := mul_lt_mul_of_pos_left hIlower Real.pi_pos
    nlinarith
  · rw [div_lt_iff₀ hn]
    have h := mul_lt_mul_of_pos_left hIupper Real.pi_pos
    nlinarith


theorem sixVertexHalfFilledLimitingPhase_injective (k : Nat) :
    Function.Injective (sixVertexHalfFilledLimitingPhase k) := by
  intro i j hij
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexHalfFilledLimitingRoot_mem_Ioo k i)
    (sixVertexHalfFilledLimitingRoot_mem_Ioo k j)
    hij
  have hn : (0 : Real) < (((k + 1) + (k + 1) : Nat) : Real) := by
    positivity
  have hquantum : sixVertexCentralQuantumNumber i =
      sixVertexCentralQuantumNumber j := by
    unfold sixVertexHalfFilledLimitingRoot at hroot
    field_simp [hn.ne', Real.pi_ne_zero] at hroot
    linarith
  exact (strictMono_sixVertexCentralQuantumNumber
    ((k + 1) + (k + 1))).injective hquantum

private theorem sixVertexHalfFilledBetheRootAt_equation
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    (sixVertexFourWidth 0 k : Real) *
        sixVertexHalfFilledBetheRootAt k j c =
      2 * Real.pi * sixVertexCentralQuantumNumber j -
        ∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRootAt k j c)
          (sixVertexHalfFilledBetheRootAt k l c) := by
  simpa only [sixVertexHalfFilledBetheRootAt_eq hc] using
    sixVertexHalfFilledBetheRoots_is_solution hc k j

private theorem sixVertexHalfFilledBetheRootAt_sum_eq_zero
    {c : Real} (hc : 2 < c) (k : Nat) :
    ∑ l, sixVertexHalfFilledBetheRootAt k l c = 0 := by
  simpa only [sixVertexHalfFilledBetheRootAt_eq hc] using
    (sixVertexHalfFilledBetheRoots_is_solution hc k).sum_eq_zero
      (sixVertexFourWidth_pos 0 k)

private def sixVertexHalfFilledBetheRootError (k : Nat)
    (j l : Fin ((k + 1) + (k + 1))) (c : Real) : Real :=
  sixVertexTheta c
      (sixVertexHalfFilledBetheRootAt k j c)
      (sixVertexHalfFilledBetheRootAt k l c) -
    (sixVertexHalfFilledBetheRootAt k l c -
      sixVertexHalfFilledBetheRootAt k j c)

private theorem tendsto_sixVertexHalfFilledBetheRootError
    (k : Nat) (j l : Fin ((k + 1) + (k + 1))) :
    Tendsto (sixVertexHalfFilledBetheRootError k j l) atTop (nhds 0) := by
  exact tendsto_sixVertexTheta_sub_linear_atTop
    (sixVertexHalfFilledBetheRootAt k j)
    (sixVertexHalfFilledBetheRootAt k l)

private theorem tendsto_sixVertexHalfFilledBetheRootError_sum
    (k : Nat) (j : Fin ((k + 1) + (k + 1))) :
    Tendsto (fun c => ∑ l, sixVertexHalfFilledBetheRootError k j l c)
      atTop (nhds 0) := by
  simpa using tendsto_finsetSum Finset.univ
    (fun l _ => tendsto_sixVertexHalfFilledBetheRootError k j l)

private theorem sixVertexHalfFilledBetheRootAt_eq_quantum_sub_error
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledBetheRootAt k j c =
      (2 * Real.pi * sixVertexCentralQuantumNumber j -
          ∑ l, sixVertexHalfFilledBetheRootError k j l c) /
        (((k + 1) + (k + 1) : Nat) : Real) := by
  have heq := sixVertexHalfFilledBetheRootAt_equation hc k j
  have hsum := sixVertexHalfFilledBetheRootAt_sum_eq_zero hc k
  have hn : (0 : Real) < (((k + 1) + (k + 1) : Nat) : Real) := by positivity
  have herr :
      (∑ l, sixVertexHalfFilledBetheRootError k j l c) =
        (∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRootAt k j c)
          (sixVertexHalfFilledBetheRootAt k l c)) +
        (((k + 1) + (k + 1) : Nat) : Real) *
          sixVertexHalfFilledBetheRootAt k j c := by
    unfold sixVertexHalfFilledBetheRootError
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hwidth :
      (sixVertexFourWidth 0 k : Real) =
        2 * (((k + 1) + (k + 1) : Nat) : Real) := by
    unfold sixVertexFourWidth
    push_cast
    ring
  rw [hwidth] at heq
  rw [herr, eq_div_iff hn.ne']
  linarith [heq]




theorem tendsto_sixVertexHalfFilledBetheRootAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    Tendsto (sixVertexHalfFilledBetheRootAt k j) atTop
      (nhds (sixVertexHalfFilledLimitingRoot k j)) := by
  have herror := tendsto_sixVertexHalfFilledBetheRootError_sum k j
  have hformula : (fun c => sixVertexHalfFilledBetheRootAt k j c) =ᶠ[atTop]
      fun c =>
        (2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ l, sixVertexHalfFilledBetheRootError k j l c) /
          (((k + 1) + (k + 1) : Nat) : Real) := by
    filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
    exact sixVertexHalfFilledBetheRootAt_eq_quantum_sub_error hc k j
  apply Tendsto.congr' hformula.symm
  simpa [sixVertexHalfFilledLimitingRoot] using
    (tendsto_const_nhds.sub herror).div_const
      ((((k + 1) + (k + 1) : Nat) : Real))


theorem tendsto_sixVertexHalfFilledBethePhaseAt (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    Tendsto
      (fun c => sixVertexBethePhase
        (sixVertexHalfFilledBetheRootAt k j c)) atTop
      (nhds (sixVertexHalfFilledLimitingPhase k j)) := by
  have hcontinuous : Continuous (fun p : Real => sixVertexBethePhase p) := by
    unfold sixVertexBethePhase
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp
    (tendsto_sixVertexHalfFilledBetheRootAt k j)

end

end StatMech.FrontierD
