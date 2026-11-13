/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.KacWardRectilinearFormal

open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwPhaseGauge
    {D : Type*} (gauge : D → ℂ) (phase : D → D → ℂ) : D → D → ℂ :=
  fun dart next ↦ (gauge dart)⁻¹ * phase dart next * gauge next


theorem kwGraphTransition_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) :
    kwGraphTransition G weight (kwPhaseGauge gauge phase) =
      kwGaugeConjugate gauge (kwGraphTransition G weight phase) := by
  ext dart next
  by_cases hstep : dart.snd = next.fst ∧ dart.edge ≠ next.edge
  · simp [kwGraphTransition, kwPhaseGauge, kwGaugeConjugate, hstep]
    ring
  · simp [kwGraphTransition, kwGaugeConjugate, hstep]



theorem kwGraphLoopScalar_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G (kwPhaseGauge gauge phase) loop =
      kwGraphLoopScalar G phase loop := by
  change ons_loopWeight
      (kwGraphTransition G (fun _ ↦ 1) (kwPhaseGauge gauge phase)) loop =
    ons_loopWeight (kwGraphTransition G (fun _ ↦ 1) phase) loop
  rw [kwGraphTransition_phaseGauge]
  exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop



theorem kwGraphFormalLog_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0) :
    kwGraphFormalLog G (kwPhaseGauge gauge phase) =
      kwGraphFormalLog G phase := by
  ext m
  change kwGraphFormalLogCoeff G (kwPhaseGauge gauge phase) m =
    kwGraphFormalLogCoeff G phase m
  unfold kwGraphFormalLogCoeff
  apply congrArg (fun z : ℂ ↦ -z / 2)
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  apply Finset.sum_congr rfl
  intro loop _
  by_cases heq : kwGraphLoopExponent G loop = m
  · simp only [if_pos heq]
    exact kwGraphLoopScalar_phaseGauge G phase gauge hgauge loop
  · simp [heq]



theorem kwGraphFormalRoot_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (gauge : G.Dart → ℂ)
    (hgauge : ∀ dart, gauge dart ≠ 0) :
    kwGraphFormalRoot G (kwPhaseGauge gauge phase) =
      kwGraphFormalRoot G phase := by
  unfold kwGraphFormalRoot
  rw [kwGraphFormalLog_phaseGauge G phase gauge hgauge]


theorem kw_detWalkRoot_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0) :
    ons_detWalkRoot
        (kwGraphTransition G weight (kwPhaseGauge gauge phase)) =
      ons_detWalkRoot (kwGraphTransition G weight phase) := by
  rw [kwGraphTransition_phaseGauge]
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop



theorem kw_det_one_sub_phaseGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0) :
    (1 - kwGraphTransition G weight (kwPhaseGauge gauge phase)).det =
      (1 - kwGraphTransition G weight phase).det := by
  rw [kwGraphTransition_phaseGauge]
  exact kw_det_one_sub_gaugeConjugate gauge _ hgauge



noncomputable def kwBranchHalfAnglePhase
    {D : Type*} (root : D → ℂ) (branch : D → D → ℂ) : D → D → ℂ :=
  fun dart next ↦ (root dart)⁻¹ * branch dart next * root next


noncomputable def kwRealHalfAngleRoot
    {D : Type*} (angle : D → ℝ) : D → ℂ :=
  fun dart ↦ Complex.exp (((angle dart : ℂ) * Complex.I) / 2)

theorem kwRealHalfAngleRoot_ne_zero
    {D : Type*} (angle : D → ℝ) (dart : D) :
    kwRealHalfAngleRoot angle dart ≠ 0 :=
  Complex.exp_ne_zero _



noncomputable def kwPrincipalHalfAnglePhase
    {D : Type*} (angle : D → Real.Angle) : D → D → ℂ :=
  fun dart next ↦ Complex.exp
    (((angle next - angle dart).toReal : ℂ) * Complex.I / 2)



noncomputable def kwPrincipalHalfAngleRoot
    {D : Type*} (angle : D → Real.Angle) : D → ℂ :=
  kwRealHalfAngleRoot (fun dart ↦ (angle dart).toReal)

theorem kwPrincipalHalfAngleRoot_ne_zero
    {D : Type*} (angle : D → Real.Angle) (dart : D) :
    kwPrincipalHalfAngleRoot angle dart ≠ 0 :=
  kwRealHalfAngleRoot_ne_zero _ _

theorem kwPrincipalHalfAngleRoot_sq
    {D : Type*} (angle : D → Real.Angle) (dart : D) :
    kwPrincipalHalfAngleRoot angle dart ^ 2 =
      Complex.exp (((angle dart).toReal : ℂ) * Complex.I) := by
  unfold kwPrincipalHalfAngleRoot kwRealHalfAngleRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem kwPrincipalHalfAnglePhase_sq
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAnglePhase angle dart next ^ 2 =
      Complex.exp
        (((angle next - angle dart).toReal : ℂ) * Complex.I) := by
  unfold kwPrincipalHalfAnglePhase
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring



noncomputable def kwPrincipalHalfAngleBranch
    {D : Type*} (angle : D → Real.Angle) : D → D → ℂ :=
  fun dart next ↦ kwPrincipalHalfAngleRoot angle dart *
    kwPrincipalHalfAnglePhase angle dart next *
      (kwPrincipalHalfAngleRoot angle next)⁻¹



theorem kwPrincipalHalfAngleBranch_sq
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAngleBranch angle dart next ^ 2 = 1 := by
  let a : ℝ := (angle dart).toReal
  let delta : ℝ := (angle next - angle dart).toReal
  let b : ℝ := (angle next).toReal
  have hxAngle : ((a + delta - b : ℝ) : Real.Angle) = 0 := by
    dsimp only [a, delta, b]
    simp only [Real.Angle.coe_sub, Real.Angle.coe_add,
      Real.Angle.coe_toReal]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hxAngle
  have hexp : Complex.exp (((a + delta - b : ℝ) : ℂ) * Complex.I) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨k, ?_⟩
    rw [← hk]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  unfold kwPrincipalHalfAngleBranch
  rw [pow_two]
  calc
    (kwPrincipalHalfAngleRoot angle dart *
          kwPrincipalHalfAnglePhase angle dart next *
          (kwPrincipalHalfAngleRoot angle next)⁻¹) *
        (kwPrincipalHalfAngleRoot angle dart *
          kwPrincipalHalfAnglePhase angle dart next *
          (kwPrincipalHalfAngleRoot angle next)⁻¹) =
      kwPrincipalHalfAngleRoot angle dart ^ 2 *
        kwPrincipalHalfAnglePhase angle dart next ^ 2 *
        (kwPrincipalHalfAngleRoot angle next ^ 2)⁻¹ := by ring
    _ = Complex.exp ((a : ℂ) * Complex.I) *
        Complex.exp ((delta : ℂ) * Complex.I) *
        (Complex.exp ((b : ℂ) * Complex.I))⁻¹ := by
      rw [kwPrincipalHalfAngleRoot_sq,
        kwPrincipalHalfAnglePhase_sq,
        kwPrincipalHalfAngleRoot_sq]
    _ = Complex.exp (((a + delta - b : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = 1 := hexp

theorem kwPrincipalHalfAngleBranch_eq_one_or_neg_one
    {D : Type*} (angle : D → Real.Angle) (dart next : D) :
    kwPrincipalHalfAngleBranch angle dart next = 1 ∨
      kwPrincipalHalfAngleBranch angle dart next = -1 :=
  sq_eq_one_iff.mp (kwPrincipalHalfAngleBranch_sq angle dart next)



theorem kwPrincipalHalfAnglePhase_eq_branch
    {D : Type*} (angle : D → Real.Angle) :
    kwPrincipalHalfAnglePhase angle =
      kwBranchHalfAnglePhase (kwPrincipalHalfAngleRoot angle)
        (kwPrincipalHalfAngleBranch angle) := by
  funext dart next
  simp only [kwBranchHalfAnglePhase, kwPrincipalHalfAngleBranch]
  field_simp [kwPrincipalHalfAngleRoot_ne_zero angle dart,
    kwPrincipalHalfAngleRoot_ne_zero angle next]



theorem kwBranchHalfAnglePhase_eq_phaseGauge
    {D : Type*} (root₀ root₁ : D → ℂ) (branch : D → D → ℂ)
    (hroot₀ : ∀ dart, root₀ dart ≠ 0)
    (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
    kwBranchHalfAnglePhase root₁ branch =
      kwPhaseGauge (fun dart ↦ (root₀ dart)⁻¹ * root₁ dart)
        (kwBranchHalfAnglePhase root₀ branch) := by
  funext dart next
  simp only [kwBranchHalfAnglePhase, kwPhaseGauge]
  field_simp [hroot₀ dart, hroot₀ next, hroot₁ dart, hroot₁ next]



theorem kwGraphFormalRoot_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root₀ root₁ : G.Dart → ℂ) (branch : G.Dart → G.Dart → ℂ)
    (hroot₀ : ∀ dart, root₀ dart ≠ 0)
    (hroot₁ : ∀ dart, root₁ dart ≠ 0) :
    kwGraphFormalRoot G (kwBranchHalfAnglePhase root₁ branch) =
      kwGraphFormalRoot G (kwBranchHalfAnglePhase root₀ branch) := by
  rw [kwBranchHalfAnglePhase_eq_phaseGauge root₀ root₁ branch
    hroot₀ hroot₁]
  apply kwGraphFormalRoot_phaseGauge
  intro dart
  exact mul_ne_zero (inv_ne_zero (hroot₀ dart)) (hroot₁ dart)



theorem kwGraphFormalRoot_fixedBranch_family
    {V T : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (root : T → G.Dart → ℂ) (branch : G.Dart → G.Dart → ℂ)
    (hroot : ∀ t dart, root t dart ≠ 0) (s t : T) :
    kwGraphFormalRoot G (kwBranchHalfAnglePhase (root t) branch) =
      kwGraphFormalRoot G (kwBranchHalfAnglePhase (root s) branch) :=
  kwGraphFormalRoot_fixedBranch G (root s) (root t) branch
    (hroot s) (hroot t)



theorem kwGraphFormalRoot_realAngle_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle₀ angle₁ : G.Dart → ℝ)
    (branch : G.Dart → G.Dart → ℂ) :
    kwGraphFormalRoot G
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch) =
      kwGraphFormalRoot G
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch) :=
  kwGraphFormalRoot_fixedBranch G _ _ branch
    (kwRealHalfAngleRoot_ne_zero angle₀)
    (kwRealHalfAngleRoot_ne_zero angle₁)



theorem kw_det_one_sub_realAngle_fixedBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle₀ angle₁ : G.Dart → ℝ)
    (branch : G.Dart → G.Dart → ℂ) :
    (1 - kwGraphTransition G weight
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₁) branch)).det =
      (1 - kwGraphTransition G weight
        (kwBranchHalfAnglePhase (kwRealHalfAngleRoot angle₀) branch)).det := by
  rw [kwBranchHalfAnglePhase_eq_phaseGauge
    (kwRealHalfAngleRoot angle₀) (kwRealHalfAngleRoot angle₁) branch
    (kwRealHalfAngleRoot_ne_zero angle₀)
    (kwRealHalfAngleRoot_ne_zero angle₁)]
  apply kw_det_one_sub_phaseGauge
  intro dart
  exact mul_ne_zero
    (inv_ne_zero (kwRealHalfAngleRoot_ne_zero angle₀ dart))
    (kwRealHalfAngleRoot_ne_zero angle₁ dart)



theorem kwGraphFormalRoot_principalAngle_sameBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle₀ angle₁ : G.Dart → Real.Angle)
    (hbranch : kwPrincipalHalfAngleBranch angle₁ =
      kwPrincipalHalfAngleBranch angle₀) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₁) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase angle₀) := by
  rw [kwPrincipalHalfAnglePhase_eq_branch angle₁,
    kwPrincipalHalfAnglePhase_eq_branch angle₀, hbranch]
  exact kwGraphFormalRoot_fixedBranch G _ _ _
    (kwPrincipalHalfAngleRoot_ne_zero angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₁)



theorem kw_det_one_sub_principalAngle_sameBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle₀ angle₁ : G.Dart → Real.Angle)
    (hbranch : kwPrincipalHalfAngleBranch angle₁ =
      kwPrincipalHalfAngleBranch angle₀) :
    (1 - kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase angle₁)).det =
      (1 - kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase angle₀)).det := by
  rw [kwPrincipalHalfAnglePhase_eq_branch angle₁,
    kwPrincipalHalfAnglePhase_eq_branch angle₀, hbranch]
  rw [kwBranchHalfAnglePhase_eq_phaseGauge
    (kwPrincipalHalfAngleRoot angle₀)
    (kwPrincipalHalfAngleRoot angle₁)
    (kwPrincipalHalfAngleBranch angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₀)
    (kwPrincipalHalfAngleRoot_ne_zero angle₁)]
  apply kw_det_one_sub_phaseGauge
  intro dart
  exact mul_ne_zero
    (inv_ne_zero (kwPrincipalHalfAngleRoot_ne_zero angle₀ dart))
    (kwPrincipalHalfAngleRoot_ne_zero angle₁ dart)



theorem kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G
        (kwPhaseGauge gauge (fun dart next ↦
          ons_turnW omega (direction next) (direction dart)))) = 0 := by
  rw [kwGraphFormalRoot_phaseGauge G _ gauge hgauge]
  exact kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq edge hedge m hrepeated

end StatMech.FrontierA
