/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.KacWardAngleGauge
import Mathlib.Topology.Connected.TotallyDisconnected

open scoped BigOperators
open Set SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager



theorem kw_continuousAt_angleToReal
    {θ : Real.Angle} (hθ : θ ≠ (Real.pi : Real.Angle)) :
    ContinuousAt Real.Angle.toReal θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hcut : θ ≠ ((-Real.pi : ℝ) : Real.Angle) := by
    simpa [Real.Angle.coe_neg, Real.Angle.neg_coe_pi] using hθ
  have hchart := AddCircle.continuousAt_equivIoc
    (p := 2 * Real.pi) (a := -Real.pi) hcut
  exact continuous_subtype_val.continuousAt.comp hchart



theorem kw_continuousOn_principalHalfAnglePhase
    {X D : Type*} [TopologicalSpace X]
    (angle : X → D → Real.Angle) (s : Set X) (dart next : D)
    (hdart : ContinuousOn (fun x ↦ angle x dart) s)
    (hnext : ContinuousOn (fun x ↦ angle x next) s)
    (hnondegenerate : ∀ x ∈ s,
      angle x next - angle x dart ≠ (Real.pi : Real.Angle)) :
    ContinuousOn
      (fun x ↦ kwPrincipalHalfAnglePhase (angle x) dart next) s := by
  intro x hx
  have hdelta : ContinuousWithinAt
      (fun y ↦ angle y next - angle y dart) s x :=
    (hnext x hx).sub (hdart x hx)
  have hreal : ContinuousWithinAt
      (fun y ↦ (angle y next - angle y dart).toReal) s x :=
    (kw_continuousAt_angleToReal
      (hnondegenerate x hx)).comp_continuousWithinAt
        (f := fun y ↦ angle y next - angle y dart) hdelta
  have hcoe : ContinuousWithinAt
      (fun y ↦ ((angle y next - angle y dart).toReal : ℂ)) s x :=
    Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt hreal
  have harg : ContinuousWithinAt
      (fun y ↦ ((angle y next - angle y dart).toReal : ℂ) *
        Complex.I / 2) s x :=
    (hcoe.mul continuousWithinAt_const).div_const 2
  exact Complex.continuous_exp.continuousAt.comp_continuousWithinAt harg


noncomputable def kwLoopPhaseProduct
    {D : Type*} {n : ℕ} [NeZero n]
    (phase : D → D → ℂ) (loop : Fin n → D) : ℂ :=
  ∏ k, phase (loop k) (loop (k + 1))


theorem kwLoopPhaseProduct_branchHalfAngle
    {D : Type*} {n : ℕ} [NeZero n]
    (root : D → ℂ) (branch : D → D → ℂ)
    (hroot : ∀ dart, root dart ≠ 0) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwBranchHalfAnglePhase root branch) loop =
      kwLoopPhaseProduct branch loop := by
  unfold kwLoopPhaseProduct kwBranchHalfAnglePhase
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have hreindex : (∏ k, root (loop (k + 1))) = ∏ k, root (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k ↦ root (loop k))
  rw [hreindex]
  have hprod : (∏ k, root (loop k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hroot (loop k))
  calc
    (∏ k, root (loop k))⁻¹ *
        ((∏ k, branch (loop k) (loop (k + 1))) *
          ∏ k, root (loop k)) =
      ((∏ k, root (loop k))⁻¹ * ∏ k, root (loop k)) *
        ∏ k, branch (loop k) (loop (k + 1)) := by ring
    _ = ∏ k, branch (loop k) (loop (k + 1)) := by
      rw [inv_mul_cancel₀ hprod, one_mul]


theorem kwLoopPhaseProduct_principal_eq_branch
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop =
      kwLoopPhaseProduct (kwPrincipalHalfAngleBranch angle) loop := by
  rw [kwPrincipalHalfAnglePhase_eq_branch]
  exact kwLoopPhaseProduct_branchHalfAngle
    (kwPrincipalHalfAngleRoot angle)
    (kwPrincipalHalfAngleBranch angle)
    (kwPrincipalHalfAngleRoot_ne_zero angle) loop


theorem kwLoopPhaseProduct_principal_sq
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop ^ 2 = 1 := by
  rw [kwLoopPhaseProduct_principal_eq_branch]
  unfold kwLoopPhaseProduct
  rw [pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro k _
  rw [← pow_two, kwPrincipalHalfAngleBranch_sq]

theorem kwLoopPhaseProduct_principal_eq_one_or_neg_one
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : D → Real.Angle) (loop : Fin n → D) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = 1 ∨
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase angle) loop = -1 :=
  sq_eq_one_iff.mp (kwLoopPhaseProduct_principal_sq angle loop)



theorem kwLoopPhaseProduct_eq_of_continuous_sign_homotopy
    {D : Type*} {n : ℕ} [NeZero n]
    (phase : ℝ → D → D → ℂ) (loop : Fin n → D)
    (hcontinuous : ∀ k : Fin n, ContinuousOn
      (fun t ↦ phase t (loop k) (loop (k + 1))) (Icc 0 1))
    (hsign : ∀ t ∈ Icc (0 : ℝ) 1,
      kwLoopPhaseProduct (phase t) loop = 1 ∨
        kwLoopPhaseProduct (phase t) loop = -1) :
    kwLoopPhaseProduct (phase 0) loop =
      kwLoopPhaseProduct (phase 1) loop := by
  let f : ℝ → ℂ := fun t ↦ kwLoopPhaseProduct (phase t) loop
  have hf : ContinuousOn f (Icc 0 1) := by
    dsimp only [f, kwLoopPhaseProduct]
    apply continuousOn_finsetProd
    intro k _
    exact hcontinuous k
  have hmaps : MapsTo f (Icc 0 1) ({1, -1} : Set ℂ) := by
    intro t ht
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hsign t ht
  exact isPreconnected_Icc.constant_of_mapsTo
    (Set.toFinite ({1, -1} : Set ℂ)).isDiscrete hf hmaps
    (by norm_num) (by norm_num)



theorem kwLoopPhaseProduct_principal_homotopy
    {D : Type*} {n : ℕ} [NeZero n]
    (angle : ℝ → D → Real.Angle) (loop : Fin n → D)
    (hcontinuous : ∀ k : Fin n, ContinuousOn
      (fun t ↦ kwPrincipalHalfAnglePhase (angle t)
        (loop k) (loop (k + 1))) (Icc 0 1)) :
    kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 0)) loop =
      kwLoopPhaseProduct (kwPrincipalHalfAnglePhase (angle 1)) loop := by
  apply kwLoopPhaseProduct_eq_of_continuous_sign_homotopy
    (fun t ↦ kwPrincipalHalfAnglePhase (angle t)) loop hcontinuous
  intro t _
  exact kwLoopPhaseProduct_principal_eq_one_or_neg_one (angle t) loop



def kwGraphLoopNonbacktracking
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : Prop :=
  ∀ k, (loop k).snd = (loop (k + 1)).fst ∧
    (loop k).edge ≠ (loop (k + 1)).edge


noncomputable def kwGraphLoopAdjacency
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) : ℂ :=
  ∏ k, if (loop k).snd = (loop (k + 1)).fst ∧
      (loop k).edge ≠ (loop (k + 1)).edge then 1 else 0

theorem kwGraphTransition_one_eq_adjacency_mul_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ) (dart next : G.Dart) :
    kwGraphTransition G (fun _ ↦ 1) phase dart next =
      (if dart.snd = next.fst ∧ dart.edge ≠ next.edge then 1 else 0) *
        phase dart next := by
  by_cases h : dart.snd = next.fst ∧ dart.edge ≠ next.edge
  · simp [kwGraphTransition, h]
  · simp [kwGraphTransition, h]



theorem kwGraphLoopScalar_eq_adjacency_mul_phaseProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwGraphLoopScalar G phase loop =
      kwGraphLoopAdjacency G loop * kwLoopPhaseProduct phase loop := by
  unfold kwGraphLoopScalar kwGraphLoopAdjacency kwLoopPhaseProduct
  rw [Finset.prod_congr rfl (fun k _ ↦
    kwGraphTransition_one_eq_adjacency_mul_phase
      G phase (loop k) (loop (k + 1))),
    Finset.prod_mul_distrib]

theorem kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hvalid : ¬kwGraphLoopNonbacktracking G loop) :
    kwGraphLoopAdjacency G loop = 0 := by
  classical
  simp only [kwGraphLoopNonbacktracking, not_forall] at hvalid
  obtain ⟨k, hk⟩ := hvalid
  unfold kwGraphLoopAdjacency
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hk]

theorem kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase₀ phase₁ : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart)
    (hphase : kwGraphLoopNonbacktracking G loop →
      kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
    kwGraphLoopScalar G phase₀ loop = kwGraphLoopScalar G phase₁ loop := by
  rw [kwGraphLoopScalar_eq_adjacency_mul_phaseProduct,
    kwGraphLoopScalar_eq_adjacency_mul_phaseProduct]
  by_cases hvalid : kwGraphLoopNonbacktracking G loop
  · rw [hphase hvalid]
  · rw [kwGraphLoopAdjacency_eq_zero_of_not_nonbacktracking G loop hvalid,
      zero_mul, zero_mul]



theorem kwGraphFormalRoot_eq_of_valid_phaseProduct_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase₀ phase₁ : G.Dart → G.Dart → ℂ)
    (hphase : ∀ {n : ℕ} [NeZero n] (loop : Fin n → G.Dart),
      kwGraphLoopNonbacktracking G loop →
        kwLoopPhaseProduct phase₀ loop = kwLoopPhaseProduct phase₁ loop) :
    kwGraphFormalRoot G phase₀ = kwGraphFormalRoot G phase₁ := by
  have hlog : kwGraphFormalLog G phase₀ = kwGraphFormalLog G phase₁ := by
    ext m
    change kwGraphFormalLogCoeff G phase₀ m =
      kwGraphFormalLogCoeff G phase₁ m
    unfold kwGraphFormalLogCoeff
    apply congrArg (fun z : ℂ ↦ -z / 2)
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    apply Finset.sum_congr rfl
    intro loop _
    by_cases heq : kwGraphLoopExponent G loop = m
    · simp only [if_pos heq]
      exact kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
        G phase₀ phase₁ loop (hphase loop)
    · simp [heq]
  unfold kwGraphFormalRoot
  rw [hlog]



theorem kwGraphFormalRoot_principalAngle_homotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : ℝ → G.Dart → Real.Angle)
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1)) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
  symm
  apply kwGraphFormalRoot_eq_of_valid_phaseProduct_eq G
  intro n hn loop hvalid
  apply kwLoopPhaseProduct_principal_homotopy angle loop
  intro k
  exact hcontinuous (loop k) (loop (k + 1)) (hvalid k)




theorem kwGraphFormalRoot_principalAngle_nondegenerateHomotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (angle : ℝ → G.Dart → Real.Angle)
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
    kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1)) =
      kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 0)) := by
  apply kwGraphFormalRoot_principalAngle_homotopy G angle
  intro dart next hvalid
  exact kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1)
    dart next (hangle dart) (hangle next)
      (fun t ht ↦ hnondegenerate t ht dart next hvalid)



theorem kw_detWalkRoot_principalAngle_homotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle : ℝ → G.Dart → Real.Angle)
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1)) :
    ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 1))) =
      ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 0))) := by
  apply ons_detWalkRoot_eq_of_loopWeight_eq
  intro n loop
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor]
  congr 1
  apply kwGraphLoopScalar_eq_of_valid_phaseProduct_eq
  intro hvalid
  symm
  apply kwLoopPhaseProduct_principal_homotopy angle loop
  intro k
  exact hcontinuous (loop k) (loop (k + 1)) (hvalid k)

theorem kw_detWalkRoot_principalAngle_nondegenerateHomotopy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (angle : ℝ → G.Dart → Real.Angle)
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle)) :
    ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 1))) =
      ons_detWalkRoot (kwGraphTransition G weight
        (kwPrincipalHalfAnglePhase (angle 0))) := by
  apply kw_detWalkRoot_principalAngle_homotopy G weight angle
  intro dart next hvalid
  exact kw_continuousOn_principalHalfAnglePhase angle (Icc 0 1)
    dart next (hangle dart) (hangle next)
      (fun t ht ↦ hnondegenerate t ht dart next hvalid)




theorem kw_principalAngleHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (angle : ℝ → G.Dart → Real.Angle)
    (hstart : kwPrincipalHalfAnglePhase (angle 0) =
      kwPhaseGauge gauge (fun dart next ↦
        ons_turnW omega (direction next) (direction dart)))
    (hcontinuous : ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        ContinuousOn (fun t ↦ kwPrincipalHalfAnglePhase (angle t) dart next)
          (Icc 0 1))
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
  rw [kwGraphFormalRoot_principalAngle_homotopy G angle hcontinuous,
    hstart]
  exact kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq gauge hgauge
      edge hedge m hrepeated




theorem kw_principalAngleNondegenerateHomotopy_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (gauge : G.Dart → ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (angle : ℝ → G.Dart → Real.Angle)
    (hstart : kwPrincipalHalfAnglePhase (angle 0) =
      kwPhaseGauge gauge (fun dart next ↦
        ons_turnW omega (direction next) (direction dart)))
    (hangle : ∀ dart,
      ContinuousOn (fun t ↦ angle t dart) (Icc 0 1))
    (hnondegenerate : ∀ t ∈ Icc (0 : ℝ) 1, ∀ dart next,
      dart.snd = next.fst ∧ dart.edge ≠ next.edge →
        angle t next - angle t dart ≠ (Real.pi : Real.Angle))
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (kwPrincipalHalfAnglePhase (angle 1))) = 0 := by
  rw [kwGraphFormalRoot_principalAngle_nondegenerateHomotopy
    G angle hangle hnondegenerate, hstart]
  exact kw_rectilinearGraph_gaugedFormalRoot_coeff_eq_zero_of_repeated_edge
    G direction hdirection omega homega homega_sq gauge hgauge
      edge hedge m hrepeated

end StatMech.FrontierA
