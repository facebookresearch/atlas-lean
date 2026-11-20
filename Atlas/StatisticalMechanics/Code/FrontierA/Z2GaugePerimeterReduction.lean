/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.Z2GaugeThermodynamicReduction
import Code.FK.TwoPoint
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open scoped BigOperators

namespace StatMech.FrontierA

noncomputable section




def finiteEventMass {E : Type*} [Fintype E] [DecidableEq E]
    (pi : ConfigSpace E -> Real) (A : Set (ConfigSpace E)) : Real :=
  ∑ omega, pi omega * A.indicator (fun _ => (1 : Real)) omega

theorem finiteEventMass_nonneg {E : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real} (hpi : 0 <= pi)
    (A : Set (ConfigSpace E)) :
    0 <= finiteEventMass pi A := by
  unfold finiteEventMass
  apply Finset.sum_nonneg
  intro omega _
  exact mul_nonneg (hpi omega) (indicator_nonneg' A omega)



theorem fkg_inequality_decreasing_events
    {E : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real}
    (hpi : 0 <= pi) (hnorm : ∑ omega, pi omega = 1)
    (hlattice : FKGLatticeCondition pi)
    {A B : Set (ConfigSpace E)}
    (hA : IsDecreasing A) (hB : IsDecreasing B) :
    finiteEventMass pi A * finiteEventMass pi B <=
      finiteEventMass pi (A ∩ B) := by
  let f : ConfigSpace E -> Real :=
    A.indicator (fun _ => (1 : Real))
  let g : ConfigSpace E -> Real :=
    B.indicator (fun _ => (1 : Real))
  have hfanti : Antitone f := by
    intro omega omega' homega
    by_cases hmem : omega ∈ A
    · by_cases hmem' : omega' ∈ A <;>
        simp [f, hmem, hmem']
    · have hmem' : omega' ∉ A := fun homega' => hmem (hA homega homega')
      simp [f, hmem, hmem']
  have hganti : Antitone g := by
    intro omega omega' homega
    by_cases hmem : omega ∈ B
    · by_cases hmem' : omega' ∈ B <;>
        simp [g, hmem, hmem']
    · have hmem' : omega' ∉ B := fun homega' => hmem (hB homega homega')
      simp [g, hmem, hmem']
  have hfmono : Monotone (fun omega => -f omega) := by
    intro omega omega' homega
    exact neg_le_neg (hfanti homega)
  have hgmono : Monotone (fun omega => -g omega) := by
    intro omega omega' homega
    exact neg_le_neg (hganti homega)
  have h := fkg_inequality hpi hnorm hlattice hfmono hgmono
  have hAB : (A ∩ B).indicator (fun _ => (1 : Real)) =
      fun omega => f omega * g omega := by
    funext omega
    by_cases ha : omega ∈ A <;> by_cases hb : omega ∈ B <;>
      simp [f, g, Set.indicator, ha, hb]
  unfold finiteEventMass
  rw [hAB]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg] using h



def finiteEventInter {E I : Type*} (s : Finset I)
    (A : I -> Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {omega | forall i, i ∈ s -> omega ∈ A i}

theorem finiteEventInter_decreasing
    {E I : Type*} {s : Finset I} {A : I -> Set (ConfigSpace E)}
    (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
    IsDecreasing (finiteEventInter s A) := by
  intro omega omega' homega hmem i hi
  exact hA i hi homega (hmem i hi)




theorem fkg_inequality_finite_decreasing_events
    {E I : Type*} [Fintype E] [DecidableEq E]
    {pi : ConfigSpace E -> Real}
    (hpi : 0 <= pi) (hnorm : ∑ omega, pi omega = 1)
    (hlattice : FKGLatticeCondition pi)
    (s : Finset I) (A : I -> Set (ConfigSpace E))
    (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
    (∏ i ∈ s, finiteEventMass pi (A i)) <=
      finiteEventMass pi (finiteEventInter s A) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [finiteEventMass, finiteEventInter, hnorm]
  | @insert a s ha ih =>
      have ha_dec : IsDecreasing (A a) := hA a (Finset.mem_insert_self a s)
      have hs_dec : IsDecreasing (finiteEventInter s A) :=
        finiteEventInter_decreasing (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      have hind := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      have hleft : 0 <= finiteEventMass pi (A a) :=
        finiteEventMass_nonneg hpi (A a)
      have hpair := fkg_inequality_decreasing_events
        hpi hnorm hlattice ha_dec hs_dec
      calc
        (∏ i ∈ insert a s, finiteEventMass pi (A i)) =
            finiteEventMass pi (A a) *
              ∏ i ∈ s, finiteEventMass pi (A i) := by simp [ha]
        _ <= finiteEventMass pi (A a) *
              finiteEventMass pi (finiteEventInter s A) :=
            mul_le_mul_of_nonneg_left hind hleft
        _ <= finiteEventMass pi (A a ∩ finiteEventInter s A) := hpair
        _ = finiteEventMass pi (finiteEventInter (insert a s) A) := by
          congr 1
          ext omega
          simp [finiteEventInter]




def fkDisconnEvent {V : Type*} (G : SimpleGraph V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  (FK.connEvent G x y)ᶜ

theorem fkDisconnEvent_decreasing {V : Type*} (G : SimpleGraph V)
    (x y : V) : IsDecreasing (fkDisconnEvent G x y) :=
  (FK.connEvent_isIncreasing G x y).compl



theorem finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x y : V) :
    finiteEventMass (FK.fkProb G p q) (fkDisconnEvent G x y) =
      1 - FK.twoPointFun G p q x y := by
  classical
  unfold finiteEventMass FK.twoPointFun fkDisconnEvent
  calc
    (∑ omega, FK.fkProb G p q omega *
        (FK.connEvent G x y)ᶜ.indicator (fun _ => (1 : Real)) omega) =
        ∑ omega, FK.fkProb G p q omega *
          (1 - (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      congr 1
      by_cases homega : omega ∈ FK.connEvent G x y <;>
        simp [homega]
    _ = (∑ omega, FK.fkProb G p q omega) -
        ∑ omega, FK.fkProb G p q omega *
          (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ omega, FK.fkProb G p q omega *
          (FK.connEvent G x y).indicator (fun _ => (1 : Real)) omega := by
      rw [FK.fkProb_sum_eq_one G hp hp1 hq]




theorem fk_finite_pair_nonconnection_product_bound
    {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (s : Finset I) (x y : I -> V) :
    (∏ i ∈ s, (1 - FK.twoPointFun G p q (x i) (y i))) <=
      finiteEventMass (FK.fkProb G p q)
        (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have h := fkg_inequality_finite_decreasing_events
    (fun omega => FK.fkProb_nonneg G hp hp1 hq0 omega)
    (FK.fkProb_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq)
    s (fun i => fkDisconnEvent G (x i) (y i))
    (fun i _ => fkDisconnEvent_decreasing G (x i) (y i))
  simpa only [finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun
    G hp hp1 hq0] using h



def gaugePerimeterPenalty (R : Real) : Real :=
  -Real.log (1 - R) / R

theorem gaugePerimeterPenalty_pos {R : Real} (hR0 : 0 < R) (hR1 : R < 1) :
    0 < gaugePerimeterPenalty R := by
  have hone : 0 < 1 - R := sub_pos.mpr hR1
  have hlt : 1 - R < 1 := by linarith
  have hlog : Real.log (1 - R) < 0 := (Real.log_neg hone hlt)
  exact div_pos (neg_pos.mpr hlog) hR0


theorem exp_neg_gaugePerimeterPenalty_mul (R : Real) (hR0 : 0 < R)
    (hR1 : R < 1) :
    Real.exp (-(gaugePerimeterPenalty R) * R) = 1 - R := by
  have hne : R ≠ 0 := ne_of_gt hR0
  have hone : 0 < 1 - R := sub_pos.mpr hR1
  rw [gaugePerimeterPenalty]
  have hexp : -(-Real.log (1 - R) / R) * R = Real.log (1 - R) := by
    field_simp
  rw [hexp, Real.exp_log hone]



theorem exp_neg_gaugePerimeterPenalty_mul_le_one_sub
    {R r : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hr0 : 0 <= r) (hrR : r <= R) :
    Real.exp (-(gaugePerimeterPenalty R) * r) <= 1 - r := by
  let t := r / R
  have ht0 : 0 <= t := div_nonneg hr0 hR0.le
  have ht1 : t <= 1 := (div_le_one hR0).2 hrR
  have hRm : 0 < 1 - R := sub_pos.mpr hR1
  have hconcave := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : Real) ∈ Set.Ioi 0 by norm_num)
    (show 1 - R ∈ Set.Ioi 0 by exact hRm)
    (sub_nonneg.mpr ht1) ht0 (by simp)
  have harg : 1 - t + t * (1 - R) = 1 - r := by
    dsimp [t]
    field_simp
    ring
  have hlog : t * Real.log (1 - R) <= Real.log (1 - r) := by
    have hc : t * Real.log (1 - R) <=
        Real.log (1 - t + t * (1 - R)) := by
      simpa [smul_eq_mul, Real.log_one] using hconcave
    rwa [harg] at hc
  have hr1 : 0 < 1 - r := by linarith
  rw [← Real.exp_log hr1]
  apply (Real.exp_le_exp).2
  calc
    -(gaugePerimeterPenalty R) * r = t * Real.log (1 - R) := by
      dsimp [gaugePerimeterPenalty, t]
      field_simp
    _ <= Real.log (1 - r) := hlog



theorem exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub
    {I : Type*} {R : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (r : I -> Real)
    (hr0 : forall i : I, i ∈ s -> 0 <= r i)
    (hrR : forall i : I, i ∈ s -> r i <= R) :
    Real.exp (-(gaugePerimeterPenalty R) * (∑ i ∈ s, r i)) <=
      ∏ i ∈ s, (1 - r i) := by
  classical
  have hsum : -(gaugePerimeterPenalty R) * (∑ i ∈ s, r i) =
      ∑ i ∈ s, (-(gaugePerimeterPenalty R) * r i) := by
    rw [Finset.mul_sum]
  rw [hsum, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun i hi => (Real.exp_pos _).le)
    (fun i hi => exp_neg_gaugePerimeterPenalty_mul_le_one_sub
      hR0 hR1 (hr0 i hi) (hrR i hi))





theorem gauge_perimeterLaw_of_product_and_sum_bounds
    {I : Type*} {R C perimeter wilson : Real}
    (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (r : I -> Real)
    (hr0 : forall i : I, i ∈ s -> 0 <= r i)
    (hrR : forall i : I, i ∈ s -> r i <= R)
    (hproduct : (∏ i ∈ s, (1 - r i)) <= wilson)
    (hsum : (∑ i ∈ s, r i) <= C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
  classical
  have hg : 0 <= gaugePerimeterPenalty R :=
    (gaugePerimeterPenalty_pos hR0 hR1).le
  have hscale :
      -(gaugePerimeterPenalty R) * (C * perimeter) <=
        -(gaugePerimeterPenalty R) * (∑ i ∈ s, r i) := by
    exact mul_le_mul_of_nonpos_left hsum (neg_nonpos.mpr hg)
  have hexp :
      Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
        Real.exp (-(gaugePerimeterPenalty R) * (∑ i ∈ s, r i)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, mul_assoc] using hscale
  exact hexp.trans <|
    (exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub
      hR0 hR1 s r hr0 hrR).trans hproduct





theorem fk_perimeterLaw_of_cylinder_bridge_and_sum_bound
    {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q R C perimeter wilson : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hR0 : 0 < R) (hR1 : R < 1)
    (s : Finset I) (x y : I -> V)
    (hR : forall i, i ∈ s -> FK.twoPointFun G p q (x i) (y i) <= R)
    (hcylinder :
      finiteEventMass (FK.fkProb G p q)
          (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) <=
        wilson)
    (hsum : (∑ i ∈ s, FK.twoPointFun G p q (x i) (y i)) <=
      C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    hR0 hR1 s (fun i => FK.twoPointFun G p q (x i) (y i))
  · intro i _
    exact FK.twoPointFun_nonneg G hp hp1 hq0 (x i) (y i)
  · exact hR
  · exact (fk_finite_pair_nonconnection_product_bound
      G hp hp1 hq s x y).trans hcylinder
  · exact hsum

end

end StatMech.FrontierA
