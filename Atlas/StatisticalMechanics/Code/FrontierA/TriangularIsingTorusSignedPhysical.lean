/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusPhysical
import Code.FrontierA.TriangularIsingCriticalC1
import Code.Ising.PressureBCIndep









open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def triangularTorusLinearCharacter
    (chi h : Fin 2 × Fin 2) : Real :=
  (-1 : Real) ^ (chi.1.val * h.1.val + chi.2.val * h.2.val)


def triangularTorusQuadraticWalshSign
    (a b : Fin 2) (chi : Fin 2 × Fin 2) : Real :=
  (-1 : Real) ^
    ((1 + a.val + chi.1.val) * (1 + b.val + chi.2.val))



theorem two_mul_triangularTorus_spinCharacter_eq_walsh
    (a b : Fin 2) (h : Fin 2 × Fin 2) :
    2 * ons_spinCharacter a b h =
      ∑ chi : Fin 2 × Fin 2,
        triangularTorusQuadraticWalshSign a b chi *
          triangularTorusLinearCharacter chi h := by
  rcases h with ⟨h1, h2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    norm_num [ons_spinCharacter, triangularTorusQuadraticWalshSign,
      triangularTorusLinearCharacter, Fintype.sum_prod_type,
      Fin.sum_univ_two]


noncomputable def triangularTorusWeightedLinearCharacterSum
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real)
    (chi : Fin 2 × Fin 2) : Real :=
  ∑ F ∈ evenSubgraphs (triangularTorusGraph L),
    triangularTorusLinearCharacter chi (triangularTorusEvenHomology L F) *
      ∏ edge ∈ F, weight edge



theorem two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real) (a b : Fin 2) :
    (2 : Complex) * triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b =
      ∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusWeightedLinearCharacterSum L weight chi := by
  classical
  unfold triangularTorusWeightedSpinCharacterSum
    triangularTorusWeightedLinearCharacterSum
  push_cast
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  have hwalsh := congrArg (fun x : Real => (x : Complex))
    (two_mul_triangularTorus_spinCharacter_eq_walsh a b
      (triangularTorusEvenHomology L F))
  push_cast at hwalsh
  calc
    (2 : Complex) * ((ons_spinCharacter a b
          (triangularTorusEvenHomology L F) : Complex) *
        ∏ edge ∈ F, (weight edge : Complex)) =
      ((2 : Complex) * (ons_spinCharacter a b
        (triangularTorusEvenHomology L F) : Complex)) *
        ∏ edge ∈ F, (weight edge : Complex) := by ring
    _ = (∑ chi : Fin 2 × Fin 2,
          (triangularTorusQuadraticWalshSign a b chi : Complex) *
            (triangularTorusLinearCharacter chi
              (triangularTorusEvenHomology L F) : Complex)) *
        ∏ edge ∈ F, (weight edge : Complex) := by rw [hwalsh]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi hchi
      ring


noncomputable def triangularTorusSeamTwistSign
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) : Real :=
  triangularTorusLinearCharacter chi
    (if triangularTorusXSeamEdge L edge then 1 else 0,
      if triangularTorusYSeamEdge L edge then 1 else 0)

private theorem prod_neg_one_indicator
    {alpha : Type*} [DecidableEq alpha]
    (F : Finset alpha) (P : alpha → Prop) [DecidablePred P] :
    (∏ x ∈ F, if P x then (-1 : Real) else 1) =
      (-1 : Real) ^ (F.filter P).card := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x F hx ih =>
      by_cases hP : P x
      · simp only [Finset.prod_insert hx, Finset.filter_insert, hP,
          if_true, ih]
        rw [Finset.card_insert_of_notMem (by simp [hx]), pow_succ]
        ring
      · simp [Finset.prod_insert hx, Finset.filter_insert, hP, hx, ih]

private theorem triangularTorusSeamTwistSign_eq_mul
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    triangularTorusSeamTwistSign L chi edge =
      (if triangularTorusXSeamEdge L edge then
          (-1 : Real) ^ chi.1.val else 1) *
        (if triangularTorusYSeamEdge L edge then
          (-1 : Real) ^ chi.2.val else 1) := by
  rcases chi with ⟨chi1, chi2⟩
  fin_cases chi1 <;> fin_cases chi2 <;>
    simp [triangularTorusSeamTwistSign, triangularTorusLinearCharacter] <;>
    split_ifs <;> norm_num



theorem prod_triangularTorusSeamTwistSign
    (L : Nat) (chi : Fin 2 × Fin 2)
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    (∏ edge ∈ F, triangularTorusSeamTwistSign L chi edge) =
      triangularTorusLinearCharacter chi (triangularTorusEvenHomology L F) := by
  classical
  rcases chi with ⟨chi1, chi2⟩
  simp_rw [triangularTorusSeamTwistSign_eq_mul]
  rw [Finset.prod_mul_distrib]
  fin_cases chi1 <;> fin_cases chi2
  · simp [triangularTorusLinearCharacter]
  · simp only [Fin.isValue, pow_zero, ite_self, Finset.prod_const_one,
      one_mul, pow_one]
    rw [prod_neg_one_indicator]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      neg_one_pow_eq_pow_mod_two]
  · simp only [Fin.isValue, pow_zero, ite_self, Finset.prod_const_one,
      pow_one, mul_one]
    rw [prod_neg_one_indicator]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      neg_one_pow_eq_pow_mod_two]
  · simp only [Fin.isValue, pow_one]
    rw [prod_neg_one_indicator, prod_neg_one_indicator, ← pow_add,
      neg_one_pow_eq_pow_mod_two]
    simp [triangularTorusLinearCharacter, triangularTorusEvenHomology,
      Nat.add_mod]
    conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
    congr 1
    omega


theorem triangularTorusXSeamEdge_card
    (L : Nat) [Fact (2 < L)] :
    ((triangularTorusGraph L).edgeFinset.filter
      (triangularTorusXSeamEdge L)).card = 2 * L := by
  have h := sum_triangularPositiveEdgeSources (A := Nat) L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge => if triangularTorusXSeamEdge L edge then 1 else 0)
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusXSeamEdge_positiveEdge_iff] at h
  have hfirst :
      (Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.1 = -1)).card = L := by
    have heq : Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.1 = -1) =
        ({-1} : Finset (ZMod L)).product Finset.univ := by
      ext p
      rcases p with ⟨x, y⟩
      simp [eq_comm]
    rw [heq]
    simp [ZMod.card]
  have hc :
      ((triangularTorusGraph L).edgeFinset.filter
        (triangularTorusXSeamEdge L)).card = L + L := by
    simpa [Finset.sum_boole, Fin.sum_univ_three, hfirst] using h
  omega


theorem triangularTorusYSeamEdge_card
    (L : Nat) [Fact (2 < L)] :
    ((triangularTorusGraph L).edgeFinset.filter
      (triangularTorusYSeamEdge L)).card = 2 * L := by
  have h := sum_triangularPositiveEdgeSources (A := Nat) L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge => if triangularTorusYSeamEdge L edge then 1 else 0)
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusYSeamEdge_positiveEdge_iff] at h
  have hsecond :
      (Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.2 = -1)).card = L := by
    have heq : Finset.univ.filter
        (fun p : ZMod L × ZMod L => p.2 = -1) =
        Finset.univ.product ({-1} : Finset (ZMod L)) := by
      ext p
      rcases p with ⟨x, y⟩
      simp [eq_comm]
    rw [heq]
    simp [ZMod.card]
  have hc :
      ((triangularTorusGraph L).edgeFinset.filter
        (triangularTorusYSeamEdge L)).card = L + L := by
    simpa [Finset.sum_boole, Fin.sum_univ_three, hsecond] using h
  omega


noncomputable def triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2) :
    Sym2 (ZMod L × ZMod L) → Real := fun edge =>
  triangularTorusSeamTwistSign L chi edge *
    triangularTorusRealEdgeWeight L J1 J2 J3 edge

theorem triangularTorusSeamTwistSign_eq_one_or_neg_one
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    triangularTorusSeamTwistSign L chi edge = 1 ∨
      triangularTorusSeamTwistSign L chi edge = -1 := by
  unfold triangularTorusSeamTwistSign triangularTorusLinearCharacter
  exact neg_one_pow_eq_or Real _

@[simp] theorem abs_triangularTorusSeamTwistSign
    (L : Nat) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusSeamTwistSign L chi edge| = 1 := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

@[simp] theorem cosh_triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    Real.cosh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) =
      Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · simp [triangularTorusSeamTwistedCoupling, h]
  · simp [triangularTorusSeamTwistedCoupling, h, Real.cosh_neg]

@[simp] theorem tanh_triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    Real.tanh (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge) =
      triangularTorusSeamTwistSign L chi edge *
        Real.tanh (triangularTorusRealEdgeWeight L J1 J2 J3 edge) := by
  rcases triangularTorusSeamTwistSign_eq_one_or_neg_one L chi edge with h | h
  · simp [triangularTorusSeamTwistedCoupling, h]
  · simp [triangularTorusSeamTwistedCoupling, h, Real.tanh_neg]

theorem tanh_triangularTorusRealEdgeWeight
    (L : Nat) (J1 J2 J3 : Real) :
    (fun edge => Real.tanh
      (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) =
      triangularTorusRealEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) := by
  funext edge
  unfold triangularTorusRealEdgeWeight
  split_ifs <;> rfl

theorem inhomogeneousEvenSubgraphSum_seamTwist
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real)
    (chi : Fin 2 × Fin 2) :
    inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
        (fun edge => triangularTorusSeamTwistSign L chi edge * weight edge) =
      triangularTorusWeightedLinearCharacterSum L weight chi := by
  classical
  unfold inhomogeneousEvenSubgraphSum
    triangularTorusWeightedLinearCharacterSum
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, prod_triangularTorusSeamTwistSign]


theorem triangularTorusSeamTwistedPartition_highTemperature
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) =
      (2 : Real) ^ (L * L) *
        (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
        triangularTorusWeightedLinearCharacterSum L
          (triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) chi := by
  rw [triangularTorusIsingPartition_highTemperature]
  have hcard : Fintype.card (ZMod L × ZMod L) = L * L := by
    simp [Fintype.card_prod, ZMod.card]
  rw [hcard]
  simp_rw [cosh_triangularTorusSeamTwistedCoupling]
  rw [prod_cosh_triangularTorusRealEdgeWeight]
  simp_rw [tanh_triangularTorusSeamTwistedCoupling]
  simp_rw [congrFun (tanh_triangularTorusRealEdgeWeight L J1 J2 J3)]
  rw [inhomogeneousEvenSubgraphSum_seamTwist]


noncomputable def triangularTorusNormalizedLinearSector
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) : Real :=
  (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
    triangularTorusWeightedLinearCharacterSum L
      (triangularTorusRealEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) chi

theorem triangularTorusSeamTwistedPartition_eq
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0) =
      (2 : Real) ^ (L * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  rw [triangularTorusSeamTwistedPartition_highTemperature]
  unfold triangularTorusNormalizedLinearSector
  ring

theorem triangularTorusNormalizedLinearSector_pos
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    0 < triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  have hZ := StatMech.Sharpness.ZJ_pos
    (triangularTorusGraph L).edgeFinset
    (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0)
  rw [triangularTorusSeamTwistedPartition_eq] at hZ
  rcases mul_pos_iff.mp hZ with h | h
  · exact h.2
  · exfalso
    exact (not_lt_of_ge (by positivity)) h.1


theorem ZJ_log_coupling_sub_abs_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (J J' : Sym2 V → Real) :
    |Real.log (StatMech.Sharpness.ZJ E J (fun _ => 0)) -
        Real.log (StatMech.Sharpness.ZJ E J' (fun _ => 0))| ≤
      ∑ edge ∈ E, |J edge - J' edge| := by
  let action : (Sym2 V → Real) → ConfigSpace V → Real := fun K s =>
    ∑ edge ∈ E, K edge * bond s edge
  have haction (s : ConfigSpace V) :
      |action J s - action J' s| ≤
        ∑ edge ∈ E, |J edge - J' edge| := by
    dsimp only [action]
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ edge ∈ E,
          (J edge * bond s edge - J' edge * bond s edge)| ≤
        ∑ edge ∈ E,
          |J edge * bond s edge - J' edge * bond s edge| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ edge ∈ E, |J edge - J' edge| := by
        apply Finset.sum_le_sum
        intro edge hedge
        rw [← sub_mul, abs_mul]
        have hb : |bond s edge| ≤ 1 := by
          rcases bond_eq_pm s edge with h | h <;> simp [h]
        exact mul_le_of_le_one_right (abs_nonneg _) hb
  have hdist := logZ_dist_le (-1) (action J) (action J')
    (∑ edge ∈ E, |J edge - J' edge|) haction
  simpa [StatMech.Ising.Z, StatMech.Sharpness.ZJ,
    StatMech.Sharpness.wJ, action] using hdist

theorem abs_triangularTorusRealEdgeWeight_le
    (L : Nat) (J1 J2 J3 : Real)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤
      |J1| + |J2| + |J3| := by
  unfold triangularTorusRealEdgeWeight
  split_ifs <;>
    nlinarith [abs_nonneg J1, abs_nonneg J2, abs_nonneg J3]

theorem abs_triangularTorusSeamTwistedCoupling_sub_le
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2)
    (edge : Sym2 (ZMod L × ZMod L)) :
    |triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge -
        triangularTorusRealEdgeWeight L J1 J2 J3 edge| ≤
      2 * (|J1| + |J2| + |J3|) *
        ((if triangularTorusXSeamEdge L edge then 1 else 0) +
          (if triangularTorusYSeamEdge L edge then 1 else 0)) := by
  let S := |J1| + |J2| + |J3|
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hw := abs_triangularTorusRealEdgeWeight_le L J1 J2 J3 edge
  have hflip :
      |-triangularTorusRealEdgeWeight L J1 J2 J3 edge -
          triangularTorusRealEdgeWeight L J1 J2 J3 edge| =
        2 * |triangularTorusRealEdgeWeight L J1 J2 J3 edge| := by
    rw [show -triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L J1 J2 J3 edge =
      -(2 * triangularTorusRealEdgeWeight L J1 J2 J3 edge) by ring,
      abs_neg, abs_mul]
    norm_num
  rcases chi with ⟨chi1, chi2⟩
  fin_cases chi1 <;> fin_cases chi2 <;>
    simp [triangularTorusSeamTwistedCoupling,
      triangularTorusSeamTwistSign, triangularTorusLinearCharacter] <;>
    split_ifs <;> simp_all [hflip] <;> nlinarith



theorem triangularTorusSeamTwistedPartition_log_sub_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusSeamTwistedCoupling L J1 J2 J3 chi) (fun _ => 0)) -
      Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
        (triangularTorusRealEdgeWeight L J1 J2 J3) (fun _ => 0))| ≤
      8 * (|J1| + |J2| + |J3|) * L := by
  calc
    _ ≤ ∑ edge ∈ (triangularTorusGraph L).edgeFinset,
        |triangularTorusSeamTwistedCoupling L J1 J2 J3 chi edge -
          triangularTorusRealEdgeWeight L J1 J2 J3 edge| :=
      ZJ_log_coupling_sub_abs_le (triangularTorusGraph L).edgeFinset _ _
    _ ≤ ∑ edge ∈ (triangularTorusGraph L).edgeFinset,
        2 * (|J1| + |J2| + |J3|) *
          ((if triangularTorusXSeamEdge L edge then 1 else 0) +
            (if triangularTorusYSeamEdge L edge then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro edge hedge
      exact abs_triangularTorusSeamTwistedCoupling_sub_le
        L J1 J2 J3 chi edge
    _ = _ := by
      rw [← Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib, Finset.sum_boole]
      rw [triangularTorusXSeamEdge_card,
        triangularTorusYSeamEdge_card]
      push_cast
      ring

@[simp] theorem triangularTorusSeamTwistedCoupling_zero
    (L : Nat) (J1 J2 J3 : Real) :
    triangularTorusSeamTwistedCoupling L J1 J2 J3 (0, 0) =
      triangularTorusRealEdgeWeight L J1 J2 J3 := by
  funext edge
  simp [triangularTorusSeamTwistedCoupling,
    triangularTorusSeamTwistSign, triangularTorusLinearCharacter]

theorem triangularTorusNormalizedLinearSector_zero
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) =
      (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
        inhomogeneousEvenSubgraphSum (triangularTorusGraph L)
          (triangularTorusRealEdgeWeight L
            (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) := by
  unfold triangularTorusNormalizedLinearSector
    triangularTorusWeightedLinearCharacterSum
    inhomogeneousEvenSubgraphSum
  congr 1
  apply Finset.sum_congr rfl
  intro F hF
  simp [triangularTorusLinearCharacter]


theorem triangularTorusNormalizedLinearSector_log_sub_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 chi) -
      Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0))| ≤
      8 * (|J1| + |J2| + |J3|) * L := by
  have h := triangularTorusSeamTwistedPartition_log_sub_abs_le
    L J1 J2 J3 chi
  rw [← triangularTorusSeamTwistedCoupling_zero L J1 J2 J3,
    triangularTorusSeamTwistedPartition_eq,
    triangularTorusSeamTwistedPartition_eq] at h
  have hpow : (2 : Real) ^ (L * L) ≠ 0 := by positivity
  have hchi := triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi
  have hzero := triangularTorusNormalizedLinearSector_pos
    L J1 J2 J3 (0, 0)
  rw [Real.log_mul hpow hchi.ne', Real.log_mul hpow hzero.ne'] at h
  convert h using 1 <;> congr 1 <;> ring

theorem triangularTorusNormalizedLinearSector_le_exp_boundary_mul
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 chi ≤
      Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let B : Real := 8 * (|J1| + |J2| + |J3|) * L
  let Pchi := triangularTorusNormalizedLinearSector L J1 J2 J3 chi
  let Pzero := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  have hchi : 0 < Pchi :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi
  have hzero : 0 < Pzero :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have habs := triangularTorusNormalizedLinearSector_log_sub_abs_le
    L J1 J2 J3 chi
  have hlog : Real.log Pchi ≤ Real.log Pzero + B := by
    dsimp only [Pchi, Pzero, B] at habs ⊢
    linarith [le_abs_self
      (Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 chi) -
        Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)))]
  calc
    Pchi = Real.exp (Real.log Pchi) := (Real.exp_log hchi).symm
    _ ≤ Real.exp (Real.log Pzero + B) := Real.exp_le_exp.mpr hlog
    _ = Real.exp B * Pzero := by
      rw [Real.exp_add, Real.exp_log hzero]
      ring


noncomputable def triangularTorusNormalizedQuadraticSector
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a b : Fin 2) : Complex :=
  ((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) *
    triangularTorusWeightedSpinCharacterSum L
      (triangularTorusEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b



theorem two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a b : Fin 2) :
    (2 : Complex) *
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b =
      ∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
  let C : Real :=
    (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  have hw := two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh
    L (triangularTorusRealEdgeWeight L
      (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b
  unfold triangularTorusNormalizedQuadraticSector
    triangularTorusNormalizedLinearSector
  rw [← triangularTorusEdgeWeight_real_cast]
  have hscaled := congrArg (fun z : Complex => (C : Complex) * z) hw
  dsimp only at hscaled
  rw [Finset.mul_sum] at hscaled
  convert hscaled using 1
  · ring
  · apply Finset.sum_congr rfl
    intro chi hchi
    norm_cast
    ring



theorem norm_triangularTorusNormalizedQuadraticSector_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (a b : Fin 2) :
    ‖triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b‖ ≤
      2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let Q := triangularTorusNormalizedQuadraticSector L J1 J2 J3 a b
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let R := Real.exp (8 * (|J1| + |J2| + |J3|) * L) * P
  have hw := two_mul_triangularTorusNormalizedQuadraticSector_eq_walsh
    L J1 J2 J3 a b
  have hsum :
      ‖∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ ≤
        ∑ chi : Fin 2 × Fin 2,
          ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ :=
    norm_sum_le _ _
  have hterm (chi : Fin 2 × Fin 2) :
      ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ =
        triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hsign : |triangularTorusQuadraticWalshSign a b chi| = 1 := by
      unfold triangularTorusQuadraticWalshSign
      rcases neg_one_pow_eq_or Real
          ((1 + a.val + chi.1.val) * (1 + b.val + chi.2.val)) with h | h <;>
        simp [h]
    rw [hsign, one_mul, abs_of_pos
      (triangularTorusNormalizedLinearSector_pos L J1 J2 J3 chi)]
  have hlinear (chi : Fin 2 × Fin 2) :
      triangularTorusNormalizedLinearSector L J1 J2 J3 chi ≤ R := by
    exact triangularTorusNormalizedLinearSector_le_exp_boundary_mul
      L J1 J2 J3 chi
  have hfour :
      (∑ _chi : Fin 2 × Fin 2, R) = 4 * R := by simp
  have hnorm : 2 * ‖Q‖ ≤ 4 * R := by
    calc
      2 * ‖Q‖ = ‖(2 : Complex) * Q‖ := by norm_num
      _ = ‖∑ chi : Fin 2 × Fin 2,
          (triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ := by
        rw [hw]
      _ ≤ ∑ chi : Fin 2 × Fin 2,
          ‖(triangularTorusQuadraticWalshSign a b chi : Complex) *
            triangularTorusNormalizedLinearSector L J1 J2 J3 chi‖ := hsum
      _ = ∑ chi : Fin 2 × Fin 2,
          triangularTorusNormalizedLinearSector L J1 J2 J3 chi := by
        apply Finset.sum_congr rfl
        intro chi hchi
        exact hterm chi
      _ ≤ ∑ _chi : Fin 2 × Fin 2, R :=
        Finset.sum_le_sum fun chi hchi => hlinear chi
      _ = 4 * R := hfour
  dsimp only [Q, R, P] at hnorm ⊢
  linarith



theorem two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    ((2 * triangularTorusNormalizedLinearSector
        L J1 J2 J3 (0, 0) : Real) : Complex) =
      triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 1 +
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 1 +
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 1 0 -
        triangularTorusNormalizedQuadraticSector L J1 J2 J3 0 0 := by
  let C : Real :=
    (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L)
  let weight := triangularTorusRealEdgeWeight L
    (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)
  have harf := two_mul_triangularTorusEvenSubgraphSum_eq_spin L weight
  have hscaled := congrArg (fun z : Complex => (C : Complex) * z) harf
  dsimp only at hscaled
  rw [triangularTorusNormalizedLinearSector_zero]
  unfold triangularTorusNormalizedQuadraticSector
  rw [← triangularTorusEdgeWeight_real_cast]
  change (((2 * (C * inhomogeneousEvenSubgraphSum
    (triangularTorusGraph L) weight) : Real)) : Complex) = _
  convert hscaled using 1 <;> norm_cast <;> ring

theorem triangularTorusNormalizedLinearSector_zero_le_two_mul_max
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) ≤
      2 * arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let Q := triangularTorusNormalizedQuadraticSector L J1 J2 J3
  let M := arfSectorNormMax Q
  have hP : 0 < P :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have harf :=
    two_mul_triangularTorusNormalizedLinearSector_zero_eq_arf L J1 J2 J3
  have hterm (a b : Fin 2) : ‖Q a b‖ ≤ M :=
    norm_le_arfSectorNormMax Q a b
  have hsum :
      ‖Q 1 1 + Q 0 1 + Q 1 0 - Q 0 0‖ ≤ 4 * M := by
    calc
      _ ≤ ‖Q 1 1 + Q 0 1 + Q 1 0‖ + ‖Q 0 0‖ := norm_sub_le _ _
      _ ≤ (‖Q 1 1 + Q 0 1‖ + ‖Q 1 0‖) + ‖Q 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖Q 1 1‖ + ‖Q 0 1‖) + ‖Q 1 0‖) + ‖Q 0 0‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ 4 * M := by
        nlinarith [hterm 1 1, hterm 0 1, hterm 1 0, hterm 0 0]
  have harfNorm := congrArg norm harf
  have hleft : ‖((2 * P : Real) : Complex)‖ = 2 * P := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hP)]
  rw [hleft] at harfNorm
  dsimp only [P, Q, M] at hsum harfNorm ⊢
  nlinarith [harfNorm.trans_le hsum]

theorem arfSectorNormMax_normalizedQuadratic_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) ≤
      2 * Real.exp (8 * (|J1| + |J2| + |J3|) * L) *
        triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  unfold arfSectorNormMax
  apply max_le
  · apply max_le <;>
      exact norm_triangularTorusNormalizedQuadraticSector_le L J1 J2 J3 _ _
  · apply max_le <;>
      exact norm_triangularTorusNormalizedQuadraticSector_le L J1 J2 J3 _ _


theorem triangularTorusSigned_normalized_log_gap_abs_le
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real) :
    |Real.log (triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)) -
      Real.log (arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3))| ≤
      8 * (|J1| + |J2| + |J3|) * L + Real.log 2 := by
  let P := triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0)
  let M := arfSectorNormMax
    (triangularTorusNormalizedQuadraticSector L J1 J2 J3)
  let B : Real := 8 * (|J1| + |J2| + |J3|) * L
  have hP : 0 < P :=
    triangularTorusNormalizedLinearSector_pos L J1 J2 J3 (0, 0)
  have hPM : P ≤ 2 * M :=
    triangularTorusNormalizedLinearSector_zero_le_two_mul_max L J1 J2 J3
  have hM : 0 < M := by
    by_contra h
    have hnonpos := le_of_not_gt h
    nlinarith
  have hMP : M ≤ 2 * Real.exp B * P :=
    arfSectorNormMax_normalizedQuadratic_le L J1 J2 J3
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hlog_upper : Real.log P - Real.log M ≤ Real.log 2 := by
    have h := Real.log_le_log hP hPM
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hM.ne'] at h
    linarith
  have hlog_lower : -(B + Real.log 2) ≤ Real.log P - Real.log M := by
    have htwoexp : 0 < 2 * Real.exp B := mul_pos (by norm_num) (Real.exp_pos _)
    have h := Real.log_le_log hM hMP
    rw [Real.log_mul htwoexp.ne' hP.ne',
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) (Real.exp_ne_zero B),
      Real.log_exp] at h
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  dsimp only [P, M, B] at hlog_upper hlog_lower hB ⊢
  rw [abs_le]
  constructor
  · exact hlog_lower
  · linarith

theorem triangularTorusNormalizedEvenSequence_eq_linear
    (J1 J2 J3 : Real) (n : Nat) :
    triangularTorusNormalizedEvenSequence J1 J2 J3 n =
      let L := n + 3
      letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
      triangularTorusNormalizedLinearSector L J1 J2 J3 (0, 0) := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusNormalizedEvenSequence,
    triangularTorusNormalizedLinearSector_zero]

theorem triangularTorusNormalizedSectorMaxSequence_eq_quadratic
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n =
      let L := n + 3
      letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
      arfSectorNormMax
        (triangularTorusNormalizedQuadraticSector L J1 J2 J3) := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  unfold triangularTorusNormalizedSectorMaxSequence
    triangularTorusNormalizedSectorSequence
    triangularTorusNormalizedQuadraticSector
  rfl

theorem triangularTorusSigned_normalizedSequence_log_gap_abs_le
    (J1 J2 J3 : Real) (rho : Complex) (n : Nat) :
    |Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence
        J1 J2 J3 rho n)| ≤
      8 * (|J1| + |J2| + |J3|) * (n + 3) + Real.log 2 := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  rw [triangularTorusNormalizedEvenSequence_eq_linear,
    triangularTorusNormalizedSectorMaxSequence_eq_quadratic]
  simpa only [L, Nat.cast_add, Nat.cast_ofNat] using
    (triangularTorusSigned_normalized_log_gap_abs_le L J1 J2 J3)



theorem triangularTorusSigned_normalized_log_gap_tendsto_zero
    (J1 J2 J3 : Real) (rho : Complex) :
    Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2)
      Filter.atTop (nhds 0) := by
  let A : Real := 8 * (|J1| + |J2| + |J3|)
  let upper : Nat → Real := fun n =>
    (A * (n + 3 : Real) + Real.log 2) / (n + 3 : Real) ^ 2
  have hrecip : Filter.Tendsto
      (fun n : Nat => (1 : Real) / (n + 3 : Real))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := Real)).comp
        (Filter.tendsto_add_atTop_nat 3)
  have hupper : Filter.Tendsto upper Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => A) Filter.atTop (nhds A)).mul hrecip).add
      ((tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).mul
          (hrecip.mul hrecip))
    convert h using 1
    funext n
    dsimp only [upper]
    have hn : (n + 3 : Real) ≠ 0 := by positivity
    field_simp
    ring
  have hlower : Filter.Tendsto (fun n => -upper n)
      Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hupper.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper ?_ ?_
  · intro n
    let gap := Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)
    have habs := triangularTorusSigned_normalizedSequence_log_gap_abs_le
      J1 J2 J3 rho n
    have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
    have hscaled : |gap / (n + 3 : Real) ^ 2| ≤ upper n := by
      rw [abs_div, abs_of_pos hden]
      dsimp only [gap, upper, A] at habs ⊢
      exact div_le_div_of_nonneg_right habs hden.le
    exact (abs_le.mp hscaled).1
  · intro n
    let gap := Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
      Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)
    have habs := triangularTorusSigned_normalizedSequence_log_gap_abs_le
      J1 J2 J3 rho n
    have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
    have hscaled : |gap / (n + 3 : Real) ^ 2| ≤ upper n := by
      rw [abs_div, abs_of_pos hden]
      dsimp only [gap, upper, A] at habs ⊢
      exact div_le_div_of_nonneg_right habs hden.le
    exact (abs_le.mp hscaled).2



theorem triangularTorusSignedNormalizedEven_logDensity_tendsto
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
  have hgap := triangularTorusSigned_normalized_log_gap_tendsto_zero
    J1 J2 J3 rho
  have hmax := triangularTorusNormalizedSectorMax_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hadd := hgap.add hmax
  have hadd' : Filter.Tendsto
      (fun n : Nat =>
        (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) -
            Real.log (triangularTorusNormalizedSectorMaxSequence
              J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedSectorMaxSequence
            J1 J2 J3 rho n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds ((1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi,
          ∫ k2 in (-Real.pi)..Real.pi,
            Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
    simpa only [zero_add] using hadd
  apply hadd'.congr'
  filter_upwards [] with n
  ring

theorem triangularTorusNormalizedEvenSequence_pos
    (J1 J2 J3 : Real) (n : Nat) :
    0 < triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
  have hZ : 0 < triangularTorusIsingPartitionSequence J1 J2 J3 n := by
    unfold triangularTorusIsingPartitionSequence
    exact StatMech.Sharpness.ZJ_pos _ _ _
  rw [triangularTorusIsingPartitionSequence_eq] at hZ
  rcases mul_pos_iff.mp hZ with h | h
  · exact h.2
  · exfalso
    exact (not_lt_of_ge (by positivity)) h.1



theorem triangularTorusIsingPartition_freeEnergy_tendsto_signed
    (J1 J2 J3 : Real) (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hpos : forall k1 k2,
      0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
  have heven := triangularTorusSignedNormalizedEven_logDensity_tendsto
    J1 J2 J3 rho hrho hpos
  have hlog2 : Filter.Tendsto
      (fun n : Nat =>
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
          (n + 3 : Real) ^ 2)
      Filter.atTop (nhds (Real.log 2)) := by
    have heq : ∀ n : Nat,
        Real.log (2 ^ ((n + 3) * (n + 3)) : Real) /
            (n + 3 : Real) ^ 2 = Real.log 2 := by
      intro n
      rw [Real.log_pow]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => Real.log 2) Filter.atTop (nhds (Real.log 2))).congr'
        (Filter.Eventually.of_forall fun n => (heq n).symm)
  have hneg := (hlog2.add heven).neg
  have hneg' : Filter.Tendsto
      (fun (x : Nat) =>
        -(Real.log (2 ^ ((x + 3) * (x + 3)) : Real) /
            (x + 3 : Real) ^ 2 +
          Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 x) /
            (x + 3 : Real) ^ 2))
      Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
    convert hneg using 1 <;> unfold triangularIsingFreeEnergyValue <;> ring
  apply hneg'.congr'
  filter_upwards [] with n
  rw [triangularTorusIsingPartitionSequence_eq]
  have htwo : (2 ^ ((n + 3) * (n + 3)) : Real) ≠ 0 := by positivity
  have hevenPos := triangularTorusNormalizedEvenSequence_pos J1 J2 J3 n
  rw [Real.log_mul htwo hevenPos.ne']
  ring

theorem sum_abs_triangularTorusRealEdgeWeight_sub
    (L : Nat) [Fact (2 < L)]
    (J1 J2 J3 K1 K2 K3 : Real) :
    (∑ edge ∈ (triangularTorusGraph L).edgeFinset,
      |triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L K1 K2 K3 edge|) =
      (L * L : Nat) * (|J1 - K1| + |J2 - K2| + |J3 - K3|) := by
  rw [sum_triangularPositiveEdgeSources L
    (triangularTorusGraph L).edgeFinset (fun _ hedge => hedge)
    (fun edge =>
      |triangularTorusRealEdgeWeight L J1 J2 J3 edge -
        triangularTorusRealEdgeWeight L K1 K2 K3 edge|)]
  simp_rw [triangularPositiveEdgeSources_edgeFinset,
    triangularTorusRealEdgeWeight_positiveEdge]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    ZMod.card, nsmul_eq_mul]
  rw [Fin.sum_univ_three]
  norm_num
  simp
  ring



theorem triangularTorusIsingPartition_freeEnergy_ray_lipschitz
    (J b c : Real) (n : Nat) :
    |(-Real.log (triangularTorusIsingPartitionSequence b b (b * J) n) /
          (n + 3 : Real) ^ 2) -
      (-Real.log (triangularTorusIsingPartitionSequence c c (c * J) n) /
          (n + 3 : Real) ^ 2)| ≤
      (2 + |J|) * |b - c| := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by dsimp only [L]; omega⟩
  have hlog := ZJ_log_coupling_sub_abs_le
    (triangularTorusGraph L).edgeFinset
    (triangularTorusRealEdgeWeight L b b (b * J))
    (triangularTorusRealEdgeWeight L c c (c * J))
  rw [sum_abs_triangularTorusRealEdgeWeight_sub] at hlog
  have hden : 0 < (n + 3 : Real) ^ 2 := by positivity
  have hdiff : |b * J - c * J| = |b - c| * |J| := by
    rw [← sub_mul, abs_mul]
  rw [hdiff] at hlog
  unfold triangularTorusIsingPartitionSequence
  rw [← sub_div, abs_div, abs_of_pos hden]
  calc
    |-Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L b b (b * J)) (fun _ => 0)) -
        -Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L c c (c * J)) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 =
      |Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L c c (c * J)) (fun _ => 0)) -
        Real.log (StatMech.Sharpness.ZJ (triangularTorusGraph L).edgeFinset
          (triangularTorusRealEdgeWeight L b b (b * J)) (fun _ => 0))| /
        (n + 3 : Real) ^ 2 := by
      congr 2
      ring
    _ ≤
      ((L * L : Nat) *
        (|b - c| + |b - c| + |b - c| * |J|)) /
          (n + 3 : Real) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa only [abs_sub_comm] using hlog
    _ = (2 + |J|) * |b - c| := by
      dsimp only [L]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      field_simp
      ring



theorem triangularTorusIsingPartition_freeEnergy_tendsto_critical
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : -1 < J)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  let gamma : Nat → Real := fun m => beta + 1 / ((m : Real) + 1)
  let C : Real := 2 + |J|
  have hC : 0 < C := by dsimp only [C]; positivity
  have hgamma : Filter.Tendsto gamma Filter.atTop (nhds beta) := by
    simpa only [gamma, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have hcontinuous : ContinuousAt
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
    (triangularIsingFreeEnergyValue_contDiffAt_one_of_gt_neg_one_root
      hbeta hJ hroot).continuousAt
  have hvalue : Filter.Tendsto
      (fun m => triangularIsingFreeEnergyValue (gamma m) (gamma m)
        (gamma m * J)) Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) :=
    hcontinuous.tendsto.comp hgamma
  obtain ⟨critical, hcritical, hcriticalUnique⟩ :=
    existsUnique_triangularIsingSymbol_zero_of_gt_neg_one hJ
  have hbetaZero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hroot
  have hbetaCritical : beta = critical :=
    hcriticalUnique beta ⟨hbeta, hbetaZero⟩
  rw [Metric.tendsto_atTop] at hvalue hgamma ⊢
  intro epsilon hepsilon
  obtain ⟨Nvalue, hNvalue⟩ := hvalue (epsilon / 3) (by positivity)
  obtain ⟨Ngamma, hNgamma⟩ := hgamma (epsilon / (3 * C)) (by positivity)
  let m := max Nvalue Ngamma
  have hmvalue :
      dist (triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J))
        (triangularIsingFreeEnergyValue beta beta (beta * J)) < epsilon / 3 :=
    hNvalue m (le_max_left _ _)
  have hmgamma : dist (gamma m) beta < epsilon / (3 * C) :=
    hNgamma m (le_max_right _ _)
  have hgammapos : 0 < gamma m := by
    dsimp only [gamma]
    have hone : 0 < 1 / ((m : Real) + 1) := by positivity
    linarith
  have hgammanebeta : gamma m ≠ beta := by
    dsimp only [gamma]
    have hone : 0 < 1 / ((m : Real) + 1) := by positivity
    linarith
  have hgammanoncritical :
      triangularIsingCriticalRate (gamma m) (gamma m * J) ≠ 1 := by
    intro hgammaRoot
    have hgammaZero : triangularIsingSymbol (gamma m) (gamma m)
        (gamma m * J) 0 0 = 0 :=
      (triangularIsingSymbol_zero_iff_criticalRate_eq_one hgammapos).2
        hgammaRoot
    have hgammaCritical : gamma m = critical :=
      hcriticalUnique (gamma m) ⟨hgammapos, hgammaZero⟩
    exact hgammanebeta (hgammaCritical.trans hbetaCritical.symm)
  have hsymbol (p q : Real) :
      0 < triangularIsingSymbol (gamma m) (gamma m) (gamma m * J) p q :=
    triangularIsingSymbol_pos_of_gt_neg_one_noncritical
      hgammapos hJ hgammanoncritical p q
  have hfixed := triangularTorusIsingPartition_freeEnergy_tendsto_signed
    (gamma m) (gamma m) (gamma m * J) rho hrho hsymbol
  rw [Metric.tendsto_atTop] at hfixed
  obtain ⟨Nfixed, hNfixed⟩ := hfixed (epsilon / 3) (by positivity)
  refine ⟨Nfixed, fun n hn => ?_⟩
  have hmiddle := hNfixed n hn
  have hfinite := triangularTorusIsingPartition_freeEnergy_ray_lipschitz
    J beta (gamma m) n
  rw [Real.dist_eq] at hmiddle hmvalue hmgamma ⊢
  calc
    |-Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2 -
        triangularIsingFreeEnergyValue beta beta (beta * J)| ≤
      |(-Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2) -
        (-Real.log (triangularTorusIsingPartitionSequence
          (gamma m) (gamma m) (gamma m * J) n) / (n + 3 : Real) ^ 2)| +
      |(-Real.log (triangularTorusIsingPartitionSequence
          (gamma m) (gamma m) (gamma m * J) n) / (n + 3 : Real) ^ 2) -
        triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J)| +
      |triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J) -
        triangularIsingFreeEnergyValue beta beta (beta * J)| := by
      calc
        _ ≤ |(-Real.log (triangularTorusIsingPartitionSequence
            beta beta (beta * J) n) / (n + 3 : Real) ^ 2) -
              (-Real.log (triangularTorusIsingPartitionSequence
                (gamma m) (gamma m) (gamma m * J) n) /
                  (n + 3 : Real) ^ 2)| +
            |(-Real.log (triangularTorusIsingPartitionSequence
              (gamma m) (gamma m) (gamma m * J) n) /
                (n + 3 : Real) ^ 2) -
              triangularIsingFreeEnergyValue beta beta (beta * J)| :=
          abs_sub_le _ _ _
        _ ≤ _ := by
          have htriangle := abs_sub_le
            (-Real.log (triangularTorusIsingPartitionSequence
              (gamma m) (gamma m) (gamma m * J) n) /
                (n + 3 : Real) ^ 2)
            (triangularIsingFreeEnergyValue (gamma m) (gamma m) (gamma m * J))
            (triangularIsingFreeEnergyValue beta beta (beta * J))
          linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      gcongr
      calc
        _ ≤ C * |beta - gamma m| := hfinite
        _ = C * |gamma m - beta| := by rw [abs_sub_comm]
        _ < C * (epsilon / (3 * C)) := by
          gcongr
        _ = epsilon / 3 := by field_simp
    _ = epsilon := by ring



theorem triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : -1 < J) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  by_cases hroot : triangularIsingCriticalRate beta (beta * J) = 1
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_critical
      rho hrho hbeta hJ hroot
  · apply triangularTorusIsingPartition_freeEnergy_tendsto_signed
      beta beta (beta * J) rho hrho
    exact triangularIsingSymbol_pos_of_gt_neg_one_noncritical
      hbeta hJ hroot


theorem triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one
    {beta J : Real} (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (hbeta : 0 < beta) (hJ : J ≤ -1) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  apply triangularTorusIsingPartition_freeEnergy_tendsto_signed
    beta beta (beta * J) rho hrho
  intro p q
  apply triangularIsingSymbol_pos_of_third_le_neg hbeta
  nlinarith [mul_le_mul_of_nonneg_left hJ hbeta.le]

noncomputable def triangularKacWardPhaseRoot : Complex :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq Complex.I (by norm_num : 0 < 4))

theorem triangularKacWardPhaseRoot_pow_four :
    triangularKacWardPhaseRoot ^ 4 = Complex.I :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq Complex.I (by norm_num : 0 < 4))



theorem triangularTorusIsingPartition_freeEnergy_tendsto_ray
    (beta J : Real) (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  by_cases hJ : -1 < J
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one
      triangularKacWardPhaseRoot triangularKacWardPhaseRoot_pow_four hbeta hJ
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one
      triangularKacWardPhaseRoot triangularKacWardPhaseRoot_pow_four hbeta
        (le_of_not_gt hJ)

end StatMech.FrontierA
