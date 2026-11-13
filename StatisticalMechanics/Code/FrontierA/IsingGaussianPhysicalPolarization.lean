/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianPhysicalCumulants
import Code.FrontierA.IsingGaussianConePolarization










open Filter Finset Polynomial Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def finiteIsingWeightedRawMomentLinePolynomial
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) : Real[X] :=
  C ((∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s)⁻¹) *
    ∑ s : ConfigSpace V, C (zeroFieldInteractionWeight G beta s) *
      (C (finiteIsingWeightedSpinReal positive s) +
        X * C (finiteIsingWeightedSpinReal direction s)) ^ order

omit [DecidableEq V] in
private theorem finiteIsingWeightedSpinReal_line
    (positive direction : V -> Real) (r : Real) (s : ConfigSpace V) :
    finiteIsingWeightedSpinReal (positive + r • direction) s =
      finiteIsingWeightedSpinReal positive s +
        r * finiteIsingWeightedSpinReal direction s := by
  unfold finiteIsingWeightedSpinReal
  simp_rw [Pi.add_apply, Pi.smul_apply, add_mul, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

theorem finiteIsingWeightedRawMomentLinePolynomial_eval
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) (r : Real) :
    (finiteIsingWeightedRawMomentLinePolynomial
      G beta positive direction order).eval r =
      finiteIsingWeightedRawMoment G beta
        (positive + r • direction) order := by
  unfold finiteIsingWeightedRawMomentLinePolynomial
    finiteIsingWeightedRawMoment
  rw [eval_mul, eval_C, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [finiteIsingWeightedSpinReal_line]

theorem finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
    (beta : Real) (positive direction : V -> Real) (order : Nat) :
    (finiteIsingWeightedRawMomentLinePolynomial
      G beta positive direction order).natDegree <= order := by
  unfold finiteIsingWeightedRawMomentLinePolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  have hsum :
      (∑ s : ConfigSpace V, C (zeroFieldInteractionWeight G beta s) *
        (C (finiteIsingWeightedSpinReal positive s) +
          X * C (finiteIsingWeightedSpinReal direction s)) ^ order).natDegree <=
        order := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    refine Polynomial.natDegree_mul_le.trans ?_
    have hlinear :
        (C (finiteIsingWeightedSpinReal positive s) +
          X * C (finiteIsingWeightedSpinReal direction s)).natDegree <= 1 :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le (by simp)
          ((Polynomial.natDegree_mul_le).trans (by simp)))
    have hpow := Polynomial.natDegree_pow_le_of_le order hlinear
    simpa using hpow
  simpa using hsum



def scalarCumulantLinePolynomial (moments : Nat -> Real[X]) : Nat -> Real[X]
  | 0 => 0
  | n + 1 => moments (n + 1) -
      ∑ k : Fin n, C (n.choose k : Real) *
        scalarCumulantLinePolynomial moments (k + 1) * moments (n - k)
termination_by order => order
decreasing_by omega

theorem scalarCumulantLinePolynomial_succ
    (moments : Nat -> Real[X]) (n : Nat) :
    scalarCumulantLinePolynomial moments (n + 1) = moments (n + 1) -
      ∑ k : Fin n, C (n.choose k : Real) *
        scalarCumulantLinePolynomial moments (k + 1) * moments (n - k) := by
  rw [scalarCumulantLinePolynomial]

theorem scalarCumulantLinePolynomial_eval
    (moments : Nat -> Real[X]) (r : Real) :
    forall order,
      (scalarCumulantLinePolynomial moments order).eval r =
        scalarCumulantsOfMoments (fun m => (moments m).eval r) order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp [scalarCumulantLinePolynomial,
          scalarCumulantsOfMoments_zero]
      | succ n =>
          rw [scalarCumulantLinePolynomial_succ,
            scalarCumulantsOfMoments_succ, eval_sub, eval_finsetSum]
          apply congrArg (fun x => (moments (n + 1)).eval r - x)
          apply Finset.sum_congr rfl
          intro k _
          simp only [eval_mul, eval_C]
          rw [ih (k.val + 1) (by omega)]

theorem scalarCumulantLinePolynomial_natDegree_le
    (moments : Nat -> Real[X])
    (hmoments : forall order, (moments order).natDegree <= order) :
    forall order,
      (scalarCumulantLinePolynomial moments order).natDegree <= order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp [scalarCumulantLinePolynomial]
      | succ n =>
          rw [scalarCumulantLinePolynomial_succ]
          apply (Polynomial.natDegree_sub_le _ _).trans
          apply max_le (hmoments (n + 1))
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro k _
          refine Polynomial.natDegree_mul_le.trans ?_
          refine (Nat.add_le_add Polynomial.natDegree_mul_le
            (hmoments (n - k.val))).trans ?_
          rw [Polynomial.natDegree_C]
          have hcumulant := ih (k.val + 1) (by omega)
          omega



def finiteIsingWeightedCumulantLinePolynomial
    (beta : Real) (positive direction : V -> Real) (order : Nat) : Real[X] :=
  scalarCumulantLinePolynomial
    (finiteIsingWeightedRawMomentLinePolynomial G beta positive direction) order

theorem finiteIsingWeightedCumulantLinePolynomial_eval
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) (r : Real) :
    (finiteIsingWeightedCumulantLinePolynomial
      G beta positive direction order).eval r =
      PhysicalIsing.finiteIsingWeightedCumulant G beta
        (positive + r • direction) order := by
  unfold finiteIsingWeightedCumulantLinePolynomial
    PhysicalIsing.finiteIsingWeightedCumulant
  rw [scalarCumulantLinePolynomial_eval]
  congr 1
  funext m
  exact finiteIsingWeightedRawMomentLinePolynomial_eval
    G beta positive direction m r

theorem finiteIsingWeightedCumulantLinePolynomial_degree_lt
    (beta : Real) (positive direction : V -> Real) (order : Nat) :
    (finiteIsingWeightedCumulantLinePolynomial
      G beta positive direction order).degree < (order + 1 : Nat) := by
  apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le ?_)
    (by exact_mod_cast Nat.lt_succ_self order)
  exact scalarCumulantLinePolynomial_natDegree_le _
    (finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
      G beta positive direction) order

namespace PhysicalIsing



noncomputable def criticalFiniteBoxWeightedScaledCumulantLinePolynomial
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) : Real[X] :=
  C (criticalFiniteBoxWeightedFourthScale d n hd ^ order) *
    finiteIsingWeightedCumulantLinePolynomial
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
        positive direction order

theorem criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) (r : Real) :
    (criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd positive direction order).eval r =
      criticalFiniteBoxWeightedScaledCumulant d n hd
        (positive + r • direction) order := by
  unfold criticalFiniteBoxWeightedScaledCumulantLinePolynomial
    criticalFiniteBoxWeightedScaledCumulant
  rw [eval_mul, eval_C,
    finiteIsingWeightedCumulantLinePolynomial_eval,
    finiteIsingWeighted_scaledCumulants]

theorem criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) :
    (criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd positive direction order).degree < (order + 1 : Nat) := by
  apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le ?_)
    (by exact_mod_cast Nat.lt_succ_self order)
  unfold criticalFiniteBoxWeightedScaledCumulantLinePolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C]
  simpa [finiteIsingWeightedCumulantLinePolynomial] using
    scalarCumulantLinePolynomial_natDegree_le
      (finiteIsingWeightedRawMomentLinePolynomial
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
          positive direction)
      (finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
          positive direction) order




theorem criticalFiniteBoxWeightedScaledCumulant_tendsto_zero_of_nonnegative_line
    (d order : Nat) (hd : 2 <= d)
    (positive negative signed : (n : Nat) -> sctBox d n -> Real)
    (hsigned : forall n, signed n = positive n - negative n)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun n => criticalFiniteBoxWeightedScaledCumulant d n hd
          (positive n + (((i : Nat) : Real) • negative n)) order)
        atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedScaledCumulant
        d n hd (signed n) order) atTop (nhds 0) := by
  have hpoly := polynomial_eval_tendsto_zero_of_nodes order
    (fun n => criticalFiniteBoxWeightedScaledCumulantLinePolynomial
      d n hd (positive n) (negative n) order)
    (fun n => criticalFiniteBoxWeightedScaledCumulantLinePolynomial_degree_lt
      d n hd (positive n) (negative n) order)
    (fun i => by
      simpa only [criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval]
        using hnodes i) (-1)
  convert hpoly using 1
  funext n
  rw [criticalFiniteBoxWeightedScaledCumulantLinePolynomial_eval, hsigned n]
  simp only [neg_smul, one_smul]
  rw [sub_eq_add_neg]

end PhysicalIsing

end

end StatMech.FrontierA
