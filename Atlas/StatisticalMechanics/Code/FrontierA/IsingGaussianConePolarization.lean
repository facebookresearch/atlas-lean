/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianNewmanBridge
import Mathlib.LinearAlgebra.Lagrange











open Filter Finset Polynomial Topology

namespace StatMech.FrontierA



theorem polynomial_eval_tendsto_zero_of_nodes
    (degree : Nat) (p : Nat -> Real[X])
    (hdegree : forall scale, (p scale).degree < (degree + 1 : Nat))
    (hnodes : forall i : Fin (degree + 1),
      Tendsto (fun scale => (p scale).eval ((i : Nat) : Real))
        atTop (nhds 0))
    (x : Real) :
    Tendsto (fun scale => (p scale).eval x) atTop (nhds 0) := by
  let nodes : Fin (degree + 1) -> Real := fun i => ((i : Nat) : Real)
  have hnodesInjective : Function.Injective nodes := by
    intro i j hij
    apply Fin.ext
    change (((i : Nat) : Real) = ((j : Nat) : Real)) at hij
    exact_mod_cast hij
  have heval (scale : Nat) :
      (p scale).eval x =
        Finset.sum Finset.univ (fun i : Fin (degree + 1) =>
          (p scale).eval (nodes i) *
            (Lagrange.basis univ nodes i).eval x) := by
    have hp : p scale =
        Lagrange.interpolate (Finset.univ : Finset (Fin (degree + 1))) nodes
          (fun i => (p scale).eval (nodes i)) :=
      Lagrange.eq_interpolate hnodesInjective.injOn (by
        simpa using hdegree scale)
    calc
      (p scale).eval x =
          (Lagrange.interpolate
            (Finset.univ : Finset (Fin (degree + 1))) nodes
            (fun i => (p scale).eval (nodes i))).eval x :=
        congrArg (fun q : Real[X] => q.eval x) hp
      _ = _ := by
        simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  have hsum : Tendsto
      (fun scale => Finset.sum Finset.univ (fun i : Fin (degree + 1) =>
        (p scale).eval (nodes i) *
          (Lagrange.basis univ nodes i).eval x))
      atTop (nhds 0) := by
    simpa only [zero_mul, Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.univ : Finset (Fin (degree + 1))) (fun i _ =>
        (hnodes i).mul_const ((Lagrange.basis univ nodes i).eval x))
  convert hsum using 1
  funext scale
  exact heval scale


def smearingPositivePart {V : Type*} (a : V -> Real) : V -> Real :=
  fun v => max (a v) 0


def smearingNegativePart {V : Type*} (a : V -> Real) : V -> Real :=
  fun v => max (-a v) 0

theorem smearingPositivePart_nonneg {V : Type*} (a : V -> Real) (v : V) :
    0 <= smearingPositivePart a v := by
  simp [smearingPositivePart]

theorem smearingNegativePart_nonneg {V : Type*} (a : V -> Real) (v : V) :
    0 <= smearingNegativePart a v := by
  simp [smearingNegativePart]

theorem smearing_eq_positivePart_sub_negativePart
    {V : Type*} (a : V -> Real) :
    a = smearingPositivePart a - smearingNegativePart a := by
  funext v
  exact (max_zero_sub_max_neg_zero_eq_self (a v)).symm



noncomputable def smearingStrictShift
    {V : Type*} [Fintype V] (a : V -> Real) : Real :=
  1 + ∑ v : V, |a v|

noncomputable def smearingStrictPositivePart
    {V : Type*} [Fintype V] (a : V -> Real) : V -> Real :=
  fun v => a v + smearingStrictShift a

noncomputable def smearingStrictNegativePart
    {V : Type*} [Fintype V] (a : V -> Real) : V -> Real :=
  fun _ => smearingStrictShift a

theorem smearingStrictPositivePart_pos
    {V : Type*} [Fintype V] (a : V -> Real) (v : V) :
    0 < smearingStrictPositivePart a v := by
  classical
  have hv : |a v| <= ∑ w : V, |a w| :=
    Finset.single_le_sum (fun w _ => abs_nonneg (a w)) (Finset.mem_univ v)
  have hneg : -|a v| <= a v := neg_abs_le (a v)
  unfold smearingStrictPositivePart smearingStrictShift
  linarith

theorem smearingStrictNegativePart_pos
    {V : Type*} [Fintype V] (a : V -> Real) (v : V) :
    0 < smearingStrictNegativePart a v := by
  classical
  unfold smearingStrictNegativePart smearingStrictShift
  have hsum : 0 <= ∑ w : V, |a w| :=
    Finset.sum_nonneg fun w _ => abs_nonneg (a w)
  linarith

theorem smearing_eq_strictPositivePart_sub_strictNegativePart
    {V : Type*} [Fintype V] (a : V -> Real) :
    a = smearingStrictPositivePart a - smearingStrictNegativePart a := by
  funext v
  simp [smearingStrictPositivePart, smearingStrictNegativePart]



noncomputable def finiteWeightedCumulant
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real) (a : V -> Real) : Real :=
  ∑ x : Fin order -> V, ursell x * ∏ i : Fin order, a (x i)



noncomputable def finiteWeightedCumulantLinePolynomial
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) : Real[X] :=
  ∑ x : Fin order -> V, C (ursell x) *
    ∏ i : Fin order, (C (positive (x i)) + C (negative (x i)) * X)

theorem finiteWeightedCumulantLinePolynomial_eval
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) (r : Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).eval r =
      finiteWeightedCumulant order ursell (positive + r • negative) := by
  classical
  unfold finiteWeightedCumulantLinePolynomial finiteWeightedCumulant
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro x _
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [eval_add, eval_C, eval_mul, eval_X, Pi.add_apply,
    Pi.smul_apply]
  ring

theorem finiteWeightedCumulantLinePolynomial_natDegree_le
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).natDegree <=
      order := by
  classical
  unfold finiteWeightedCumulantLinePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  refine Polynomial.natDegree_mul_le.trans ?_
  have hprod :
      (∏ i : Fin order,
        (C (positive (x i)) + C (negative (x i)) * X)).natDegree <= order := by
    calc
      _ <= ∑ i : Fin order,
          (C (positive (x i)) + C (negative (x i)) * X).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ <= ∑ _i : Fin order, 1 := by
        apply Finset.sum_le_sum
        intro i _
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (by simp) ((Polynomial.natDegree_mul_le).trans (by simp)))
      _ = order := by simp
  simpa using hprod

theorem finiteWeightedCumulantLinePolynomial_degree_lt
    {V : Type*} [Fintype V] (order : Nat)
    (ursell : (Fin order -> V) -> Real)
    (positive negative : V -> Real) :
    (finiteWeightedCumulantLinePolynomial order ursell positive negative).degree <
      (order + 1 : Nat) := by
  exact lt_of_le_of_lt
    (Polynomial.degree_le_of_natDegree_le
      (finiteWeightedCumulantLinePolynomial_natDegree_le
        order ursell positive negative))
    (by exact_mod_cast Nat.lt_succ_self order)






theorem signedCumulant_tendsto_zero_of_nonnegative_line
    {E : Type*} [AddCommGroup E] [Module Real E]
    (order : Nat) (cumulant : Nat -> E -> Real)
    (linePolynomial : Nat -> E -> E -> Real[X])
    (hdegree : forall scale positive negative,
      (linePolynomial scale positive negative).degree < (order + 1 : Nat))
    (heval : forall scale positive negative r,
      (linePolynomial scale positive negative).eval r =
        cumulant scale (positive + r • negative))
    (positive negative signed : E)
    (hsigned : signed = positive - negative)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun scale => cumulant scale
          (positive + (((i : Nat) : Real) • negative)))
        atTop (nhds 0)) :
    Tendsto (fun scale => cumulant scale signed) atTop (nhds 0) := by
  have hpoly := polynomial_eval_tendsto_zero_of_nodes order
    (fun scale => linePolynomial scale positive negative)
    (fun scale => hdegree scale positive negative)
    (fun i => by simpa only [heval] using hnodes i) (-1)
  convert hpoly using 1
  funext scale
  rw [heval]
  simp only [neg_smul, one_smul, sub_eq_add_neg, hsigned]




theorem finiteWeightedCumulant_tendsto_zero_of_nonnegative_line
    {V : Type*} [Fintype V]
    (order : Nat) (ursell : Nat -> (Fin order -> V) -> Real)
    (positive negative signed : V -> Real)
    (hsigned : signed = positive - negative)
    (hnodes : forall i : Fin (order + 1),
      Tendsto
        (fun scale => finiteWeightedCumulant order (ursell scale)
          (positive + (((i : Nat) : Real) • negative)))
        atTop (nhds 0)) :
    Tendsto
      (fun scale => finiteWeightedCumulant order (ursell scale) signed)
      atTop (nhds 0) := by
  apply signedCumulant_tendsto_zero_of_nonnegative_line order
    (fun scale a => finiteWeightedCumulant order (ursell scale) a)
    (fun scale => finiteWeightedCumulantLinePolynomial order (ursell scale))
    (fun scale positive negative =>
      finiteWeightedCumulantLinePolynomial_degree_lt
        order (ursell scale) positive negative)
    (fun scale positive negative r =>
      finiteWeightedCumulantLinePolynomial_eval
        order (ursell scale) positive negative r)
    positive negative signed hsigned hnodes

end StatMech.FrontierA
