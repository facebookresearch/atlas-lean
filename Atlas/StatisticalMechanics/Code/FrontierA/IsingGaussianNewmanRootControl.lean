/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingGaussianNewmanBridge
import Mathlib.Topology.Algebra.InfiniteSum.Real









open scoped BigOperators

namespace StatMech.FrontierA

private theorem tsum_pow_le_sq_tsum_mul_tsum_pow
    (roots : Nat → Real) (m : Nat) (hm : 2 ≤ m)
    (hroots : ∀ i, 0 ≤ roots i) (hsum : Summable roots) :
    (∑' i, roots i ^ m) ≤
      (∑' i, roots i ^ 2) * (∑' i, roots i) ^ (m - 2) := by
  let total : Real := ∑' i, roots i
  have htotal : 0 ≤ total := tsum_nonneg hroots
  have hle (i : Nat) : roots i ≤ total := by
    exact hsum.le_tsum i fun j _ => hroots j
  have hsquare : Summable (fun i => roots i ^ 2) := by
    refine (hsum.mul_right total).of_nonneg_of_le
      (fun i => sq_nonneg (roots i)) ?_
    intro i
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hle i) (hroots i)
  have hpower : Summable (fun i => roots i ^ m) := by
    refine (hsquare.mul_right (total ^ (m - 2))).of_nonneg_of_le
      (fun i => pow_nonneg (hroots i) m) ?_
    intro i
    have hm' : m = 2 + (m - 2) := by omega
    have hpow' : roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := by
      calc
        roots i ^ m = roots i ^ (2 + (m - 2)) :=
          congrArg (fun n => roots i ^ n) hm'
        _ = roots i ^ 2 * roots i ^ (m - 2) := pow_add _ _ _
    calc
      roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := hpow'
      _ ≤ roots i ^ 2 * total ^ (m - 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hroots i) (hle i) (m - 2)) (sq_nonneg (roots i))
  calc
    (∑' i, roots i ^ m) ≤
        ∑' i, roots i ^ 2 * total ^ (m - 2) := by
      exact hpower.tsum_le_tsum (fun i => by
        have hm' : m = 2 + (m - 2) := by omega
        have hpow' : roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := by
          calc
            roots i ^ m = roots i ^ (2 + (m - 2)) :=
              congrArg (fun n => roots i ^ n) hm'
            _ = roots i ^ 2 * roots i ^ (m - 2) := pow_add _ _ _
        rw [hpow']
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hroots i) (hle i) (m - 2)) (sq_nonneg (roots i)))
        (hsquare.mul_right (total ^ (m - 2)))
    _ = (∑' i, roots i ^ 2) * total ^ (m - 2) :=
      hsquare.tsum_mul_right _





structure NewmanRootCumulantRepresentation
    (cumulants : Nat → Nat → Real) where
  roots : Nat → Nat → Real
  roots_nonneg : ∀ scale i, 0 ≤ roots scale i
  roots_summable : ∀ scale, Summable (roots scale)
  order_zero : ∀ scale, cumulants scale 0 = 0
  odd_order : ∀ scale order, Odd order → cumulants scale order = 0
  even_power_sum : ∀ scale halfOrder, 2 ≤ halfOrder →
    |cumulants scale (2 * halfOrder)| ≤
      (Nat.factorial (2 * halfOrder) : Real) *
        (∑' i, roots scale i ^ halfOrder)
  fourth_mass : ∀ scale,
    12 * (∑' i, roots scale i ^ 2) ≤
      |cumulants scale 4|
  variance_mass : ∀ scale,
    (∑' i, roots scale i) ≤ 1 + |cumulants scale 2|



theorem NewmanRootCumulantRepresentation.newmanFourthCumulantControl
    {cumulants : Nat → Nat → Real}
    (hroot : NewmanRootCumulantRepresentation cumulants) :
    NewmanFourthCumulantControl cumulants := by
  refine ⟨hroot.order_zero, hroot.odd_order, ?_⟩
  intro scale halfOrder hhalf
  let roots := hroot.roots scale
  have hnonneg : ∀ i, 0 ≤ roots i :=
    hroot.roots_nonneg scale
  have hsummable : Summable roots := hroot.roots_summable scale
  have hsum : 0 ≤ ∑' i, roots i := tsum_nonneg hnonneg
  have hsq : 0 ≤ ∑' i, roots i ^ 2 := tsum_nonneg fun _ => by positivity
  have hfactorial : 0 ≤ (Nat.factorial (2 * halfOrder) : Real) := by
    positivity
  have hpowers := tsum_pow_le_sq_tsum_mul_tsum_pow
    roots halfOrder hhalf hnonneg hsummable
  have hsqFourth : (∑' i, roots i ^ 2) ≤
      |cumulants scale 4| := by
    calc
      (∑' i, roots i ^ 2) ≤
          12 * (∑' i, roots i ^ 2) := by nlinarith
      _ ≤ |cumulants scale 4| := hroot.fourth_mass scale
  have hsumVariance : (∑' i, roots i) ^ (halfOrder - 2) ≤
      (1 + |cumulants scale 2|) ^ (halfOrder - 2) :=
    pow_le_pow_left₀ hsum (hroot.variance_mass scale) (halfOrder - 2)
  calc
    |cumulants scale (2 * halfOrder)| ≤
        (Nat.factorial (2 * halfOrder) : Real) *
          (∑' i, roots i ^ halfOrder) :=
      hroot.even_power_sum scale halfOrder hhalf
    _ ≤ (Nat.factorial (2 * halfOrder) : Real) *
          ((∑' i, roots i ^ 2) *
            (∑' i, roots i) ^ (halfOrder - 2)) :=
      mul_le_mul_of_nonneg_left hpowers hfactorial
    _ ≤ (Nat.factorial (2 * halfOrder) : Real) *
          (|cumulants scale 4| *
            (1 + |cumulants scale 2|) ^ (halfOrder - 2)) := by
      gcongr
    _ = (Nat.factorial (2 * halfOrder) : Real) *
          |cumulants scale 4| *
            (1 + |cumulants scale 2|) ^ (halfOrder - 2) := by ring

end StatMech.FrontierA
