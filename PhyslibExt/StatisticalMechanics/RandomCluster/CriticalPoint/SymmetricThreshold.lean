/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sharp threshold from symmetry and maximal influence

An abstract inequality: a Russo-type derivative bound, edge symmetry and a KKL maximal-influence
bound give a derivative lower bound of order `μ (1 - μ) log n`.

## i. Overview

This is an inequality between real numbers. Its hypotheses are the three inputs (derivative ≥
constant · total influence, total influence ≥ half the edge count times the maximal influence, KKL),
so it is conditional on all three.

## ii. Key results

- `symmetricThreshold_of_maxInfluence`: `(c_R c_M / 2) μ (1 - μ) log n ≤ deriv`, conditional on the
  three inputs.

## iii. Table of contents

- A. Symmetric threshold

## iv. References

* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
* E. Friedgut, G. Kalai, *Every monotone graph property has a sharp threshold*, Proc. AMS 124
  (1996).
-/

@[expose] public section

namespace StatMech
namespace BeffaraDC

/-! ## A. Symmetric threshold -/

lemma symmetricThreshold_of_maxInfluence
    {n edgeCount : ℕ} {μ deriv totalInfluence maxInfluence cRusso cMax : ℝ}
    (hn : 1 ≤ n) (hne : n ≤ edgeCount)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hcRusso : 0 ≤ cRusso) (hcMax : 0 ≤ cMax)
    (hderiv : cRusso * totalInfluence ≤ deriv)
    (hsymm : (edgeCount : ℝ) / 2 * maxInfluence ≤ totalInfluence)
    (hmax : cMax * μ * (1 - μ) * Real.log (edgeCount : ℝ) / edgeCount
      ≤ maxInfluence) :
    (cRusso * cMax / 2) * μ * (1 - μ) * Real.log (n : ℝ) ≤ deriv := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have heposNat : 0 < edgeCount := lt_of_lt_of_le Nat.zero_lt_one (hn.trans hne)
  have hepos : (0 : ℝ) < edgeCount := by exact_mod_cast heposNat
  have hnreal : (n : ℝ) ≤ edgeCount := by exact_mod_cast hne
  have hlog : Real.log (n : ℝ) ≤ Real.log (edgeCount : ℝ) :=
    Real.log_le_log hnpos hnreal
  have hvariance : 0 ≤ μ * (1 - μ) :=
    mul_nonneg hμ0 (sub_nonneg.mpr hμ1)
  have horbit : 0 ≤ (edgeCount : ℝ) / 2 := by positivity
  have hmaxScaled := mul_le_mul_of_nonneg_left hmax horbit
  have htotal : (cMax / 2) * μ * (1 - μ) * Real.log (edgeCount : ℝ)
      ≤ totalInfluence := by
    apply le_trans _ hsymm
    calc
      (cMax / 2) * μ * (1 - μ) * Real.log (edgeCount : ℝ)
          = ((edgeCount : ℝ) / 2) *
              (cMax * μ * (1 - μ) * Real.log (edgeCount : ℝ) / edgeCount) := by
              field_simp
      _ ≤ (edgeCount : ℝ) / 2 * maxInfluence := hmaxScaled
  have htotalScaled := mul_le_mul_of_nonneg_left htotal hcRusso
  have hlogScaled : (cRusso * cMax / 2) * μ * (1 - μ) * Real.log (n : ℝ)
      ≤ (cRusso * cMax / 2) * μ * (1 - μ) * Real.log (edgeCount : ℝ) := by
    exact mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hcRusso hcMax) (by norm_num)) hμ0)
        (sub_nonneg.mpr hμ1))
  apply hlogScaled.trans
  apply (show (cRusso * cMax / 2) * μ * (1 - μ) * Real.log (edgeCount : ℝ)
      = cRusso * ((cMax / 2) * μ * (1 - μ) * Real.log (edgeCount : ℝ)) by ring).le.trans
  exact htotalScaled.trans hderiv

end BeffaraDC
end StatMech
