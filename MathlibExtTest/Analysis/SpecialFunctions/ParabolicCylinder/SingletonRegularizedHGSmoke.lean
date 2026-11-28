/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.Basic
import Mathlib.Tactic.NormNum

public section

noncomputable section

open Complex

-- A negative-integer denominator parameter is permitted; its initial Gamma pole gives zero.
example : regularizedHGFunCoeff ({Complex.I} : Multiset ℂ) ({-1} : Multiset ℂ) 0 = 0 := by
  have hGamma : Gamma (-1 : ℂ) = 0 := by
    simpa only [Nat.cast_one] using Gamma_neg_nat_eq_zero 1
  norm_num [regularizedHGFunCoeff_singleton_eq, hGamma]

-- The same pole parameter has a nonzero, nonreal later coefficient.
example : regularizedHGFunCoeff ({Complex.I} : Multiset ℂ) ({-1} : Multiset ℂ) 2 =
    (-1 + Complex.I) / 2 := by
  norm_num [regularizedHGFunCoeff_singleton_eq, ascPochhammer_succ_eval,
    mul_add, add_mul, Complex.I_mul_I]

-- Regularization and numerator termination leave exactly one quadratic term at z=i.
example : regularizedHGFun ({-2} : Multiset ℂ) ({-1} : Multiset ℂ) Complex.I = -1 := by
  have hcoeff (n : ℕ) :
      regularizedHGFunCoeff ({-2} : Multiset ℂ) ({-1} : Multiset ℂ) n =
        if n = 2 then 1 else 0 := by
    cases n with
    | zero =>
      have hGamma : Gamma (-1 : ℂ) = 0 := by
        simpa only [Nat.cast_one] using Gamma_neg_nat_eq_zero 1
      norm_num [regularizedHGFunCoeff_singleton_eq, hGamma]
    | succ n =>
      cases n with
      | zero => norm_num [regularizedHGFunCoeff_singleton_eq, ascPochhammer_succ_eval]
      | succ n =>
        cases n with
        | zero => norm_num [regularizedHGFunCoeff_singleton_eq, ascPochhammer_succ_eval]
        | succ n =>
          have hn : 2 < n.succ.succ.succ :=
            Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ n))
          have hz := regularizedHGFunCoeff_eq_zero_left
            ({-2} : Multiset ℂ) ({-1} : Multiset ℂ) n.succ.succ.succ 2 (by simp) hn
          simp only [hz, ite_eq_right (Nat.ne_of_gt hn)]
  have hterm :
      (fun n : ℕ => regularizedHGFunCoeff ({-2} : Multiset ℂ) ({-1} : Multiset ℂ) n *
        Complex.I ^ n) = fun n : ℕ => if n = 2 then (-1 : ℂ) else 0 := by
    funext n
    rw [hcoeff n]
    by_cases hn : n = 2
    · subst n
      simp only [ite_true, one_mul, Complex.I_sq]
    · simp only [ite_eq_right hn, zero_mul]
  have hseries := hasSum_regularizedHGFun_singleton (-2) (-1) Complex.I
  rw [hterm] at hseries
  exact hseries.unique (hasSum_ite_eq 2 (-1 : ℂ))
