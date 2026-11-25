/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ProcessBalances.SpeciesBalanceScaling
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum

open Domains.Chemistry.ProcessBalances.SpeciesBalanceScaling

-- The old endpoint 6 becomes 3; the accumulation rate of 2 becomes 12.
example : HasDerivWithinAt (fun u : ℝ => 3 * (2 * (2 * u) + 1)) 12
    {u : ℝ | 2 * u ∈ Set.Icc (0 : ℝ) 6} 3 := by
  let I := Set.Icc (0 : ℝ) 6
  have h : ∀ (_ : Unit) (t : ℝ), t ∈ I →
      HasDerivWithinAt (fun u : ℝ => 2 * u + 1) ((4 : ℝ) - 3 + 1) I t := by
    intro i t _
    have hid : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
    have hd : HasDerivAt (fun u : ℝ => 2 * u + 1) (2 * 1) t :=
      (hid.const_mul 2).add_const 1
    have hrate : (4 : ℝ) - 3 + 1 = 2 * 1 := by norm_num
    simpa only [hrate] using hd.hasDerivWithinAt (s := I)
  have hs := (species_balance_scaling_iff (S := Unit) I (fun _ u => 2 * u + 1)
    (fun _ _ => 4) (fun _ _ => 3) (fun _ _ => 1) 3 2 (by norm_num) (by norm_num)).mp h
    () 3 (by norm_num [I])
  have hrate : (3 * 2) * (4 : ℝ) - (3 * 2) * 3 + (3 * 2) * 1 = 12 := by norm_num
  simpa only [hrate] using hs

-- Conversely, the scaled balance recovers the derivative in the original units.
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 6) :
    HasDerivWithinAt (fun u : ℝ => 2 * u + 1) 2 (Set.Icc (0 : ℝ) 6) t := by
  let I := Set.Icc (0 : ℝ) 6
  have h : ∀ (_ : Unit) (s : ℝ), 2 * s ∈ I →
      HasDerivWithinAt (fun u : ℝ => 3 * (2 * (2 * u) + 1))
        ((3 * 2) * (4 : ℝ) - (3 * 2) * 3 + (3 * 2) * 1) {u : ℝ | 2 * u ∈ I} s := by
    intro i s _
    have hid : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id' s
    have hd : HasDerivAt (fun u : ℝ => 3 * (2 * (2 * u) + 1)) (3 * (2 * (2 * 1))) s :=
      (((hid.const_mul 2).const_mul 2).add_const 1).const_mul 3
    have hrate : (3 * 2) * (4 : ℝ) - (3 * 2) * 3 + (3 * 2) * 1 = 3 * (2 * (2 * 1)) := by
      norm_num
    simpa only [hrate] using hd.hasDerivWithinAt (s := {u : ℝ | 2 * u ∈ I})
  have hd := (species_balance_scaling_iff (S := Unit) I (fun _ u => 2 * u + 1)
    (fun _ _ => 4) (fun _ _ => 3) (fun _ _ => 1) 3 2 (by norm_num) (by norm_num)).mpr h () t ht
  have hrate : (4 : ℝ) - 3 + 1 = 2 := by norm_num
  simpa only [hrate] using hd
