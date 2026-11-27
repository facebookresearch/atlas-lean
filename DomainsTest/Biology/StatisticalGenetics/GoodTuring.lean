/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.GoodTuring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

namespace DomainsTest.Biology.StatisticalGenetics.GoodTuring

open Finset WantedExt.Biology.StatisticalGenetics.GoodTuringWanted

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : ∑ a, p a = 1) :
    expect 1 p (fun ω => (freqOfFreq ω 1 : ℝ)) = 1 := by
  have h := expect_missingMass p hp hp₁ 0
  simpa [expect, massSeen, count, sampleProb, hp₁] using h.symm

example :
    expect 1 (fun _ : Fin 2 => (1 / 2 : ℝ))
        (fun ω => massSeen (fun _ => (1 / 2 : ℝ)) ω 0) =
      expect 2 (fun _ : Fin 2 => (1 / 2 : ℝ))
        (fun ω => (freqOfFreq ω 1 : ℝ)) / 2 := by
  convert expect_missingMass (fun _ : Fin 2 => (1 / 2 : ℝ))
    (by intro a; norm_num) (by norm_num) 1 using 1
  norm_num

example :
    expect 2 (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)
        (fun ω => massSeen (fun a => if a = 0 then (1 : ℝ) else 0) ω 0) =
      expect 3 (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)
        (fun ω => (freqOfFreq ω 1 : ℝ)) / 3 := by
  convert expect_missingMass (fun a : Fin 2 => if a = 0 then (1 : ℝ) else 0)
    (by intro a; split_ifs <;> norm_num) (by norm_num) 2 using 1
  norm_num

end DomainsTest.Biology.StatisticalGenetics.GoodTuring
