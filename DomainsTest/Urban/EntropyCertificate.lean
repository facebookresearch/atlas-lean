/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Urban.EntropyCertificate
import Mathlib.Tactic.NormNum

/-!
# Entropy-certificate checks

Focused checks for `MathlibExt.Urban.EntropyCertificate`: a
`2 × 2` margin-preserving table with a zero entry
(`S = [[2, 0], [1, 3]]` against `T = [[1, 1], [2, 2]]`) has a
nonnegative optimality certificate.

These are elaboration and non-vacuity checks, not new results.
-/

open InformationTheory

/-- The certificate of the margin-preserving perturbation is
nonnegative. -/
example : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      ((fun i => if i = 0 then (1 : ℝ) else 2) i
        * (fun _ _ => (1 : ℝ)) i j * (fun _ => (1 : ℝ)) j)
      * klFun ((fun i j => if i = 0 then (if j = 0 then (2 : ℝ) else 0)
            else (if j = 0 then 1 else 3)) i j
          / ((fun i => if i = 0 then (1 : ℝ) else 2) i
            * (fun _ _ => (1 : ℝ)) i j * (fun _ => (1 : ℝ)) j)) :=
  (SinkhornMargins.entropy_optimality_certificate (ι := Fin 2) (κ := Fin 2)
    (K := fun _ _ => (1 : ℝ))
    (S := fun i j => if i = 0 then (if j = 0 then (2 : ℝ) else 0)
      else (if j = 0 then 1 else 3))
    (a := fun i => if i = 0 then (1 : ℝ) else 2)
    (b := fun _ => (1 : ℝ))
    (by simp) (by intro i; fin_cases i <;> simp)
    (by simp)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp)
    (by intro i; fin_cases i <;> norm_num [Fin.sum_univ_two])
    (by intro j; fin_cases j <;> norm_num [Fin.sum_univ_two])).2
