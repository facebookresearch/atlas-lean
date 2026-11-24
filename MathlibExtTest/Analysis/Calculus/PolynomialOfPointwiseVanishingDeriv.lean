/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum

open Set MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted
open scoped ContDiff

-- The linear function has zero second derivative, including the one-sided endpoint derivatives.
example : ∃ p : Polynomial ℝ, p.eval 0 = 0 ∧ p.eval 1 = 1 := by
  obtain ⟨p, hp⟩ := exists_polynomial_eq_of_forall_exists_iteratedDerivWithin_eq_zero (fun x : ℝ => x)
    contDiff_id.contDiffOn (fun x hx => by
      refine ⟨2, ?_⟩
      norm_num [iteratedDerivWithin_fun_id hx (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))])
  exact ⟨p, (hp 0 (by norm_num)).symm, (hp 1 (by norm_num)).symm⟩
