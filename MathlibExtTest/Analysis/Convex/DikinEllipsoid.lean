/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.DikinEllipsoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open Filter Set
open scoped Topology
open MathlibExt.Analysis.Convex.SelfConcordant
  (isSelfConcordantBarrier_neg_log mem_of_dikin_lt_one)

/-- A nonzero step of local length `1/2` for the logarithmic barrier stays on the positive ray. -/
example : (1 / 2 : ℝ) ∈ Ioi (0 : ℝ) := by
  refine mem_of_dikin_lt_one (E := ℝ) (F := fun x : ℝ => -Real.log x) (Q := Ioi (0 : ℝ))
    isSelfConcordantBarrier_neg_log.2.1 (x := (1 : ℝ)) (y := (1 / 2 : ℝ)) (by norm_num) ?_
  let f (t : ℝ) := -Real.log (1 + t * (1 / 2 - 1))
  let u (t : ℝ) := 1 + t * (1 / 2 - 1)
  have hu : ∀ᶠ t in 𝓝 (0 : ℝ), u t ≠ 0 := by
    have hc : Continuous u := by dsimp only [u]; fun_prop
    exact hc.continuousAt.eventually_ne (by norm_num [u])
  have ha (t : ℝ) : HasDerivAt u (1 / 2 - 1) t := by
    simpa only [u, id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const (1 / 2 - 1 : ℝ)).const_add 1
  have hderiv (t : ℝ) (ht : u t ≠ 0) :
      HasDerivAt f (-(1 / 2 - 1) / u t) t := by
    convert ((ha t).log ht).neg using 1
    exact neg_div _ _
  have he : deriv f =ᶠ[𝓝 (0 : ℝ)] fun t => -(1 / 2 - 1) / u t :=
    hu.mono fun t ht => (hderiv t ht).deriv
  have hquot : HasDerivAt (fun t => -(1 / 2 - 1) / u t) (1 / 4) 0 := by
    convert (hasDerivAt_const (0 : ℝ) (-(1 / 2 - 1) : ℝ)).div (ha 0)
      (by norm_num [u]) using 1
    norm_num [u]
  change iteratedDeriv 2 f 0 < 1
  rw [iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq, hquot.deriv]
  norm_num
