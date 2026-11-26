/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RubberModuliStackModels
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
For y=z^2 the source scaling z maps to 2z forces the target scaling
y maps to 4y. The actual native affine scheme square commutes. Fixing
the original target contraction would discard this rubber isomorphism.
The example is the affine chart of the two-endpoint-marked genus-zero
map; its continuous combined scaling is why that unrigidified map is
excluded by finite combined automorphisms.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open Polynomial

noncomputable section

private def scale (c : ℚ) : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (C c * X)
private def degreeTwo : ℚ[X] →ₐ[ℚ] ℚ[X] := aeval (X ^ 2)

private theorem combined : (scale 2).comp degreeTwo = degreeTwo.comp (scale 4) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, degreeTwo, scale, aeval_X, map_mul, map_pow, aeval_C]
  change (C (2 : ℚ) * X) ^ 2 = C (4 : ℚ) * X ^ 2
  rw [mul_pow, ← map_pow]
  norm_num

example :
    Spec.map (CommRingCat.ofHom (scale 2).toRingHom) ≫
      Spec.map (CommRingCat.ofHom degreeTwo.toRingHom) =
    Spec.map (CommRingCat.ofHom degreeTwo.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (scale 4).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun h : ℚ[X] →ₐ[ℚ] ℚ[X] => Spec.map (CommRingCat.ofHom h.toRingHom)) combined

example : scale 4 ≠ AlgHom.id ℚ ℚ[X] := by
  intro h
  have hX := congrArg (fun h : ℚ[X] →ₐ[ℚ] ℚ[X] => h X) h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hX
  norm_num [scale] at hc

example : (2 : ℚ) * 1 ≠ 1 := by norm_num
