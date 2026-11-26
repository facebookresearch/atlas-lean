/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.NumberTheory.QuadraticForms.HermitianLatticeMass
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

open HermitianLattice NumberField
open scoped NumberField TensorProduct BigOperators nonZeroDivisors

-- These toy Gaussian residue counts are sanity checks, not tests of `normalizedCount`.
private def gaussianCount (n s : ℕ) [NeZero n] : ℕ :=
  ((Finset.univ : Finset (ZMod n × ZMod n)).filter
    (fun z ↦ (s : ZMod n) * (z.1 ^ 2 + z.2 ^ 2) = (s : ZMod n))).card

example : gaussianCount 5 1 = 4 := by decide
example : gaussianCount 25 1 = 20 := by decide
example : gaussianCount 3 1 = 4 := by decide
example : gaussianCount 9 1 = 12 := by decide
example : gaussianCount 3 3 = 9 := by decide
example : gaussianCount 9 3 = 36 := by decide

example : referenceCoefficient .split 5 1 = (4 : ℝ) / 5 := by
  norm_num [referenceCoefficient, Finset.prod_range_succ]

example : referenceCoefficient .inert 3 1 = (4 : ℝ) / 3 := by
  norm_num [referenceCoefficient, Finset.prod_range_succ]

example : referenceCoefficient .ramified 2 1 = 1 := by
  norm_num [referenceCoefficient]

example : normExponent .ramified 2 1 1 = (1 : ℝ) / 2 := by
  norm_num [normExponent, discriminantCorrection, Nat.even_iff]

example : normExponent .ramified 2 2 0 = (2 : ℝ) := by
  norm_num [normExponent, discriminantCorrection, Nat.even_iff]

example : (2 : ℝ) ^ (2 : ℕ) * referenceCoefficient .ramified 2 2 = 3 := by
  norm_num [referenceCoefficient, Finset.prod_range_succ]

section Structural

variable {K E V : Type*} [Field K] [NumberField K] [IsTotallyReal K]
  [Field E] [NumberField E] [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
  [AddCommGroup V] [Module E V] [Module.Finite E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) (𝓞 E) V]
  [IsScalarTower (𝓞 K) E V]
  (h : DefiniteForm K E V) (L : FullLattice E V)
  (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

example : Function.Injective (completionInclusion (E := E) p (dual h L)) :=
  completionInclusion_injective (E := E) p (dual h L)

end Structural
