/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperharmonicPrimeSumsAlternatingHyperharmonicTypeIIIIsEquivalent
import MathlibExt.NumberTheory.AlternatingHyperharmonicTypeIIISquarefree
import MathlibExt.Analysis.Asymptotics.Jakimczuk
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.NumberTheory.GeneralizedHarmonicGamma

/-!
# Tests for type III alternating hyperharmonic asymptotics

These examples use all four asymptotics at order parameter two.
-/

namespace MathlibExtTest.NumberTheory
namespace HyperharmonicPrimeSumsAlternatingHyperharmonicTypeIIIIsEquivalent

open MetaMathlibExt Asymptotics Filter

example : (fun n : ℕ =>
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 5 n) ~[atTop]
    fun n : ℕ => (n : ℝ) ^ 2 * Real.log 2 / 8 := by
  simpa [alternatingZeta_one, Nat.factorial] using
    (alternatingHyperharmonic_typeIII_isEquivalent (y := 2) (p := 1)
      (by decide) (by decide)).1

example : (fun n : ℕ =>
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic 1) 4 n) ~[atTop]
    fun n : ℕ => (n : ℝ) * Real.log n / 4 := by
  simpa [Nat.factorial] using
    (alternatingHyperharmonic_typeIII_isEquivalent (y := 2) (p := 1)
      (by decide) (by decide)).2.1

example : (fun n : ℕ =>
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic 2) 4 (2 * n)) ~[atTop]
    fun n : ℕ => (n : ℝ) * ((∑' i : ℕ, 1 / (i : ℝ) ^ 2) - alternatingZeta 2) / 2 := by
  simpa [Nat.factorial] using
    (alternatingHyperharmonic_typeIII_isEquivalent (y := 2) (p := 2)
      (by decide) (by decide)).2.2.1 (by decide)

example : (fun n : ℕ =>
    signedIteratedPartialSum true (alternatingGeneralizedHarmonic 2) 4 (2 * n - 1)) ~[atTop]
    fun n : ℕ => (n : ℝ) * ((∑' i : ℕ, 1 / (i : ℝ) ^ 2) + alternatingZeta 2) / 2 := by
  simpa [Nat.factorial] using
    (alternatingHyperharmonic_typeIII_isEquivalent (y := 2) (p := 2)
      (by decide) (by decide)).2.2.2 (by decide)

end HyperharmonicPrimeSumsAlternatingHyperharmonicTypeIIIIsEquivalent
end MathlibExtTest.NumberTheory
