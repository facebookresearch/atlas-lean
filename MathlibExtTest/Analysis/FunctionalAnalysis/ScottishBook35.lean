/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.BallSphere
import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35

/-!
# Tests for projective Hilbert space

The quotient identifies antipodal vectors and distinguishes perpendicular unit vectors.
The non-homeomorphism theorem applies to real square-summable sequences.
-/

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook35Wanted

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook35

private def unitOne : Metric.sphere (0 : ℂ) 1 :=
  ⟨1, by simp⟩

private def unitI : Metric.sphere (0 : ℂ) 1 :=
  ⟨Complex.I, by simp⟩

example : (Quot.mk _ unitOne : ProjectiveHilbertSpace ℂ) = Quot.mk _ (-unitOne) :=
  Quot.sound (Or.inr (by simp))

example : (Quot.mk _ unitOne : ProjectiveHilbertSpace ℂ) ≠ Quot.mk _ unitI := by
  intro h
  let absRealPart : ProjectiveHilbertSpace ℂ → ℝ :=
    Quot.lift (fun x : Metric.sphere (0 : ℂ) 1 => |(x : ℂ).re|) (by
      intro x y hxy
      rcases hxy with hxy | hxy <;> simp [hxy])
  have heq : |(1 : ℂ).re| = |Complex.I.re| := congrArg absRealPart h
  simp at heq

example : ¬ ProjectiveHilbertSpaceHomeomorphicToHilbertSpace (lp (fun _ : ℕ => ℝ) 2) := by
  apply projective_hilbert_space_not_homeomorphic_to_hilbert_space
  intro h
  let b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2) := default
  exact h.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent

end MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook35
