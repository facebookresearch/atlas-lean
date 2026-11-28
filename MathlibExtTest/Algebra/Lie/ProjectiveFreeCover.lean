/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Lie.ProjectiveFreeCover
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import MathlibExtTest.Algebra.Category.LieModuleCat.Basic

/-!
# A projective free Lie cover with a nonzero central kernel

The matrix module over ZMod 6 is free and hence projective. Its free Lie cover projects
the generator labelled E₀₁ to E₀₁ and sends the lifted commutator of E₀₁,E₁₀ to their
nonzero matrix commutator. The generator labelled by the zero matrix is a nonzero
central element in the projection kernel.
-/

@[expose] public section

noncomputable section

namespace LieAlgebra.ProjectiveFreeCoverReviewTests

open LieModuleCat.ReviewTests

abbrev Cover := LieAlgebra.ProjectiveFreeCover R Mat

example : Module.Projective R Mat := inferInstance
example : Module.Free R Cover := inferInstance
example : LieAlgebra R Cover := inferInstance

def generator (a : Mat) : Cover := Finsupp.single a 1

lemma projection_generator (a : Mat) : LieAlgebra.projectiveCoverProjection R Mat (generator a) =
    a := by
  change Finsupp.linearCombination R (id : Mat → Mat) (Finsupp.single a 1) = a
  simp

example : LieAlgebra.projectiveCoverProjection R Mat (generator x) 0 1 = 1 ∧
    LieAlgebra.projectiveCoverProjection R Mat ⁅generator x, generator y⁆ 0 0 = 1 := by
  constructor
  · rw [projection_generator]
    norm_num [x]
  · rw [LieHom.map_lie, projection_generator, projection_generator]
    exact commutator_00

example : generator (0 : Mat) ≠ 0 ∧
    LieAlgebra.projectiveCoverProjection R Mat (generator 0) = 0 ∧
      ⁅generator (0 : Mat), generator x⁆ = 0 := by
  refine ⟨?_, projection_generator 0, ?_⟩
  · intro h
    have h' := congrArg (fun a : Cover =>
      LieAlgebra.projectiveFreeCoverEquiv R Mat a (0 : Mat)) h
    simp [generator, LieAlgebra.projectiveFreeCoverEquiv] at h'
  · exact LieAlgebra.projectiveFreeCover_lie_eq_zero_of_projection_eq_zero R Mat
      (generator 0) (generator x) (projection_generator 0)

end LieAlgebra.ProjectiveFreeCoverReviewTests

end
