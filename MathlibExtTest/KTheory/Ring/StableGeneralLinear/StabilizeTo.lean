/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.StabilizeTo

@[expose] public section

namespace MathlibExtTest.AlgebraicKTheory.StableGL.StabilizeTo

universe u

private theorem diagram_comparison
    (R : Type u) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.stabilizeTo R h g =
      (AlgebraicKTheory.finiteGLDiagram.obj (SemiRingCat.of R)).map
        (CategoryTheory.homOfLE h) g :=
  AlgebraicKTheory.StableGL.stabilizeTo_eq_finiteGLDiagram_map R h g

private theorem stable_class
    (R : Type u) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    AlgebraicKTheory.StableGL.of
        (Matrix.GeneralLinearGroup.stabilizeTo R h g) =
      AlgebraicKTheory.StableGL.of g :=
  AlgebraicKTheory.StableGL.of_stabilizeTo h g

private abbrev ZeroSemiring := Fin 0 → ℕ

private theorem zero_stage_stable_class (N : ℕ) :
    AlgebraicKTheory.StableGL.of
        (Matrix.GeneralLinearGroup.stabilizeTo ZeroSemiring
          (Nat.zero_le N)
          (1 : Matrix.GeneralLinearGroup (Fin 0) ZeroSemiring)) =
      AlgebraicKTheory.StableGL.of
        (1 : Matrix.GeneralLinearGroup (Fin 0) ZeroSemiring) :=
  AlgebraicKTheory.StableGL.of_stabilizeTo (Nat.zero_le N) 1

#print axioms diagram_comparison
#print axioms stable_class
#print axioms zero_stage_stable_class

end MathlibExtTest.AlgebraicKTheory.StableGL.StabilizeTo
