/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MinimalGradedResolutionBettiEq

/-!
# Tests for graded Betti invariance

The Betti table of a minimal resolution of the zero module vanishes.

Reference: Eisenbud, *Commutative Algebra with a View Toward Algebraic
Geometry*, Chapter 20, https://doi.org/10.1007/978-1-4612-5350-1.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MinimalGradedResolutionBettiEq

open MathlibExt.RingTheory.MinimalGradedResolution

private def zeroResolution {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M] [Subsingleton M]
    (G : Grading (k := k) (n := n) (M := M)) : MinimalResolution G where
  ranks _ := 0
  degrees _ := Fin.elim0
  differential _ := 0
  augmentation := 0
  differential_graded _ j _ _ := (freePiece Fin.elim0 j).zero_mem
  augmentation_graded j _ _ := (G.piece j).zero_mem
  augmentation_surjective m := ⟨0, Subsingleton.elim _ _⟩
  exact_zero := by ext x; simp [Subsingleton.elim x 0]
  exact_succ _ := by ext x; simp [Subsingleton.elim x 0]
  minimal _ := by simp
  length_bound _ _ := rfl

/-- The Betti table of a minimal resolution of the zero free module vanishes. -/
public theorem betti_zero {k : Type*} [Field k] {n : ℕ}
    (G : Grading (k := k) (n := n) (M := Fin 0 → PolynomialRing k n))
    (P : MinimalResolution G) (i : ℕ) (j : ℤ) : betti G P i j = 0 := by
  rw [WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted.betti_eq
    G P (zeroResolution G) i j]
  unfold betti
  have hEmpty : (Finset.univ : Finset (Fin ((zeroResolution G).ranks i))) = ∅ := by
    exact Finset.eq_empty_of_forall_notMem fun a _ ↦ Fin.elim0 a
  rw [hEmpty, Finset.filter_empty, Finset.card_empty]

end MathlibExtTest.AlgebraicGeometry.MinimalGradedResolutionBettiEq
