/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Tactic.NormNum

/-!
# Quasimap homogeneous and nonreduced normalization checks

Repeated regular coefficients remain different homogeneous elements.
The doubled origin keeps its nonzero nilpotent coordinate, which would
be erased by replacing the source unstable ideal with its radical.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.QuasimapSourceNormalizations

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LinearizedLineBundles
open MathlibExt.AlgebraicGeometry.QuasimapBasepointDefects
open MathlibExt.AlgebraicGeometry.QuasimapInvariantAlgebras

section Homogeneous

variable {S : Scheme} {G W : Over S} [GrpObj G] [ModObj G W]
  (L : CharacterPolarization G W) [InvariantAlgebraModel G W L]
  [Nontrivial Γ(W.left, ⊤)]
  (h1 : (1 : Γ(W.left, ⊤)) ∈ invariantPiece G W L 1)

def zeroUnit : InvariantAlgebra G W L :=
  DirectSum.of (fun m => ↥(invariantPiece G W L m)) 0 ⟨1,SetLike.one_mem_graded _⟩

def oneUnit : InvariantAlgebra G W L :=
  DirectSum.of (fun m => ↥(invariantPiece G W L m)) 1 ⟨1,h1⟩

example : zeroUnit L ≠ oneUnit L h1 := by
  intro h
  have hc := congrArg (fun x : InvariantAlgebra G W L => (x 0).val) h
  simp [zeroUnit, oneUnit, DirectSum.of_eq_of_ne] at hc

example : DirectSum.coeRingHom (invariantPiece G W L) (zeroUnit L) =
    DirectSum.coeRingHom (invariantPiece G W L) (oneUnit L h1) := by
  simp [zeroUnit, oneUnit]

end Homogeneous

abbrev Dual := TrivSqZeroExt ℚ ℚ

def epsilon : Dual := TrivSqZeroExt.inr 1

def doubleIdeal : Ideal (Polynomial ℚ) := Ideal.span {Polynomial.X ^ 2}

def doubleCoordinate : Polynomial ℚ ⧸ doubleIdeal :=
  Ideal.Quotient.mk doubleIdeal Polynomial.X

def evaluateNilpotent : Polynomial ℚ →+* Dual :=
  Polynomial.eval₂RingHom (algebraMap ℚ Dual) epsilon

example : doubleCoordinate ^ 2 = 0 := by
  have h : Ideal.Quotient.mk doubleIdeal (Polynomial.X ^ 2) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa [doubleCoordinate] using h

example : doubleCoordinate ≠ 0 := by
  intro h
  have hker : doubleIdeal ≤ RingHom.ker evaluateNilpotent := by
    rw [doubleIdeal, Ideal.span_le]
    rintro p rfl
    change evaluateNilpotent (Polynomial.X ^ 2) = 0
    simp [evaluateNilpotent, epsilon, pow_two]
  have hzero : evaluateNilpotent Polynomial.X = 0 :=
    hker (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hs := congrArg TrivSqZeroExt.snd hzero
  norm_num [evaluateNilpotent, epsilon] at hs

end MathlibExtTest.AlgebraicGeometry.QuasimapSourceNormalizations
