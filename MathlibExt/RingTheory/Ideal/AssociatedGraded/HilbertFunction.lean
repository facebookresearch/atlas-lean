/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import MathlibExt.RingTheory.Ideal.AdicOrder
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Associated-graded piece ranks and nonzero initial forms

For an ideal I in a commutative Noetherian ring R, each piece I^n / I^(n+1) of the associated
graded is finitely generated over R/I. The piece finrank is defined for any ideal. At a
maximal ideal it is the vector-space finrank over the residue field, and the Noetherian
hypothesis ensures finite-dimensionality.

If R is also local and I is proper, every nonzero x : R has some order n with x ∈ I^n and
nonzero class in I^n / I^(n+1). The element x need not be assumed to lie in I, since n may be
zero.

See Atiyah–Macdonald, *Introduction to Commutative Algebra*, Chapters 7 and 11.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

/-- For a commutative Noetherian ring R, any ideal I and n : ℕ, the piece AssociatedGradedPiece I
n = I^n / I^(n+1) is a finitely generated module over R ⧸ I. -/
theorem associatedGradedPiece_finite [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    Module.Finite (R ⧸ I) (AssociatedGradedPiece I n) := by
  infer_instance

/-- For an ideal I in a commutative ring R and n : ℕ, define associatedGradedPieceFinrank I n to
be Module.finrank (R ⧸ I) (I^n / I^(n+1)). This natural-number rank is defined without
maximality or finite-generation hypotheses; at a maximal ideal it is the residue-field
finrank. -/
def associatedGradedPieceFinrank (I : Ideal R) (n : ℕ) : ℕ :=
  Module.finrank (R ⧸ I) (AssociatedGradedPiece I n)

/-- For a maximal ideal I in a commutative ring R and n : ℕ, define
associatedGradedHilbertFunction I n as the finrank of I^n / I^(n+1) over the field R ⧸ I. If R
is Noetherian, this piece is finite-dimensional, so the value is its finite vector-space
dimension. -/
def associatedGradedHilbertFunction (I : Ideal R) [I.IsMaximal] (n : ℕ) : ℕ :=
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  Module.finrank (R ⧸ I) (AssociatedGradedPiece I n)

/-- Let R be a commutative Noetherian local ring, let I be a proper ideal, and let x : R satisfy x
≠ 0. Then there exist n : ℕ and hxn : x ∈ I^n such that the initial form of x in I^n / I^(n+1)
is nonzero. Equivalently, x has membership in I^n but not in I^(n+1) for some n, which may be
zero. -/
theorem exists_initialForm_ne_zero_of_ne_zero
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤) {x : R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (hxn : x ∈ I ^ n),
      initialForm I n ⟨x, hxn⟩ ≠ 0 := by
  obtain ⟨n, hxn, hnext⟩ :=
    Ideal.exists_mem_pow_notMem_pow_succ_of_ne_zero I hI hx
  refine ⟨n, hxn, ?_⟩
  rw [ne_eq, initialForm_eq_zero_iff]
  exact hnext

end Ideal
