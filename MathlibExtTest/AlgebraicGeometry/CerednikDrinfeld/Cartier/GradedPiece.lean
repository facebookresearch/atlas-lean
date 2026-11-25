/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece

@[expose] public noncomputable section

namespace CartierGradedPieceTest

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders for membership in a graded piece. -/
theorem exactSource {B : Type u} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (n : ℕ) (f : CartierModule p X.F) :
    f ∈ X.gradedPiece j n ↔ ∀ c : GaloisField p 2,
      endAct (X.actEnd (WittVector.teichmuller p c)) f =
        homothety (j (WittVector.teichmuller p c) ^ p ^ n) f :=
  X.mem_gradedPiece_iff j n f

/-- Consumer with the original binders: the grading has period two. -/
theorem exactSourcePeriodic {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (n k : ℕ) : X.gradedPiece j (n + 2 * k) = X.gradedPiece j n :=
  X.gradedPiece_add_two_mul j n k

/-- Non-vacuity: the graded pieces of the standard special formal `O_D`-module over a ring of
characteristic `p` satisfy the periodicity. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) :
    (SpecialFormalODModule.standard j).gradedPiece j 3 =
      (SpecialFormalODModule.standard j).gradedPiece j 1 :=
  gradedPiece_add_two _ j 1

end CartierGradedPieceTest
