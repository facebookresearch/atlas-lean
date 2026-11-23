/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
public import MathlibExt.RingTheory.AdicCompletionMaps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.WittVector.Frobenius

/-!
# Literal A_cris and B_cris⁺ of a semiperfect ring

A_cris is the native p-adic completion of the universal PD hull of
W(R^flat) to R; B_cris⁺ is exactly A_cris[1/p] (Scholze–Weinstein, the
paragraph after Proposition 4.1.3). This is not Fontaine's B_cris, which
also inverts a period. A finite PD test obtains
its coefficient map through the displayed p-power quotient projection.
Thus evaluation retains the original hull map and every nilpotent test.
No independent period-ring carrier or evaluation homomorphism is supplied.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Proposition 4.1.3 and
the paragraph preceding Theorem 4.1.4, p. 30.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings

open SemiperfectWittPDEnvelopes

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R)

/-- The actual p-adic ideal of the original universal PD hull. -/
def completionIdeal : Ideal A.algebra.ring := Ideal.span {(p : A.algebra.ring)}

/-- Fontaine's ring is this exact completion, without a p-torsionfree assumption. -/
abbrev Acris := AdicCompletion (completionIdeal p R A) A.algebra.ring

/-- The rational ring `B_cris⁺ = A_cris[1/p]`: exactly the localization of A_cris at p. -/
abbrev BcrisPlus := Localization.Away (p : Acris p R A)

/-- The original universal-hull coefficient map into its actual completion. -/
def hullToAcris : A.algebra.ring →+* Acris p R A :=
  algebraMap A.algebra.ring (Acris p R A)

/-- The original Witt coefficients in A_cris. -/
def wittToAcris : WittRing p R →+* Acris p R A :=
  (hullToAcris p R A).comp A.algebra.scalars

/-- The actual p-power quotient projection, retaining the full hull coefficients. -/
def finiteProjection (n : ℕ) :
    Acris p R A →+* (A.algebra.ring ⧸ completionIdeal p R A ^ n) :=
  (AdicCompletion.evalₐ (completionIdeal p R A) n).toRingHom

variable {p R A}

/-- A p-nilpotent target kills the corresponding original p-adic ideal power. -/
theorem finite_kernel {B : Type} [CommRing B] (f : A.algebra.ring →+* B)
    (n : ℕ) (hn : (p : B) ^ n = 0) :
    completionIdeal p R A ^ n ≤ RingHom.ker f := by
  rw [completionIdeal, Ideal.span_singleton_pow, Ideal.span_le]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change f ((p : A.algebra.ring) ^ n) = 0
  simpa only [map_pow, map_natCast] using hn

/-- Evaluation on an actual nilpotent coefficient ring uses its exact finite projection. -/
def finiteEvaluation {B : Type} [CommRing B] (f : A.algebra.ring →+* B)
    (n : ℕ) (hn : (p : B) ^ n = 0) : Acris p R A →+* B :=
  (Ideal.Quotient.lift _ f (finite_kernel f n hn)).comp (finiteProjection p R A n)

/-- This evaluation extends precisely the original hull map. -/
theorem finiteEvaluation_hull {B : Type} [CommRing B]
    (f : A.algebra.ring →+* B) (n : ℕ) (hn : (p : B) ^ n = 0)
    (x : A.algebra.ring) :
    finiteEvaluation f n hn (hullToAcris p R A x) = f x := by
  change Ideal.Quotient.lift (completionIdeal p R A ^ n) f (finite_kernel f n hn)
    ((AdicCompletion.evalₐ (completionIdeal p R A) n)
      (AdicCompletion.of (completionIdeal p R A) A.algebra.ring x)) = f x
  rw [AdicCompletion.evalₐ_of]
  rfl

/-- All original Witt coefficients are preserved at every admissible finite stage. -/
theorem finiteEvaluation_witt {B : Type} [CommRing B]
    (f : A.algebra.ring →+* B) (n : ℕ) (hn : (p : B) ^ n = 0)
    (x : WittRing p R) :
    finiteEvaluation f n hn (wittToAcris p R A x) = f (A.algebra.scalars x) :=
  finiteEvaluation_hull f n hn _

/-- The universal-hull Frobenius is fixed by the original Witt Frobenius. -/
structure HullFrobenius where
  hom : A.algebra.ring →+* A.algebra.ring
  dividedPowers : DividedPowers.IsDPMorphism A.algebra.dividedPowers
    A.algebra.dividedPowers hom
  coefficients : hom.comp A.algebra.scalars =
    A.algebra.scalars.comp WittVector.frobenius

/-- Every hull Frobenius preserves the actual p-adic ideal. -/
theorem HullFrobenius.completion_preserved (F : HullFrobenius (A := A)) :
    (completionIdeal p R A).map F.hom ≤ completionIdeal p R A := by
  simp only [completionIdeal, Ideal.map_span, Set.image_singleton, map_natCast, le_refl]

/-- Completion Frobenius retains every original p-power projection. -/
abbrev CompletedFrobenius (F : HullFrobenius (A := A)) :=
  AdicCompletionMaps.Map (completionIdeal p R A) (completionIdeal p R A)
    F.hom F.completion_preserved

end MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
