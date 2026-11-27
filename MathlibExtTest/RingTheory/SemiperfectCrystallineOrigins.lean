/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings

/-!
The full original Witt kernel, literal p-completion and literal p-localization
are retained. Finite evaluation is checked against the original hull and
Witt coefficients on every p-nilpotent target, including zero algebras.
The universal-envelope constructor remains separate Wanted work.
-/

open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings

noncomputable section

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R)

example : WittRing p R = WittVector p (Perfection R p) := rfl

example : reductionIdeal p R = RingHom.ker (reduction p R) := rfl

example : Acris p R A =
    AdicCompletion (Ideal.span {(p : A.algebra.ring)}) A.algebra.ring := rfl

example : BcrisPlus p R A = Localization.Away (p : Acris p R A) := rfl

example (B : Type) [CommRing B] (f : A.algebra.ring →+* B)
    (n : ℕ) (hn : (p : B) ^ n = 0) (x : WittRing p R) :
    finiteEvaluation f n hn (wittToAcris p R A x) = f (A.algebra.scalars x) :=
  finiteEvaluation_witt f n hn x

example (B : Type) [CommRing B] [Subsingleton B] (f : A.algebra.ring →+* B)
    (x : A.algebra.ring) :
    finiteEvaluation f 0 (Subsingleton.elim _ _)
      (hullToAcris p R A x) = f x := finiteEvaluation_hull f 0 _ x

example (hR : IsSemiperfect p R) (F : HullFrobenius (A := A))
    (n : ℕ) (x : Acris p R A) :
    finiteProjection p R A n
        ((WantedExt.RingTheory.SemiperfectCrystallinePeriodRings.completedWittPDFrobenius
          (p := p) (R := R) (hR := hR) (A := A) (F := F)).hom x) =
      MathlibExt.RingTheory.AdicCompletionMaps.quotientMap
        (completionIdeal p R A) (completionIdeal p R A) F.hom F.completion_preserved n
        (finiteProjection p R A n x) :=
  RingHom.congr_fun
    ((WantedExt.RingTheory.SemiperfectCrystallinePeriodRings.completedWittPDFrobenius
      p R hR A F).projection n) x

#print axioms MathlibExt.RingTheory.SemiperfectWittPDEnvelopes.reduction
#print axioms MathlibExt.RingTheory.SemiperfectWittPDEnvelopes.padicScalars
#print axioms MathlibExt.RingTheory.SemiperfectWittPDEnvelopes.UniversalEnvelope.to_unique
#print axioms MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings.finite_kernel
#print axioms MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings.finiteEvaluation_hull
#print axioms MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings.finiteEvaluation_witt
