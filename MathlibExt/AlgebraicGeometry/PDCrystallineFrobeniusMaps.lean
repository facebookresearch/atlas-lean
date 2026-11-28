/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallineModuleLimits

/-!
# Original PD Frobenius reindexing and finite crystalline arrows

Frobenius reindexing keeps each original thickening ring and PD ideal,
precomposes its hull coefficients by the source Witt/PD Frobenius, and
composes its reduction point with the actual scheme Frobenius. Every
finite arrow is the native quotient of the completed Frobenius, with
all original p-power projection and restriction squares retained.

Compatibility of those fixed maps with divided powers is a proof output.
No inverse Frobenius or changed ideal is used.

Source: BBM82; Scholze--Weinstein1211.6357v2, Sections3.1 and4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDCrystallineFrobeniusMaps

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.RingTheory.SemiperfectCrystallineResidues
open SemiperfectCrystallinePDStages

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (F₀ : HullFrobenius (A := A)) (φ : CompletedFrobenius F₀)

/-- The original geometric Frobenius of Spec R, reused from the group source maps. -/
abbrev baseFrobenius : Spec (.of R) ⟶ Spec (.of R) :=
  PDivisibleBaseChangeModels.frobeniusBase p (PDivisibleCartierGroupMaps.primeFieldBase p R)

/-- The actual residue map of the original hull Frobenius. -/
def hullReductionFrobenius : (A.algebra.ring ⧸ A.algebra.ideal) →+*
    (A.algebra.ring ⧸ A.algebra.ideal) :=
  Ideal.quotientMap A.algebra.ideal F₀.hom
    (Ideal.map_le_iff_le_comap.mp F₀.dividedPowers.ideal_comp)

/-- Completion Frobenius preserves every original hull coefficient. -/
theorem completedFrobenius_hull (x : A.algebra.ring) :
    φ.hom (hullToAcris p R A x) = hullToAcris p R A (F₀.hom x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  have h := RingHom.congr_fun (φ.projection n) (hullToAcris p R A x)
  change (AdicCompletion.evalₐ (completionIdeal p R A) n)
    (φ.hom (hullToAcris p R A x)) =
      MathlibExt.RingTheory.AdicCompletionMaps.quotientMap (completionIdeal p R A)
        (completionIdeal p R A) F₀.hom F₀.completion_preserved n
        ((AdicCompletion.evalₐ (completionIdeal p R A) n)
          (AdicCompletion.of (completionIdeal p R A) A.algebra.ring x)) at h
  rw [AdicCompletion.evalₐ_of, MathlibExt.RingTheory.AdicCompletionMaps.quotientMap_mk] at h
  change (AdicCompletion.evalₐ (completionIdeal p R A) n)
    (φ.hom (hullToAcris p R A x)) =
      (AdicCompletion.evalₐ (completionIdeal p R A) n)
        (AdicCompletion.of (completionIdeal p R A) A.algebra.ring (F₀.hom x))
  rw [AdicCompletion.evalₐ_of]
  exact h

/-- The literal p-adic ideal is preserved; no invertibility of Frobenius is needed. -/
theorem completedIdeal_preserved : (completedIdeal p R A).map φ.hom ≤ completedIdeal p R A := by
  simp only [completedIdeal, Ideal.map_span, Set.image_singleton, map_natCast, le_refl]

/-- The actual quotient Frobenius on A_cris/p^(n+1). -/
def finiteFrobenius (n : ℕ) : FiniteRing p R A n →+* FiniteRing p R A n :=
  MathlibExt.RingTheory.AdicCompletionMaps.quotientMap (completedIdeal p R A)
    (completedIdeal p R A) φ.hom (completedIdeal_preserved p R A F₀ φ) (n + 1)

/-- All original completed coefficients are preserved at every finite stage. -/
theorem finiteFrobenius_quotient (n : ℕ) (x : Acris p R A) :
    finiteFrobenius p R A F₀ φ n (finiteQuotient p R A n x) =
      finiteQuotient p R A n (φ.hom x) := rfl

/-- Every original hull coefficient has its original Frobenius image. -/
theorem finiteFrobenius_hull (n : ℕ) (x : A.algebra.ring) :
    finiteFrobenius p R A F₀ φ n (finiteHullMap p R A n x) =
      finiteHullMap p R A n (F₀.hom x) := by
  change finiteQuotient p R A n (φ.hom (hullToAcris p R A x)) = _
  rw [completedFrobenius_hull]
  rfl

/-- All original p-power transition maps commute with that fixed finite Frobenius. -/
theorem finiteFrobenius_transition {n m : ℕ} (h : n ≤ m) :
    (finiteTransition p R A h).comp (finiteFrobenius p R A F₀ φ m) =
      (finiteFrobenius p R A F₀ φ n).comp (finiteTransition p R A h) := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Source compatibility proofs concern only these fixed maps and the original PD kernels. -/
structure Compatibility : Prop where
  base : baseFrobenius p R ≫ (baseScheme p R A E).hom =
    (baseScheme p R A E).hom ≫ Spec.map (CommRingCat.ofHom (hullReductionFrobenius p R A F₀))
  finitePD : ∀ n : ℕ, DividedPowers.IsDPMorphism (P.dividedPowers n) (P.dividedPowers n)
    (finiteFrobenius p R A F₀ φ n)
  finitePoint : ∀ n : ℕ,
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (finiteIdeal p R A E n)
      (finiteFrobenius p R A F₀ φ n)
      (Ideal.map_le_iff_le_comap.mp (finitePD n).ideal_comp))) ≫ (finiteTest p R A E P n).point =
        (finiteTest p R A E P n).point ≫ baseFrobenius p R

variable (C : Compatibility p R A E P F₀ φ)

/-- Reindex the actual ring by original hull Frobenius coefficients. -/
def reindexedAlgebra (B : FullPDCrystallineTests.Obj p (hullPDBase p R A)
    (baseScheme p R A E)) : CommAlgCat.{0} A.algebra.ring := by
  letI : Algebra A.algebra.ring B.ring :=
    ((algebraMap A.algebra.ring B.ring).comp F₀.hom).toAlgebra
  exact CommAlgCat.of A.algebra.ring B.ring

/-- The full-PD Frobenius reindexing retains the original ring, ideal and divided powers. -/
def reindexedTest (B : FullPDCrystallineTests.Obj p (hullPDBase p R A)
    (baseScheme p R A E)) : FullPDCrystallineTests.Obj p (hullPDBase p R A)
    (baseScheme p R A E) where
  ring := reindexedAlgebra p R A E F₀ B
  ideal := B.ideal
  dividedPowers := B.dividedPowers
  baseCompatible := B.baseCompatible.comp _ F₀.dividedPowers
  pNilpotent := B.pNilpotent
  point := B.point ≫ baseFrobenius p R
  pointBase := by
    change (B.point ≫ baseFrobenius p R) ≫ (baseScheme p R A E).hom = _
    rw [Category.assoc, C.base, ← Category.assoc, B.pointBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- Every original PD arrow uses the same underlying algebra map after Frobenius reindexing. -/
def reindexedArrow {B D : FullPDCrystallineTests.Obj p (hullPDBase p R A)
    (baseScheme p R A E)} (f : B ⟶ D) : reindexedTest p R A E P F₀ φ C B ⟶
    reindexedTest p R A E P F₀ φ C D where
  algebra :=
    { __ := f.algebra.toRingHom
      commutes' x := f.algebra.commutes (F₀.hom x) }
  dividedPowers := f.dividedPowers
  pointCompatible := by
    change Spec.map (CommRingCat.ofHom
      (FullPDCrystallineTests.reductionMap f.algebra f.dividedPowers.ideal_comp)) ≫
        (D.point ≫ baseFrobenius p R) = B.point ≫ baseFrobenius p R
    rw [← Category.assoc, f.pointCompatible]

/-- This is the actual full-basis Frobenius reindexing functor. -/
def reindex : FullPDCrystallineTests.Obj p (hullPDBase p R A) (baseScheme p R A E) ⥤
    FullPDCrystallineTests.Obj p (hullPDBase p R A) (baseScheme p R A E) where
  obj := reindexedTest p R A E P F₀ φ C
  map := reindexedArrow p R A E P F₀ φ C
  map_id B := by
    apply FullPDCrystallineTests.Hom.ext
    apply AlgHom.ext
    intro x
    rfl
  map_comp f g := by
    apply FullPDCrystallineTests.Hom.ext
    apply AlgHom.ext
    intro x
    rfl

/-- Original coefficient rings reindex by the identity, not by a chosen ring map. -/
def coefficientReindex :
    FullPDCrystallineSheaves.structureRingPresheaf p (hullPDBase p R A) (baseScheme p R A E) ⋙
      forget₂ CommRingCat.{1} RingCat.{1} ⟶
    (reindex p R A E P F₀ φ C).op ⋙
      (FullPDCrystallineSheaves.structureRingPresheaf p (hullPDBase p R A) (baseScheme p R A E) ⋙
        forget₂ CommRingCat.{1} RingCat.{1}) where
  app B := RingCat.ofHom (RingHom.id (ULift.{1} B.unop.ring))
  naturality {B D} f := by ext x; rfl

/-- The native PD arrow inducing each finite cartesian Frobenius base change. -/
def finiteArrow (n : ℕ) : reindexedTest p R A E P F₀ φ C (finiteTest p R A E P n) ⟶
    finiteTest p R A E P n where
  algebra :=
    { __ := finiteFrobenius p R A F₀ φ n
      commutes' x := finiteFrobenius_hull p R A F₀ φ n x }
  dividedPowers := C.finitePD n
  pointCompatible := C.finitePoint n

/-- The native cartesian arrows commute with every original finite p-power restriction. -/
theorem finiteArrow_naturality {n m : ℕ} (h : n ≤ m) :
    (reindex p R A E P F₀ φ C).map (SemiperfectCrystallinePDStages.finiteArrow p R A E P h) ≫
      finiteArrow p R A E P F₀ φ C m =
    finiteArrow p R A E P F₀ φ C n ≫ SemiperfectCrystallinePDStages.finiteArrow p R A E P h := by
  apply FullPDCrystallineTests.Hom.ext
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end MathlibExt.AlgebraicGeometry.PDCrystallineFrobeniusMaps
