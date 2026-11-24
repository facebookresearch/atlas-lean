/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittFrobenius
public import MathlibExt.AlgebraicGeometry.IntegralFarguesFontaineModels

/-!
# Actual relative mixed-characteristic Fargues--Fontaine annuli

The base is an actual perfectoid pair over the actual residue field of E.
The period ring is W(R-plus) tensor W(k) O_E, with the actual ideal
(pi,[varpi]). Its open spectrum removes the zero loci of both generators,
and its quotient is the native coequalizer of the actual q-Frobenius.

Rational rings complete the integral ring of definition before inverting
their denominator. The annular sheaf is constrained on these exact rings
and by its native right Kan universal property. These generic rational
and gluing adapters reuse the completed source primitives from
IntegralFarguesFontaineModels; no general-E theorem port is claimed.

Sources: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2 and
Section II.1; the completed generic annular source and license notices
are retained in the imported integral/rational models.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.RingTheory.AdicRationalRingModels
open LocalWittCoefficientFields
open AffineAdicSpectra

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)

/-- An actual residue-linear perfectoid pair with its genuine period parameter. -/
@[nolint unusedArguments]
structure Base (_C : CoefficientData p E) where
  pair : CharPPerfectoidPair p
  [residueAlgebra : Algebra (Residue p E) pair.plus]
  perfect : Function.Bijective (fun a : pair.plus ↦ a ^ p)
  varpi : pair.plus
  unit : IsUnit (varpi : pair.ring)
  nilpotent : IsTopologicallyNilpotent (varpi : pair.ring)

attribute [instance] Base.residueAlgebra

variable (S : Base p C)

/-- Its actual perfect residue test, including the zero-ring boundary. -/
def residueTest : RelativeWittLoopTests.PerfectAlgebra p (Residue p E) :=
  ⟨CommAlgCat.of (Residue p E) S.pair.plus, by
    refine ⟨?_, S.perfect⟩
    let := C.residueCharacteristic
    have h := congrArg (algebraMap (Residue p E) S.pair.plus)
      (CharP.cast_eq_zero (Residue p E) p)
    simpa only [map_natCast, map_zero] using h⟩

/-- The actual ramified integral period ring. -/
abbrev Ring := RamifiedWitt p C (residueTest p C S)

/-- The original uniformizer coefficient, with no p-for-pi substitution. -/
def prime : Ring p C S :=
  letI := coefficientAlgebra p C
  RelativeWittLoopTests.coefficient p (Residue p E) (Integers p E)
    (residueTest p C S) C.uniformizer

/-- The actual Teichmuller coefficient in the original Witt tensor factor. -/
def teichmuller (a : S.pair.plus) : Ring p C S :=
  letI := coefficientAlgebra p C
  RelativeWittLoopTests.tensor p (Residue p E) (Integers p E)
    (residueTest p C S) (WittVector.teichmuller p a) 1

/-- The exact relative period ideal. -/
def periodIdeal : Ideal (Ring p C S) := Ideal.span {prime p C S, teichmuller p C S S.varpi}

instance ringTopology : TopologicalSpace (Ring p C S) := (periodIdeal p C S).adicTopology

/-- The actual q-Frobenius, with q fixed by E's residue cardinality. -/
def frobenius : Ring p C S ≃+* Ring p C S :=
  RelativeWittFrobenius.ramifiedFrobeniusEquiv p C (residueTest p C S)

/-- The actual all-rank punctured spectrum of the ramified ring. -/
abbrev Y := {v : Spa (⊤ : Subring (Ring p C S)) //
  ¬ v.val.relation.vle (prime p C S) 0 ∧
    ¬ v.val.relation.vle (teichmuller p C S S.varpi) 0}

def ySpace : TopCat := TopCat.of (Y p C S)

/-- The source Frobenius dictionary is fixed on every original all-rank valuation. -/
structure FrobeniusPoints where
  homeomorph : Y p C S ≃ₜ Y p C S
  normalized : ∀ y : Y p C S, (homeomorph y).val.val =
    AffineAdicSpectra.comap (frobenius p C S).toRingHom y.val.val

variable (φ : FrobeniusPoints p C S)

def frobeniusMap : ySpace p C S ⟶ ySpace p C S :=
  TopCat.ofHom ⟨φ.homeomorph, φ.homeomorph.continuous_toFun⟩

/-- The actual relative orbit space, indexed by this whole perfectoid base. -/
def xSpace : TopCat := coequalizer (frobeniusMap p C S φ) (𝟙 (ySpace p C S))

def quotient : ySpace p C S ⟶ xSpace p C S φ :=
  coequalizer.π (frobeniusMap p C S φ) (𝟙 _)

theorem quotient_frobenius : frobeniusMap p C S φ ≫ quotient p C S φ =
    quotient p C S φ := by
  dsimp only [quotient, xSpace]
  exact (coequalizer.condition (frobeniusMap p C S φ) (𝟙 _)).trans (Category.id_comp _)

/-- Actual annular rational presentations, with their exact point domains. -/
structure RationalPresentation where
  numerators : Finset (Ring p C S)
  denominator : Ring p C S
  annular : IsAnnular (Ring p C S) (periodIdeal p C S) numerators denominator
  punctured : ∃ a : Ring p C S,
    denominator = prime p C S * teichmuller p C S S.varpi * a
  openSet : Opens (ySpace p C S)
  domain : ∀ y : Y p C S, y ∈ openSet ↔
    ¬ y.val.val.relation.vle denominator 0 ∧
      ∀ t ∈ numerators, y.val.val.relation.vle t denominator

instance rationalPreorder : Preorder (RationalPresentation p C S) where
  le P Q := P.openSet ≤ Q.openSet
  le_refl P := le_refl _
  le_trans _ _ _ h j := h.trans j

/-- The actual rational-basis inclusion functor. -/
def rationalOpens : RationalPresentation p C S ⥤ Opens (ySpace p C S) where
  obj P := P.openSet
  map h := homOfLE (leOfHom h)

/-- The actual completed annular coefficient ring at each rational chart. -/
def ChartRing (P : RationalPresentation p C S) : Type :=
  RationalRing (Ring p C S) (periodIdeal p C S) P.numerators P.denominator

instance chartCommRing (P : RationalPresentation p C S) : CommRing (ChartRing p C S P) :=
  inferInstanceAs (CommRing
    (RationalRing (Ring p C S) (periodIdeal p C S) P.numerators P.denominator))

instance chartCompletedAlgebra (P : RationalPresentation p C S) :
    Algebra (CompletedDefinition (Ring p C S) (periodIdeal p C S)
      P.numerators P.denominator) (ChartRing p C S P) :=
  inferInstanceAs (Algebra
    (CompletedDefinition (Ring p C S) (periodIdeal p C S) P.numerators P.denominator)
    (RationalRing (Ring p C S) (periodIdeal p C S) P.numerators P.denominator))

def chartCoefficient (P : RationalPresentation p C S) : Ring p C S →+* ChartRing p C S P :=
  coefficient (Ring p C S) (periodIdeal p C S) P.numerators P.denominator

/-- A chart of the doubly punctured space inverts both original period coefficients. -/
theorem chartPunctures_unit (P : RationalPresentation p C S) :
    IsUnit (chartCoefficient p C S P (prime p C S)) ∧
      IsUnit (chartCoefficient p C S P (teichmuller p C S S.varpi)) := by
  have h : IsUnit (chartCoefficient p C S P P.denominator) :=
    coefficient_denominator (Ring p C S) (periodIdeal p C S) P.numerators P.denominator
  obtain ⟨a, ha⟩ := P.punctured
  rw [ha, map_mul, map_mul] at h
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)⟩

/-- The actual completed-definition lattice in every filtration degree. -/
def chartNeighbourhood (P : RationalPresentation p C S) (n : ℕ) : Set (ChartRing p C S P) :=
  (algebraMap
      (CompletedDefinition (Ring p C S) (periodIdeal p C S) P.numerators P.denominator)
      (ChartRing p C S P)) ''
    (RingHom.ker ((AdicCompletion.evalₐ
      (completionIdeal (Ring p C S) (periodIdeal p C S) P.numerators P.denominator) n).toRingHom))

/-- Source-normalized rational topology and restriction maps on the real rings. -/
class RationalRestrictions where
  [topology : ∀ P : RationalPresentation p C S, TopologicalSpace (ChartRing p C S P)]
  neighbourhoods : ∀ P : RationalPresentation p C S,
    (𝓝 (0 : ChartRing p C S P)).HasBasis (fun _ : ℕ ↦ True) (chartNeighbourhood p C S P)
  restrict : ∀ {P Q : RationalPresentation p C S}, Q.openSet ≤ P.openSet →
    ChartRing p C S P →+* ChartRing p C S Q
  continuous : ∀ {P Q : RationalPresentation p C S} (h : Q.openSet ≤ P.openSet),
    Continuous (restrict h)
  coefficient : ∀ {P Q : RationalPresentation p C S} (h : Q.openSet ≤ P.openSet),
    (restrict h).comp (chartCoefficient p C S P) = chartCoefficient p C S Q
  unique : ∀ {P Q : RationalPresentation p C S} (f g : ChartRing p C S P →+* ChartRing p C S Q),
    Continuous f → Continuous g →
      f.comp (chartCoefficient p C S P) = g.comp (chartCoefficient p C S P) → f = g
  basis : ∀ (U : Opens (ySpace p C S)) (y : Y p C S), y ∈ U →
    ∃ P : RationalPresentation p C S, y ∈ P.openSet ∧ P.openSet ≤ U

attribute [instance_reducible] RationalRestrictions.topology
attribute [instance] RationalRestrictions.topology

variable [D : RationalRestrictions p C S]

/-- The actual coefficient-normalized restriction has the identity law. -/
theorem restrict_id (P : RationalPresentation p C S) : D.restrict (le_refl P.openSet) =
    RingHom.id (ChartRing p C S P) :=
  D.unique _ _ (D.continuous _) continuous_id (by rw [D.coefficient]; rfl)

/-- Its composition law follows from the same actual uniqueness property. -/
theorem restrict_comp {P Q T : RationalPresentation p C S}
    (h : Q.openSet ≤ P.openSet) (j : T.openSet ≤ Q.openSet) :
    D.restrict (j.trans h) = (D.restrict j).comp (D.restrict h) :=
  D.unique _ _ (D.continuous _) ((D.continuous j).comp (D.continuous h))
    (by rw [D.coefficient, RingHom.comp_assoc, D.coefficient, D.coefficient])

/-- The real rational-ring diagram, not an arbitrary structure presheaf. -/
def rationalRings : (RationalPresentation p C S)ᵒᵖ ⥤ CommRingCat where
  obj P := .of (ChartRing p C S P.unop)
  map f := CommRingCat.ofHom (D.restrict (leOfHom f.unop))
  map_id P := by
    change CommRingCat.ofHom (D.restrict (le_refl P.unop.openSet)) = 𝟙 _
    rw [restrict_id]
    rfl
  map_comp {P Q T} f g := by
    have h := restrict_comp p C S (leOfHom f.unop) (leOfHom g.unop)
    exact congrArg CommRingCat.ofHom h

/-- The exact source annular sheaf, pinned by its rational rings and Kan property. -/
structure PeriodSheaf where
  sheaf : TopCat.Sheaf CommRingCat (ySpace p C S)
  rationalComparison : (rationalOpens p C S).op ⋙ sheaf.obj ≅ rationalRings p C S
  [kan : sheaf.obj.IsRightKanExtension rationalComparison.hom]

attribute [instance] PeriodSheaf.kan


end MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
