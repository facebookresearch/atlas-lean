/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EqualCharacteristicCoefficientModels
public import MathlibExt.AlgebraicGeometry.RelativeWittFrobenius
public import MathlibExt.AlgebraicGeometry.IntegralFarguesFontaineModels

/-!
# Actual equal-characteristic relative Fargues--Fontaine rings and annuli

For E = k((t)) the original integral period ring is literally R+[[t]],
with ideal (t,varpi). Frobenius acts coefficientwise by the actual
q-power Frobenius and fixes every original k[[t]] coefficient. Rational
charts use the native completed ring of definition and invert a
denominator divisible by both t and the original varpi coefficient.

The all-rank annular spectrum removes both zero loci; the quotient
map is the actual native Frobenius coequalizer. This retains the
equal-characteristic coefficient field separately from mixed Witt rings.

Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2 and
Section II.1. The actual generic annular/rational source integration is
reused from `IntegralFarguesFontaineModels` with its source attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EqualCharacteristicFFRingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.RingTheory.AdicRationalRingModels
open EqualCharacteristicCoefficientModels AffineAdicSpectra

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
  (C : ResidueData p k)

/-- The actual perfectoid residue base, with its original pseudouniformizer. -/
@[nolint unusedArguments]
structure Base (_C : ResidueData p k) where
  pair : CharPPerfectoidPair p
  [residueAlgebra : Algebra k pair.plus]
  perfect : Function.Bijective (fun a : pair.plus ↦ a ^ p)
  varpi : pair.plus
  unit : IsUnit (varpi : pair.ring)
  nilpotent : IsTopologicallyNilpotent (varpi : pair.ring)

attribute [instance] Base.residueAlgebra

variable (S : Base p k C)

/-- Its original perfect k-algebra, retaining all native scalar maps. -/
def residueTest : RelativeWittLoopTests.PerfectAlgebra p k :=
  ⟨CommAlgCat.of k S.pair.plus, by
    refine ⟨?_, S.perfect⟩
    have h := congrArg (algebraMap k S.pair.plus) (CharP.cast_eq_zero k p)
    simpa only [map_natCast, map_zero] using h⟩

/-- The actual source equal-characteristic integral period ring. -/
abbrev Ring := PowerSeries S.pair.plus

/-- The original coefficient uniformizer t is the actual series variable. -/
def prime : Ring p k C S := PowerSeries.X

/-- A source plus coefficient is its literal constant series. -/
def baseCoefficient (a : S.pair.plus) : Ring p k C S := PowerSeries.C a

/-- Original k[[t]] coefficients map by their actual residue-algebra map. -/
def integralCoefficients : IntegralCoefficients k →+* Ring p k C S :=
  PowerSeries.map (algebraMap k S.pair.plus)

/-- The exact source equal-characteristic period ideal. -/
def periodIdeal : Ideal (Ring p k C S) :=
  Ideal.span {prime p k C S, baseCoefficient p k C S S.varpi}

instance ringTopology : TopologicalSpace (Ring p k C S) := (periodIdeal p k C S).adicTopology

/-- The original residue-degree coefficient Frobenius equivalence. -/
def coefficientFrobenius : S.pair.plus ≃+* S.pair.plus :=
  RingEquiv.ofBijective
    (RelativeWittFrobenius.iteratedFrobenius p k (residueTest p k C S) C.degree)
    (RelativeWittFrobenius.iteratedFrobenius_bijective p k (residueTest p k C S) C.degree)

/-- The coefficient Frobenius is actual q-power on every original plus element. -/
theorem coefficientFrobenius_apply (a : S.pair.plus) :
    coefficientFrobenius p k C S a = a ^ Nat.card k := by
  rw [C.cardinality]
  exact RelativeWittFrobenius.iteratedFrobenius_apply p k (residueTest p k C S) C.degree a

/-- The source Frobenius fixes every original residue coefficient. -/
theorem coefficientFrobenius_scalar (a : k) :
    coefficientFrobenius p k C S (algebraMap k S.pair.plus a) =
      algebraMap k S.pair.plus a := by
  rw [coefficientFrobenius_apply, ← map_pow, Nat.card_eq_fintype_card]
  exact congrArg (algebraMap k S.pair.plus) (FiniteField.pow_card a)

/-- Frobenius is coefficientwise q-power and leaves the actual t variable fixed. -/
def frobenius : Ring p k C S ≃+* Ring p k C S :=
  { __ := PowerSeries.map (coefficientFrobenius p k C S).toRingHom
    invFun := PowerSeries.map (coefficientFrobenius p k C S).symm.toRingHom
    left_inv := by
      intro f
      apply PowerSeries.ext
      intro n
      exact (coefficientFrobenius p k C S).symm_apply_apply (PowerSeries.coeff n f)
    right_inv := by
      intro f
      apply PowerSeries.ext
      intro n
      exact (coefficientFrobenius p k C S).apply_symm_apply (PowerSeries.coeff n f) }

/-- Every original integral E coefficient is retained by the relative Frobenius. -/
theorem frobenius_integralCoefficients (f : IntegralCoefficients k) :
    frobenius p k C S (integralCoefficients p k C S f) = integralCoefficients p k C S f := by
  apply PowerSeries.ext
  intro n
  exact coefficientFrobenius_scalar p k C S (PowerSeries.coeff n f)

/-- The actual source uniformizer is fixed, with no p-for-t substitution. -/
theorem frobenius_prime : frobenius p k C S (prime p k C S) = prime p k C S :=
  by
    change PowerSeries.map (coefficientFrobenius p k C S).toRingHom PowerSeries.X =
      PowerSeries.X
    exact PowerSeries.map_X _

/-- The source varpi coefficient has exactly its actual q-power image. -/
theorem frobenius_baseCoefficient (a : S.pair.plus) :
    frobenius p k C S (baseCoefficient p k C S a) =
      baseCoefficient p k C S (a ^ Nat.card k) := by
  change PowerSeries.map (coefficientFrobenius p k C S).toRingHom (PowerSeries.C a) =
    PowerSeries.C (a ^ Nat.card k)
  rw [PowerSeries.map_C]
  exact congrArg PowerSeries.C (coefficientFrobenius_apply p k C S a)

/-- The original all-rank annulus removes the two actual period zero loci. -/
abbrev Y := {v : Spa (⊤ : Subring (Ring p k C S)) //
  ¬ v.val.relation.vle (prime p k C S) 0 ∧
    ¬ v.val.relation.vle (baseCoefficient p k C S S.varpi) 0}

def ySpace : TopCat := TopCat.of (Y p k C S)

/-- The actual point-Frobenius homeomorphism is fixed on every original valuation. -/
structure FrobeniusPoints where
  homeomorph : Y p k C S ≃ₜ Y p k C S
  normalized : ∀ y, (homeomorph y).val.val =
    AffineAdicSpectra.comap (frobenius p k C S).toRingHom y.val.val

variable (F : FrobeniusPoints p k C S)

def frobeniusMap : ySpace p k C S ⟶ ySpace p k C S :=
  TopCat.ofHom ⟨F.homeomorph, F.homeomorph.continuous_toFun⟩

/-- The actual Frobenius-orbit curve point space. -/
def xSpace : TopCat := coequalizer (frobeniusMap p k C S F) (𝟙 (ySpace p k C S))

/-- The original native orbit map on the displayed equal-characteristic annulus. -/
def quotient : ySpace p k C S ⟶ xSpace p k C S F :=
  coequalizer.π (frobeniusMap p k C S F) (𝟙 _)

/-- The source orbit map identifies precisely the displayed Frobenius arrows. -/
theorem quotient_frobenius : frobeniusMap p k C S F ≫ quotient p k C S F =
    quotient p k C S F :=
  (coequalizer.condition _ _).trans (Category.id_comp _)

/-- Actual rational presentations retain both original period punctures. -/
structure RationalPresentation where
  numerators : Finset (Ring p k C S)
  denominator : Ring p k C S
  annular : IsAnnular (Ring p k C S) (periodIdeal p k C S) numerators denominator
  punctured : ∃ a : Ring p k C S,
    denominator = prime p k C S * baseCoefficient p k C S S.varpi * a
  openSet : Opens (ySpace p k C S)
  domain : ∀ y : Y p k C S, y ∈ openSet ↔
    ¬ y.val.val.relation.vle denominator 0 ∧
      ∀ t ∈ numerators, y.val.val.relation.vle t denominator

instance rationalPreorder : Preorder (RationalPresentation p k C S) where
  le P Q := P.openSet ≤ Q.openSet
  le_refl P := le_refl _
  le_trans _ _ _ h j := h.trans j

/-- The actual source rational-basis open functor. -/
def rationalOpens : RationalPresentation p k C S ⥤ Opens (ySpace p k C S) where
  obj P := P.openSet
  map h := homOfLE (leOfHom h)

/-- The actual completed rational coefficient ring at the specified original chart. -/
def ChartRing (P : RationalPresentation p k C S) : Type :=
  RationalRing (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator

instance chartCommRing (P : RationalPresentation p k C S) :
    CommRing (ChartRing p k C S P) :=
  inferInstanceAs (CommRing
    (RationalRing (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator))

instance chartCompletedAlgebra (P : RationalPresentation p k C S) :
    Algebra (CompletedDefinition (Ring p k C S) (periodIdeal p k C S)
      P.numerators P.denominator) (ChartRing p k C S P) :=
  inferInstanceAs (Algebra
    (CompletedDefinition (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator)
    (RationalRing (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator))

/-- Original integral coefficients use the native completed rational-ring map. -/
def chartCoefficient (P : RationalPresentation p k C S) :
    Ring p k C S →+* ChartRing p k C S P :=
  coefficient (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator

/-- Every rational chart inverts both actual source period elements. -/
theorem chartPunctures_unit (P : RationalPresentation p k C S) :
    IsUnit (chartCoefficient p k C S P (prime p k C S)) ∧
      IsUnit (chartCoefficient p k C S P (baseCoefficient p k C S S.varpi)) := by
  have h : IsUnit (chartCoefficient p k C S P P.denominator) :=
    coefficient_denominator (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator
  obtain ⟨a, ha⟩ := P.punctured
  rw [ha, map_mul, map_mul] at h
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h),
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)⟩

/-- The original valuation integers map through their actual power-series dictionary. -/
def integerCoefficients : Integers k →+* Ring p k C S :=
  (integralCoefficients p k C S).comp (integerEquiv k).symm.toRingHom

/-- The actual E=k((t)) coefficient map extends the original integral series map. -/
def fieldCoefficients (P : RationalPresentation p k C S) :
    CoefficientField k →+* ChartRing p k C S P :=
  IsLocalization.Away.lift (S := CoefficientField k)
    (g := (chartCoefficient p k C S P).comp (integralCoefficients p k C S))
    (PowerSeries.X : PowerSeries k) (by
      change IsUnit (chartCoefficient p k C S P
        (PowerSeries.map (algebraMap k S.pair.plus) PowerSeries.X))
      rw [PowerSeries.map_X]
      exact (chartPunctures_unit p k C S P).1)

/-- Every original k[[t]] coefficient has its source-normalized rational-chart image. -/
theorem fieldCoefficients_integral (P : RationalPresentation p k C S)
    (f : IntegralCoefficients k) :
    fieldCoefficients p k C S P (integralEmbedding k f) =
      chartCoefficient p k C S P (integralCoefficients p k C S f) := by
  exact IsLocalization.Away.lift_eq _ _ _

/-- The chart topology uses the original completed-definition ideal filtration. -/
def chartNeighbourhood (P : RationalPresentation p k C S) (n : ℕ) :
    Set (ChartRing p k C S P) :=
  (algebraMap
      (CompletedDefinition (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator)
      (ChartRing p k C S P)) ''
    (RingHom.ker ((AdicCompletion.evalₐ
      (completionIdeal (Ring p k C S) (periodIdeal p k C S) P.numerators P.denominator)
        n).toRingHom))

/-- All actual annular restriction maps are fixed on the original R+[[t]] coefficients. -/
class RationalRestrictions where
  [topology : ∀ P : RationalPresentation p k C S, TopologicalSpace (ChartRing p k C S P)]
  neighbourhoods : ∀ P,
    (𝓝 (0 : ChartRing p k C S P)).HasBasis (fun _ : ℕ ↦ True)
      (chartNeighbourhood p k C S P)
  restrict : ∀ {P Q : RationalPresentation p k C S}, Q.openSet ≤ P.openSet →
    ChartRing p k C S P →+* ChartRing p k C S Q
  continuous : ∀ {P Q : RationalPresentation p k C S} (h : Q.openSet ≤ P.openSet),
    Continuous (restrict h)
  coefficient : ∀ {P Q : RationalPresentation p k C S} (h : Q.openSet ≤ P.openSet),
    (restrict h).comp (chartCoefficient p k C S P) = chartCoefficient p k C S Q
  unique : ∀ {P Q : RationalPresentation p k C S}
    (f g : ChartRing p k C S P →+* ChartRing p k C S Q),
    Continuous f → Continuous g →
      f.comp (chartCoefficient p k C S P) = g.comp (chartCoefficient p k C S P) → f = g
  basis : ∀ (U : Opens (ySpace p k C S)) (y : Y p k C S), y ∈ U →
    ∃ P : RationalPresentation p k C S, y ∈ P.openSet ∧ P.openSet ≤ U

attribute [instance_reducible] RationalRestrictions.topology
attribute [instance] RationalRestrictions.topology

variable [D : RationalRestrictions p k C S]

/-- Identity restriction is fixed by the original coefficient comparison. -/
theorem restrict_id (P : RationalPresentation p k C S) :
    D.restrict (le_refl P.openSet) = RingHom.id (ChartRing p k C S P) :=
  D.unique _ _ (D.continuous _) continuous_id (by rw [D.coefficient]; rfl)

/-- Composition is fixed by the same original coefficient comparison. -/
theorem restrict_comp {P Q T : RationalPresentation p k C S}
    (h : Q.openSet ≤ P.openSet) (j : T.openSet ≤ Q.openSet) :
    D.restrict (j.trans h) = (D.restrict j).comp (D.restrict h) :=
  D.unique _ _ (D.continuous _) ((D.continuous j).comp (D.continuous h))
    (by rw [D.coefficient, RingHom.comp_assoc, D.coefficient, D.coefficient])

/-- The annular ring diagram consists of the actual completed rational rings. -/
def rationalRings : (RationalPresentation p k C S)ᵒᵖ ⥤ CommRingCat where
  obj P := .of (ChartRing p k C S P.unop)
  map f := CommRingCat.ofHom (D.restrict (leOfHom f.unop))
  map_id P := by
    change CommRingCat.ofHom (D.restrict (le_refl P.unop.openSet)) = 𝟙 _
    rw [restrict_id]
    rfl
  map_comp f g := congrArg CommRingCat.ofHom
    (restrict_comp p k C S (leOfHom f.unop) (leOfHom g.unop))

/-- The source annular sheaf is pinned by its native rational rings and Kan property. -/
structure PeriodSheaf where
  sheaf : TopCat.Sheaf CommRingCat (ySpace p k C S)
  rationalComparison : (rationalOpens p k C S).op ⋙ sheaf.obj ≅ rationalRings p k C S
  [kan : sheaf.obj.IsRightKanExtension rationalComparison.hom]

attribute [instance] PeriodSheaf.kan

end MathlibExt.AlgebraicGeometry.EqualCharacteristicFFRingModels
