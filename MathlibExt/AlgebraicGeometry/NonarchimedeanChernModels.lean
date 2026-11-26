/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneSymbolModels
public import MathlibExt.AlgebraicGeometry.OpenDeligneSymbolSources
public import MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels
public import MathlibExt.AlgebraicGeometry.ModelLineMetrics

/-!
# Actual valuation models and their model intersections

The special fibre is the native quotient by the norm-less-than-one ideal
and the native scheme pullback. All reduced components, their original
local composition lengths and their coherent subset-Euler degrees occur.
Divisorial points retain the original scalar map, the valuative centre,
the actual component local ring and a maximal-ideal uniformizer; they
require an explicit discrete valuation.

For general complete nonarchimedean fields, the intersection of a model
function with model lines is the logarithmic norm of an actual model
Deligne determinant generator.

The local Chern measures (compact-test limits of these model intersections)
are not constructed here: their convergence needs nef approximations, and
their global counterparts need a model-boundary class finer than the
placewise one. They are left to a separate development.

Source: Yuan--Zhang, arXiv:2105.13587v9, Appendix A.6.2, pp245--246, and
Section 3.6.6. Model norm and bounded determinant primitives retain their
original source and license notices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanChernModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open _root_.AlgebraicGeometry
open ValuedLineFibres ModelLineMetrics CoherentCurveLinearSeries
open DeligneSymbolModels GlobalBoundedDeterminantModels RelativeDeterminantPairings
open SchemeComponentIntersectionModels ModelIntersectionDegrees
open GenericSectionMaps
open OpenDeligneSymbolSources CanonicalKoszulDeterminants

variable (K : Type) [NormedField K]
  (X : Over (Spec (.of K)))
  (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)

/-- An actual discrete value group, with a uniformizer. -/
structure DiscreteValuation where
  uniformizer : K
  positive : 0 < ‖uniformizer‖
  small : ‖uniformizer‖ < 1
  discrete : ∀ a : K, a ≠ 0 → ∃ n : ℤ, ‖a‖ = ‖uniformizer‖ ^ n

/-- The valuation residue field is the actual norm-less-than-one quotient. -/
structure ValuationResidue where
  ideal : Ideal (integerRing K hK)
  [maximal : ideal.IsMaximal]
  normalized : ∀ a : integerRing K hK, a ∈ ideal ↔ ‖a.val‖ < 1

attribute [instance] ValuationResidue.maximal

def ValuationResidue.field (V : ValuationResidue K hK) := integerRing K hK ⧸ V.ideal

instance valuationResidueField (V : ValuationResidue K hK) : Field V.field :=
  Ideal.Quotient.field V.ideal

variable (d : ℕ) (L : Fin d → X.left.Modules)

/-- A common genuine model of the original rational powers, including all denominators. -/
structure ModelTuple where
  scheme : Scheme.{0}
  structureMap : scheme ⟶ Spec (.of (integerRing K hK))
  [proper : IsProper structureMap]
  [flat : Flat structureMap]
  [presentation : LocallyOfFinitePresentation structureMap]
  genericMap : X.left ⟶ scheme
  genericSquare : IsPullback genericMap X.hom structureMap
    (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))
  denominator : Fin d → ℕ+
  line : Fin d → scheme.Modules
  isLine : ∀ i, IsLineBundle (line i)
  genericLine : ∀ i, (Scheme.Modules.pullback genericMap).obj (line i) ≅
    CurvePositivity.power (L i) (denominator i)

attribute [instance] ModelTuple.proper ModelTuple.flat ModelTuple.presentation

variable {K X hK d L} (M : ModelTuple K X hK d L)

/-- Each original power is the same native integral model, rather than a new model carrier. -/
def ModelTuple.model (i : Fin d) :
    ModelLineMetrics.Model K X hK (CurvePositivity.power (L i) (M.denominator i)) :=
  ⟨M.scheme, M.structureMap, M.genericMap, M.genericSquare, M.line i,
    M.isLine i, M.genericLine i⟩

def specialFibre (V : ValuationResidue K hK) : Over (Spec (.of V.field)) :=
  Over.mk (pullback.snd M.structureMap
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal))))

def specialProjection (V : ValuationResidue K hK) : (specialFibre M V).left ⟶ M.scheme :=
  pullback.fst M.structureMap (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk V.ideal)))

def specialLine (V : ValuationResidue K hK) (i : Fin d) : (specialFibre M V).left.Modules :=
  (Scheme.Modules.pullback (specialProjection M V)).obj (M.line i)

/-- Every analytic point's centre has the fixed original base and generic maps. -/
structure ModelCentre (p : NonArchPoint K X) where
  map : Spec (.of (residueIntegers K X p)) ⟶ M.scheme
  base : map ≫ M.structureMap = Spec.map (CommRingCat.ofHom (integralScalar K X hK p))
  generic : Spec.map (CommRingCat.ofHom (residueIntegers K X p).subtype) ≫ map =
    Spec.map (CommRingCat.ofHom (completionUnit K X p.val)) ≫
      X.left.fromSpecResidueField p.val.schemePoint ≫ M.genericMap

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]

/-- The actual whole special-fibre component intersection dictionary. -/
abbrev SpecialComponents (V : ValuationResidue K hK) :=
  ComponentIntersectionSources (specialFibre M V) d (specialLine M V)

set_option maxHeartbeats 800000 in
/-- A divisorial point is fixed by the actual model component's DVR and centre. -/
structure DivisorialPoint (V : ValuationResidue K hK)
    (S : SpecialComponents M V) (v : DiscreteValuation K)
    (C : Component (specialFibre M V).left) where
  point : NonArchPoint K X
  generic : _root_.closure ({point.val.schemePoint} : Set X.left) = Set.univ
  centre : ModelCentre M point
  reductionPoint : Spec (.of (residueIntegers K X point))
  reductionIdeal : ∀ a : residueIntegers K X point,
    a ∈ reductionPoint.asIdeal ↔ ‖a.val‖ < 1
  reduction : centre.map reductionPoint =
    specialProjection M V ((S.components.frame C).inclusion (S.components.frame C).genericPoint)
  fraction : M.scheme.presheaf.stalk (centre.map reductionPoint) →+*
    X.left.residueField point.val.schemePoint
  originalSections : ∀ (U : M.scheme.Opens) (s : Γ(M.scheme,U))
    (hc : centre.map reductionPoint ∈ U) (hg : M.genericMap point.val.schemePoint ∈ U),
    fraction (M.scheme.presheaf.germ U _ hc s) =
      X.left.evaluation (M.genericMap ⁻¹ᵁ U) point.val.schemePoint hg (M.genericMap.app U s)
  injective : Function.Injective fraction
  localUniformizer : M.scheme.presheaf.stalk (centre.map reductionPoint)
  uniformizerNonzero : localUniformizer ≠ 0
  maximalPrincipal : IsLocalRing.maximalIdeal (M.scheme.presheaf.stalk (centre.map reductionPoint)) =
    Ideal.span {localUniformizer}
  unitNorm : ∀ a : M.scheme.presheaf.stalk (centre.map reductionPoint), IsUnit a →
    point.val.absoluteValue (fraction a) = 1
  uniformizerNorm : point.val.absoluteValue (fraction localUniformizer) =
    Real.rpow ‖v.uniformizer‖ ((componentLength (S.components.frame C)).toNat : ℝ)⁻¹

variable [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

variable (N : ModelTuple K X hK (d + 1)
  (Fin.cons (structureModule X.left) L))

/-- The generic first line has its ACTUAL unit section; all other sections
are zero. The full Koszul is acyclic because this same first section is a unit. -/
def genericUnitSections : ∀ i : Fin (d+1), Γ(pullbackLines N.genericMap N.line i,⊤) := by
  intro i
  by_cases hi : i = 0
  · subst i
    exact (N.genericLine 0).inv.app ⊤
      (MetrizedFibrePowerModels.powerSectionAt (structureModule X.left) ⊤
        (1 : Γ(X.left,⊤)) (N.denominator 0))
  · exact 0

/-- Data for the model intersection (`modelIntersection`) of the model tuple $N$, whose first line
models a power of the structure sheaf: determinant data and presentations defining the Deligne line
of the model lines over $\operatorname{Spec} K^\circ$, where $K^\circ$ is the ring of integers of
$K$; a generator `integralFrame` of its sections over $K^\circ$; the derived base change to the
generic fibre, with the Koszul data of the generic sections (the unit section on the first line,
zero on the others) and their canonical evaluation `genericCanonical`; and a generator `frame` of
the generic determinant pairing over $K$ that corresponds to `integralFrame`. -/
structure ModelIntersectionSource where
  determinant : DeterminantSources
  presentations : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Spec (.of (integerRing K hK))),
    Presentations N.structureMap N.line R a
  deligne : DeligneLine determinant N.structureMap d N.line presentations
  integralFrame : Module.Basis Unit (integerRing K hK)
    (Sections (Over.mk (𝟙 (Spec (.of (integerRing K hK))))) deligne.line)
  genericBaseChange : DerivedCartesianBaseChange N.structureMap
    (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype)) N.genericMap X.hom N.genericSquare
  genericTensor : PullbackSubsetSources N.genericMap N.line
  genericPullbacks : DeterminantPullbackCoherence.Coherence.{0}
  genericKoszul : FullSectionKoszul (pullbackLines N.genericMap N.line) (genericUnitSections N)
  genericTotal : FullKoszulAffineSource X.hom (pullbackLines N.genericMap N.line) (genericUnitSections N)
    genericKoszul (.of K) (𝟙 _) (cartesianTopPresentations genericBaseChange genericTensor genericPullbacks
      (presentations (.of K) (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))))
  genericCanonical : CanonicalEvaluation determinant
    (fun t ↦ (cartesianTopPresentations genericBaseChange genericTensor genericPullbacks
      (presentations (.of K) (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))) t).complex)
    genericTotal.complex genericTotal.toTotalTermModel.assembly
  unitKoszul : KoszulAffineSource X.hom
    ((Scheme.Modules.pullback N.genericMap).obj (N.line 0))
    ((N.genericLine 0).inv.app ⊤
      (MetrizedFibrePowerModels.powerSectionAt (structureModule X.left) ⊤
        (1 : Γ(X.left,⊤)) (N.denominator 0))) (.of K) (𝟙 _)
  frame : Module.Basis Unit K
    (localPairing (presentations (.of K) (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))))
  frameSource : (tilde.isoTop
      (localPairing (presentations (.of K) (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))))).hom
      (frame ()) =
    (deligne.affine (.of K) (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))).hom.app ⊤
      (localPullbackSection (Spec.map (CommRingCat.ofHom (integerRing K hK).subtype))
        deligne.line ⊤ ⊤ (by simp) (integralFrame ()))

/-- Actual valuation-ring Deligne model intersection, with all rational denominators. -/
def modelIntersection (S : ModelIntersectionSource N) : ℝ :=
  -Real.log ‖S.frame.repr S.genericCanonical.value ()‖ /
    ∏ i : Fin (d+1), (N.denominator i : ℝ)

end MathlibExt.AlgebraicGeometry.NonarchimedeanChernModels
