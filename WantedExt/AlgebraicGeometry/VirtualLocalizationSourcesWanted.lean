/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.VirtualLocalizationModels
public import MathlibExt.AlgebraicGeometry.EquivariantCotangentDiagramModels

/-!
# Native source adapters and the algebraic virtual-localization theorem

The cotangent request chooses a compatible source diagram. It does not
assert a strict cochain action for an arbitrary chosen cotangent model.
The affine cotangent and simplicial square constructions are completed
in AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
under Apache 2.0; these requests concern their native scheme-module
diagram adapter and geometric theorem proofs.

All obstruction maps remain the original derived phi or its computed
fixed restriction. All classes, Euler expressions and push maps in the
last theorem are the displayed native definitions. No localization
identity, inverse Euler or virtual class is an independent hypothesis.
Reference: Graber--Pandharipande alg-geom/9708001v2, Equation(1) and Section1, Proposition1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.VirtualLocalizationSources

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonObj
open MathlibExt.AlgebraicGeometry
open IntegralChowChernModels AlgebraicWeightBundleModels TorusFixedSchemeModels
open GlobalObstructionMorphisms DerivedTwoTermObstructionModels
open GlobalPerfectObstructionTheory
open SchemeDerivedCotangentPullbacks
open EquivariantDerivedObstructionModels FixedDerivedObstructionMaps
open EquivariantPerfectObstructionTheoryModels EquivariantVirtualClassModels
open AlgebraicEquivariantChowModels AlgebraicEquivariantCoefficientModels AlgebraicFixedChowModels
open AlgebraicMovingEulerModels RationalSchemeChowComparisonModels VirtualLocalizationModels
open StackCycleRelations StackChowGroups
open EquivariantCotangentDiagramModels

/-- Choose the source-compatible native global action/product cotangent diagram. -/
def_wanted source_adapted_action_cotangent (X : SchemeData) [ModObj Gm X.scheme] :
    Σ C : CotangentNormalization X.scheme.hom, CotangentActionData X.scheme C

/-- Choose the whole native action/fixed diagram with one shared original source model. -/
def_wanted source_adapted_cotangent_diagram (X : SchemeData) [ModObj Gm X.scheme]
    (F : FixedSchemeModel Gm X.scheme) (Z : FixedComponents Gm X.scheme F) :
    CotangentDiagram X.scheme F Z

/-- Adapt the actual derived scheme-module pullback, with its native derived counit. -/
def_wanted actual_scheme_derived_pullback (X Y : Scheme.{0}) (f : Y ⟶ X) :
    DerivedPullbackSource f

/-- Finite vector-bundle sources are acyclic for that native pullback. -/
theorem_wanted actual_two_term_pullback_acyclic (X Y : Scheme.{0}) (f : Y ⟶ X)
    (P : DerivedPullbackSource f) (E : GlobalPOTVirtualClass.TwoTermModel X) :
    SourceAcyclic f P E

/-- Source transport is computed from the original two term linearizations. -/
def_wanted actual_obstruction_source_action (X : Over base) [ModObj Gm X]
    (E : EquivariantObstructionTerms X) (C : CotangentActionData X E.obstruction.cotangent) :
    SourceActionData E C

/-- The all-scheme fixed functor retains nonreduced coefficient tests. -/
def_wanted actual_fixed_scheme (X : SchemeData) [ModObj Gm X.scheme] :
    FixedSchemeModel Gm X.scheme

/-- Connected components retain their actual closed embeddings and cover of the fixed scheme. -/
def_wanted actual_fixed_components (X : SchemeData) [ModObj Gm X.scheme]
    (F : FixedSchemeModel Gm X.scheme) : FixedComponents Gm X.scheme F

/-- Represent the given derived map, using its actual native injective replacement. -/
def_wanted original_derived_pot_presentation (X : Over base) (P : DerivedPOT X) :
    CochainPresentation P

/-- Fixed bundles and their differential are the computed weight-zero source sums. -/
def_wanted actual_fixed_bundle_source (X : Over base) [ModObj Gm X]
    (E : EquivariantPOT X) (F : SchemeData) (i : F.scheme ⟶ X)
    (hi : FixedPoint Gm X i) (W : FixedTerms E.terms i hi) :
    FixedBundleData E.terms i hi W

/-- The native inclusion is fixed in both original nonzero cochain degrees. -/
def_wanted actual_fixed_source_inclusion (X : Over base) [ModObj Gm X]
    (E : EquivariantPOT X) (F : SchemeData) (i : F.scheme ⟶ X)
    (hi : FixedPoint Gm X i) (W : FixedTerms E.terms i hi)
    (B : FixedBundleData E.terms i hi W) : FixedSourceData E.terms i hi W B

/-- The fixed map uses the same chosen original model in the compatible full diagram: its fixed
cotangent model and square map are the diagram's own (`Diagram.fixed j`, `Diagram.square j`, after
transport along `_original`). -/
def_wanted source_compatible_fixed_obstruction (X : SchemeData) [ModObj Gm X.scheme]
    (E : EquivariantPOT X.scheme) (S : FixedSchemeModel Gm X.scheme)
    (Z : FixedComponents Gm X.scheme S) (Diagram : CotangentDiagram X.scheme S Z)
    (_original : E.terms.obstruction.cotangent = Diagram.original) (j : Fin Z.count)
    (W : FixedTerms E.terms ((Z.component j).toAmbient Gm X.scheme) (componentFixed (Z.component
      j)))
    (B : FixedBundleData E.terms ((Z.component j).toAmbient Gm X.scheme)
      (componentFixed (Z.component j)) W) :
    {P : FixedObstructionData E.terms ((Z.component j).toAmbient Gm X.scheme)
        (componentFixed (Z.component j)) W B //
      P.cotangent = Diagram.fixed j ∧ HEq P.differential (Diagram.square j)}

/-- The fixed homology and amplitude claims concern the already computed induced phi. -/
theorem_wanted induced_fixed_pot_properties (X : SchemeData) [ModObj Gm X.scheme]
    (E : EquivariantPOT X.scheme) (_ambient : EquivariantSmoothEmbedding X.scheme)
    (S : FixedSchemeModel Gm X.scheme)
    (Z : FixedComponent Gm X.scheme S)
    (W : FixedTerms E.terms (Z.toAmbient Gm X.scheme) (componentFixed Z))
    (B : FixedBundleData E.terms (Z.toAmbient Gm X.scheme) (componentFixed Z) W)
    (P : FixedObstructionData E.terms (Z.toAmbient Gm X.scheme) (componentFixed Z) W B) :
    FixedTheoryProperties E (Z.toAmbient Gm X.scheme) (componentFixed Z) W B P

/-- The coefficient comparison sends every original integral generic-point cycle to itself. -/
def_wanted actual_rational_scheme_chow_comparison (F : SchemeData) : NativeChowComparison F

/-- The ordinary geometry uses a presentation of this exact original derived phi. -/
def_wanted actual_original_virtual_geometry (X : SchemeData) (P : DerivedPOT X.scheme) :
    OrdinaryVirtualGeometry X P

/-- The native fixed-action flat-pull/character coefficient map is bijective. -/
theorem_wanted actual_fixed_chow_isomorphism (F : SchemeData)
    (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
    (P : FixedChowData F D K) : FixedChowIsomorphism F D K P

/-- The finite formula inverts the Euler cap of the original actual moving dual bundles. -/
theorem_wanted finite_moving_euler_inverse (F : SchemeData)
    (E : List (DualMovingSummand F)) (d : ℕ)
    (_dimension : topologicalKrullDim F.scheme.left ≤ (d : ℕ)) :
    movingEuler F E * inverseMovingEuler F E d = 1 ∧
      inverseMovingEuler F E d * movingEuler F E = 1

/-- Quotient the same original cone and dual bundle, with their native zero-section class. -/
def_wanted actual_equivariant_virtual_geometry (X : SchemeData) [ModObj Gm X.scheme]
    (E : EquivariantPOT X.scheme) (Q : EquivariantSource X.scheme)
    (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
    (O : OrdinaryVirtualGeometry X E.terms.obstruction) :
    EquivariantVirtualGeometry X E Q D K O

/-- The virtual localization formula. Let $X$ be a scheme of finite type over $\mathbb{C}$ with a
$\mathbb{G}_m$-action and a $\mathbb{G}_m$-equivariant perfect obstruction theory $E$, let `D` and
`K` be cycle data and a Kresch presentation for Artin stacks of finite type over $\mathbb{C}$, and
let `P` be localization data for $X$ and $E$ (`LocalizationData`: a model of the quotient stack
$[X/\mathbb{G}_m]$ (`EquivariantSource`) with Chern data for the identity character, the ordinary
and equivariant virtual geometry of $E$, a $\mathbb{G}_m$-equivariant closed embedding of $X$ into
a smooth separated scheme of finite type over $\mathbb{C}$, the fixed scheme with its connected
components $F_j$, and for each $F_j$ its fixed obstruction theory, virtual normal bundle
$N_j^{\mathrm{vir}}$ and push-forward data along $\iota_j : F_j \to X$). Then, in the localized
equivariant Chow group (`localizationFormula`),
$[X]^{\mathrm{vir}} = \sum_j \iota_{j*}([F_j]^{\mathrm{vir}} \cap e(N_j^{\mathrm{vir}})^{-1})$. -/
theorem_wanted virtual_localization (X : SchemeData) [ModObj Gm X.scheme]
    (E : EquivariantPOT X.scheme)
    (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
    (P : LocalizationData X E D K) : localizationFormula P

end WantedExt.AlgebraicGeometry.VirtualLocalizationSources
