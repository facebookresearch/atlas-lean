/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantVirtualClassModels
public import MathlibExt.AlgebraicGeometry.EquivariantProjectivePushModels

/-!
# The source-normalized algebraic virtual-localization equation

The original and fixed classes are native cone/zero-section classes of
the original derived phi and its computed fixed restriction. The moving
inverse Euler is the finite Chern formula of the original dual moving
summands. Every summand uses the actual closed component map, its native
projective Chow push and the prescribed polynomial localization.

The source theorem retains the smooth equivariant closed ambient embedding.
It is a conditional comparison: `localizationFormula` is stated for a supplied `LocalizationData`
package, and the localization equality is requested for every such package. Assembling the package
from a scheme with a torus action, a POT and a smooth equivariant embedding (the quotient source
and character, the fixed Chow comparison data, and the polynomial compatibility of each component
push) is out of scope here; the separate requests cover only the individual pieces named in
`VirtualLocalizationSourcesWanted` (the ordinary and equivariant virtual geometry from given
sources, the rational Chow comparison, the fixed-Chow isomorphism and the moving Euler inverse).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.VirtualLocalizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open IntegralChowChernModels AlgebraicWeightBundleModels TorusFixedSchemeModels
open DerivedTwoTermObstructionModels FixedDerivedObstructionMaps
open EquivariantPerfectObstructionTheoryModels EquivariantVirtualClassModels
open AlgebraicEquivariantChowModels AlgebraicEquivariantCoefficientModels AlgebraicFixedChowModels
open AlgebraicMovingEulerModels RationalSchemeChowComparisonModels EquivariantProjectivePushModels
open EquivariantCharacterLineModels StackCycleRelations StackChowGroups
open scoped DirectSum

/-- The additional ambient hypothesis of the source localization theorem: an equivariant closed
embedding into a nonsingular variety (here: a smooth, separated, finite-type complex scheme). -/
structure EquivariantSmoothEmbedding (X : Over base) [ModObj Gm X] where
  ambient : SchemeData
  [action : ModObj Gm ambient.scheme]
  [smooth : Smooth ambient.scheme.hom]
  [separated : IsSeparated ambient.scheme.hom]
  embedding : X ⟶ ambient.scheme
  [closed : IsClosedImmersion embedding.left]
  equivariant : γ[Gm,X] ≫ embedding = (Gm ◁ embedding) ≫ γ[Gm,ambient.scheme]

attribute [instance] EquivariantSmoothEmbedding.action EquivariantSmoothEmbedding.smooth
  EquivariantSmoothEmbedding.separated EquivariantSmoothEmbedding.closed

theorem componentFixed {X : Over base} [ModObj Gm X] {S : FixedSchemeModel Gm X}
    (Z : FixedComponent Gm X S) : FixedPoint Gm X (Z.toAmbient Gm X) :=
  fixedReindex Gm X Z.inclusion S.inclusion S.fixed

variable {X : Over base} [ModObj Gm X] (E : EquivariantPOT X)
  (Q : EquivariantSource X) (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K :
    KreschPresentation D)
  (C : CharacterChernData Q D K characterOne) (F : SchemeData) (i : F.scheme ⟶ X)
  (hi : FixedPoint Gm X i)

local instance : ModObj Gm F.scheme := trivialAction F.scheme

include hi in
theorem fixedEquivariance : γ[Gm,F.scheme] ≫ i = (Gm ◁ i) ≫ γ[Gm,X] := hi.symm

/-- All fixed data are tied to the original source terms and the actual closed map. -/
structure FixedLocalizationData where
  [closed : IsClosedImmersion i.left]
  terms : FixedTerms E.terms i hi
  bundles : FixedBundleData E.terms i hi terms
  obstruction : FixedObstructionData E.terms i hi terms bundles
  properties : FixedTheoryProperties E i hi terms bundles obstruction
  ordinary : OrdinaryVirtualGeometry F (fixedDerivedPOT E i hi terms bundles obstruction properties)
  rational : NativeChowComparison F
  chow : FixedChowData F D K
  normal : VirtualNormalData F E.terms terms
  dimensionBound : ℕ
  dimension : topologicalKrullDim F.scheme.left ≤ (dimensionBound : ℕ)
  map : EquivariantMap chow.quotient Q i (fixedEquivariance F i hi)
  push : ProjectiveChowPushData D K chow.quotient.inScope Q.inScope map.map
  coefficients : PolynomialCompatible D K chow.quotient Q i (fixedEquivariance F i hi) map push
    chow.character C

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The actual localized component contribution [F]^vir/e(N^vir) and its closed push. -/
def localizedTerm (P : FixedLocalizationData E Q D K C F i hi) : LocalizedChow Q D K C :=
  localizedPush D K P.chow.quotient Q i (fixedEquivariance F i hi) P.map P.push P.chow.character C
    P.coefficients
    (fixedChowComparison F D K P.chow
      (inverseVirtualEuler F P.normal P.dimensionBound (P.ordinary.formalClass P.rational)))

/-- The data of the virtual localization formula for a `G_m`-equivariant perfect obstruction
theory `E` on a noetherian complex scheme `X` of finite type with a `G_m`-action: the quotient
stack `[X/G_m]` (`quotient`) with Chern data for the line bundle of the identity character
(`character`); the cone and vector-bundle data defining the virtual class of `X` for `E`
(`ordinary`) and their `G_m`-equivariant versions on quotient stacks (`equivariant`); a
`G_m`-equivariant closed embedding of `X` into a smooth separated complex scheme of finite type
(`ambient`); the fixed-point scheme of `X` (`fixed`) with its decomposition into finitely many
connected components (`components`); and, for each component, its fixed localization data
(`component`, see `FixedLocalizationData`). -/
structure LocalizationData (X : SchemeData) [ModObj Gm X.scheme]
    (E : EquivariantPOT X.scheme) (D : CycleConstructionData base (FiniteTypeArtin ℂ))
    (K : KreschPresentation D) where
  quotient : EquivariantSource X.scheme
  character : CharacterChernData quotient D K characterOne
  ordinary : OrdinaryVirtualGeometry X E.terms.obstruction
  equivariant : EquivariantVirtualGeometry X E quotient D K ordinary
  ambient : EquivariantSmoothEmbedding X.scheme
  fixed : FixedSchemeModel Gm X.scheme
  components : FixedComponents Gm X.scheme fixed
  component : ∀ j : Fin components.count,
    FixedLocalizationData E quotient D K character (components.component j).data
      ((components.component j).toAmbient Gm X.scheme) (componentFixed (components.component j))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The equation is formed from the actual maps and native classes, not supplied as data. -/
def localizationFormula {X : SchemeData} [ModObj Gm X.scheme] {E : EquivariantPOT X.scheme}
    {D : CycleConstructionData base (FiniteTypeArtin ℂ)} {K : KreschPresentation D}
    (P : LocalizationData X E D K) : Prop :=
  localize P.quotient D K P.character
    (DirectSum.lof ℚ ℤ (EquivariantChow D K P.quotient) (virtualDimension E.terms.obstruction)
      (equivariantVirtualClass X E P.quotient D K P.ordinary P.equivariant)) =
    ∑ j : Fin P.components.count,
      localizedTerm E P.quotient D K P.character (P.components.component j).data
        ((P.components.component j).toAmbient Gm X.scheme) (componentFixed (P.components.component
          j))
        (P.component j)

end MathlibExt.AlgebraicGeometry.VirtualLocalizationModels
