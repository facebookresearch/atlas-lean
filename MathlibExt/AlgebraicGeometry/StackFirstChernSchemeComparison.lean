/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackFirstChernOperators
public import MathlibExt.AlgebraicGeometry.IntegralGysinRecipes
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Native scheme comparison for the stack first Chern cap

The scheme source represents sections of the actual line module on every
parameter scheme. Its zero represents the literal zero module section.
Its cap is inverse projection pull after zero push on the existing integral
scheme Chow carrier. These ordinary maps and homotopy identities are the
completed AxiomMath/Stacks scheme source; they are not new Wanted theorems.

The stack comparison keeps the full total-space, projection and zero maps,
and the actual cycle-class comparison to the same scheme Chow groups.
Conventions: here the total space of the line module `L` represents sections
`𝒪 → f^*L`, so it is `Spec Sym(Lᵛ)` and the self-intersection of its zero
section caps with `+c₁(L)`. The pinned AxiomMath
`Chow/AffineBundle/ZeroSectionSelfIntersection.lean` uses the total space
`Spec Sym(ℒ)` and obtains `-c₁(ℒ)`; it applies with `ℒ = Lᵛ`.

References: Kresch, arXiv:math/9810166v1, Theorem 2.1.12; Fulton,
Intersection Theory, Sections 2.1 and 3.3; AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b,
Chow/AffineBundle/ZeroSectionSelfIntersection.lean and
Chow/AffineBundle/LineBundleChowBijective.lean, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AlgebraicGeometry.StackFirstChernSchemeComparison

open CategoryTheory CategoryTheory.Limits
open StackCycleGeometry StackCycleRelations StackFibreModels StackVectorBundles StackChowGroups
open StackFirstChernOperators IntegerSchemeChow IntegralOperationalChow
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry

variable {k : Type} [Field k]

/-- Pull a genuine line-module section using native unit and composition. -/
def sectionPullback {U : FieldScheme k} (L : U.scheme.left.Modules)
    {T V : Over U.scheme.left} (f : V ⟶ T)
    (s : structureModule T.left ⟶ (Scheme.Modules.pullback T.hom).obj L) :
    structureModule V.left ⟶ (Scheme.Modules.pullback V.hom).obj L :=
  (pullbackUnit V.left T.left f.left).inv ≫ (Scheme.Modules.pullback f.left).map s ≫
    (Scheme.Modules.pullbackComp f.left T.hom).hom.app L ≫
      (Scheme.Modules.pullbackCongr (Over.w f)).hom.app L

def schemeZeroPoint {U V : FieldScheme k} (p : V.scheme ⟶ U.scheme)
    (z : U.scheme ⟶ V.scheme) (h : z ≫ p = 𝟙 U.scheme)
    (T : Over U.scheme.left) : T ⟶ Over.mk p.left :=
  Over.homMk (T.hom ≫ z.left) (by
    change (T.hom ≫ z.left) ≫ p.left = T.hom
    have hh := congrArg Over.Hom.left h
    change z.left ≫ p.left = 𝟙 U.scheme.left at hh
    rw [Category.assoc, hh, Category.comp_id])

def schemeProjectionPull (O : CycleOperations (k := k))
    {U V : FieldScheme k} (p : V.scheme ⟶ U.scheme) [Flat p.left]
    (pure : PureRelativeDimension p 1) (d : ℤ) :
    IntegerSchemeChow.ChowGroup U (d - 1) →+ IntegerSchemeChow.ChowGroup V d :=
  (IntegralGysinRecipes.chowCast V (by omega)).comp (O.flat p 1 pure (d - 1))

/-- Conditional integration of the ordinary, completed scheme line source.
All modules, sections, zero maps and Chow maps have fixed native endpoints. -/
structure SchemeLineSource (O : CycleOperations (k := k))
    (U : FieldScheme k) (L : U.scheme.left.Modules) where
  line : IsLineBundle L
  total : FieldScheme k
  projection : total.scheme ⟶ U.scheme
  zero : U.scheme ⟶ total.scheme
  zero_over : zero ≫ projection = 𝟙 U.scheme
  [flat : Flat projection.left]
  [zero_proper : IsProper zero.left]
  pure : PureRelativeDimension projection 1
  sections : ∀ T : Over U.scheme.left,
    (T ⟶ Over.mk projection.left) ≃
      (structureModule T.left ⟶ (Scheme.Modules.pullback T.hom).obj L)
  naturality : ∀ {T V : Over U.scheme.left} (f : V ⟶ T)
    (s : T ⟶ Over.mk projection.left),
    sections V (f ≫ s) = sectionPullback L f (sections T s)
  zero_section : ∀ T : Over U.scheme.left,
    sections T (schemeZeroPoint projection zero zero_over T) = 0
  homotopy : ∀ d : ℤ, Function.Bijective (schemeProjectionPull O projection pure d)

attribute [instance] SchemeLineSource.flat SchemeLineSource.zero_proper

def schemeFirstChern {O : CycleOperations (k := k)}
    {U : FieldScheme k} {L : U.scheme.left.Modules} (C : SchemeLineSource O U L)
    (d : ℤ) : IntegerSchemeChow.ChowGroup U d →+
      IntegerSchemeChow.ChowGroup U (d - 1) :=
  (AddEquiv.ofBijective (schemeProjectionPull O C.projection C.pure d)
    (C.homotopy d)).symm.toAddMonoidHom.comp (O.proper C.zero d)

/-- The full native total-space and zero diagrams identify the line geometry;
the desired cap equality is not part of this background identification. -/
structure SchemeGeometry {X : Stack (Spec (.of k))} {E : VectorBundle X}
    (z : StackBundleCones.ZeroSection E) {U : FieldScheme k}
    (dictionary : SchemeCycleDictionary U X)
    {O : CycleOperations (k := k)} {L : U.scheme.left.Modules}
    (source : SchemeLineSource O U L) where
  bundleDictionary : SchemeCycleDictionary source.total E.total
  projection : totalMap E.projection ⋙ dictionary.comparison.functor ≅
    bundleDictionary.comparison.functor ⋙ Over.map source.projection.left
  zero : totalMap z.map ⋙ bundleDictionary.comparison.functor ≅
    dictionary.comparison.functor ⋙ Over.map source.zero.left

variable
  (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k))
  (K : KreschPresentation D)
  {X : Stack (Spec (.of k))} (hX : FiniteTypeArtin k X)
  {E : VectorBundle X} (C : FirstChernData D K hX E)
  (U : FieldScheme k) (dictionary : SchemeCycleDictionary U X)
  (classes : CycleClassData D K X hX)
  (comparison : SchemeComparisonData D K U X hX dictionary classes)
  (O : CycleOperations (k := k)) (L : U.scheme.left.Modules)
  (source : SchemeLineSource O U L)

/-- The entire zero and projection diagrams commute through the actual
scheme representations, and the caps use those same cycle-class maps. -/
structure SchemeComparison where
  geometry : SchemeGeometry C.zero dictionary source
  cap : ∀ (d : ℤ) (a : ChowGroup D K X hX d),
    comparison.map (d - 1) (firstChern C d a) =
      schemeFirstChern source d (comparison.map d a)

end AlgebraicGeometry.StackFirstChernSchemeComparison
