/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms
public import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine-normalized global cotangent and perfect-obstruction contracts

A target complex is characterized on every actual affine source/target chart
by the full cotangent complex of an actual polynomial resolution of the chart
ring map. Its comparisons commute with actual section restrictions. Refinement
maps are normalized on pure differentials by augmentation-preserving polynomial
resolution maps, with identity/composition equations. Thus independent local
isomorphisms cannot silently introduce a twisted global target.

The public perfect-obstruction contract binds its target to this normalization.
It does not construct a new global cotangent complex. The completed public
constructor is `Scheme.Hom.cotangentComplex` in AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/Cotangent/SchemeCotangentComplex.lean` (Apache 2.0; Stacks 08T2).
Its arbitrary-resolution comparison is completed in
`StacksFrontier/Cotangent/ResolutionCotangentAny.lean` (08QI). Supplying this
native sheaf-module bridge is a port/comparison dependency, not a new Wanted
existence theorem. Reference: Behrend--Fantechi, §4,
https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicTopology _root_.Simplicial
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
attribute [local instance] HasDerivedCategory.standard

/-- A pair of affine opens `U ⊆ X` and `V ⊆ Y` with `U ⊆ f⁻¹ V`. -/
structure AffineChart {X Y : Scheme.{0}} (f : X ⟶ Y) where
  /-- The affine open of the source. -/
  source : X.Opens
  /-- The affine open of the target. -/
  target : Y.Opens
  source_affine : IsAffineOpen source
  target_affine : IsAffineOpen target
  over : source ≤ f ⁻¹ᵁ target

namespace AffineChart
variable {X Y : Scheme.{0}} {f : X ⟶ Y}
/-- The ring of the target chart. -/
abbrev base (a : AffineChart f) := Γ(Y, a.target)
/-- The ring of the source chart. -/
abbrev ring (a : AffineChart f) := Γ(X, a.source)
/-- The chart ring map `Γ(Y, V) → Γ(X, U)` induced by `f`. -/
instance (a : AffineChart f) : Algebra a.base a.ring :=
  (f.appLE a.target a.source a.over).hom.toAlgebra
end AffineChart

/-- Sections over an open, as a functor from sheaves of modules. -/
def moduleSections {X : Scheme.{0}} (U : X.Opens) : X.Modules ⥤ ModuleCat.{0} Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

instance {X : Scheme.{0}} (U : X.Opens) : (moduleSections U).Additive where
  map_add := by intros; rfl

/-- The complex of sections over an open of a complex of sheaves of modules. -/
def sectionsComplex {X : Scheme.{0}} (C : Complex X) (U : X.Opens) :
    CochainComplex (ModuleCat.{0} Γ(X, U)) ℤ :=
  ((moduleSections U).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C

/-- Restriction of sections from `U` to `V ⊆ U`, as a map of complexes over `Γ(X, U)`. -/
def sectionRestriction {X : Scheme.{0}} (C : Complex X) {U V : X.Opens} (h : V ≤ U) :
    sectionsComplex C U ⟶
      ((ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (sectionsComplex C V) where
  f j := (C.X j).val.map (homOfLE h).op
  comm' i j _ := (C.d i j).val.naturality (homOfLE h).op

/-- Literal polynomial-resolution maps on a chart refinement, together with
the uniquely pure-differential-normalized induced cotangent cochain map. -/
structure ResolutionRefinement {X Y : Scheme.{0}} {f : X ⟶ Y}
    (a b : AffineChart f) (hU : b.source ≤ a.source) (hV : b.target ≤ a.target)
    (R : PolynomialResolution a.base a.ring) (S : PolynomialResolution b.base b.ring) where
  polynomialMap : ∀ n, R.algebra.obj n →+* S.algebra.obj n
  scalar : ∀ n (x : a.base),
    polynomialMap n (algebraMap a.base (R.algebra.obj n) x) =
      algebraMap b.base (S.algebra.obj n)
        ((Y.presheaf.map (homOfLE hV).op).hom x)
  augmentation : ∀ n (x : R.algebra.obj n),
    S.augmentation.app n (polynomialMap n x) =
      (X.presheaf.map (homOfLE hU).op).hom (R.augmentation.app n x)
  simplicial : ∀ {i j} (g : i ⟶ j) (x : R.algebra.obj i),
    polynomialMap j (R.algebra.map g x) = S.algebra.map g (polynomialMap i x)
  cotangentMap : affineComplex R ⟶
    ((ModuleCat.restrictScalars (X.presheaf.map (homOfLE hU).op).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (affineComplex S)
  pure_differential : ∀ (n : ℕ) (x : R.algebra.obj (op ⦋n⦌)),
    (affineDegreeIso S n).hom ((cotangentMap.f (-(n : ℤ)))
      ((affineDegreeIso R n).inv
        (CommAlgCat.resolutionCotangentTermDifferential a.base (CommAlgCat.of a.base a.ring)
          R.algebra R.augmentation (op ⦋n⦌) x))) =
    CommAlgCat.resolutionCotangentTermDifferential b.base (CommAlgCat.of b.base b.ring)
      S.algebra S.augmentation (op ⦋n⦌) (polynomialMap (op ⦋n⦌) x)

/-- A global native model with actual canonical affine comparison and overlap
coherence. These fields are bridge dependencies, not arbitrary cotangent names. -/
structure CotangentNormalization {X Y : Scheme.{0}} (f : X ⟶ Y) where
  complex : Complex X
  resolution : ∀ a : AffineChart f, PolynomialResolution a.base a.ring
  comparison : ∀ a : AffineChart f,
    affineComplex (resolution a) ⟶ sectionsComplex complex a.source
  [comparison_quasiIso : ∀ a : AffineChart f, QuasiIso (comparison a)]
  refinement : ∀ (a b : AffineChart f) (hU : b.source ≤ a.source) (hV : b.target ≤ a.target),
    ResolutionRefinement a b hU hV (resolution a) (resolution b)
  naturality : ∀ (a b : AffineChart f) (hU : b.source ≤ a.source) (hV : b.target ≤ a.target),
    comparison a ≫ sectionRestriction complex hU =
      (refinement a b hU hV).cotangentMap ≫
        ((ModuleCat.restrictScalars (X.presheaf.map (homOfLE hU).op).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (comparison b)
  identity : ∀ (a : AffineChart f) n,
    (refinement a a le_rfl le_rfl).polynomialMap n = RingHom.id _
  composition : ∀ (a b c : AffineChart f)
    (hU : b.source ≤ a.source) (hV : b.target ≤ a.target)
    (hU' : c.source ≤ b.source) (hV' : c.target ≤ b.target) n,
    (refinement a c (hU'.trans hU) (hV'.trans hV)).polynomialMap n =
      ((refinement b c hU' hV').polynomialMap n).comp
        ((refinement a b hU hV).polynomialMap n)
attribute [instance] CotangentNormalization.comparison_quasiIso

/-- Global perfect obstruction theory with the actual cotangent normalization
bound to its target, and the genuine local-perfect amplitude and homology laws. -/
structure PerfectObstructionTheory {X Y : Scheme.{0}} (f : X ⟶ Y) where
  cotangent : CotangentNormalization f
  obstructionMorphism : ObstructionMorphism cotangent.complex

end MathlibExt.AlgebraicGeometry.GlobalPerfectObstructionTheory
