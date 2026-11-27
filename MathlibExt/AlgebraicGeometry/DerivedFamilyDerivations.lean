/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

/-!
# Derived derivations over the whole affine-family diagram

At a family (A,n,x), the lift space is the native Hom from Δ[n] to
X(E), mapped to the corresponding Hom into X(A), over the actual
simplex x. Reindexing uses both the actual algebra and simplex maps.
The global derivation space is the native homotopy limit of these
actual based fibres. This retains stack automorphisms and descent.

Kernel QCoh sections are fixed on the entire semilinear kernel diagram,
using the enhanced raw-module localization. They are not independently
selected objects with isomorphic fibres.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV arXiv:1111.3209v4, conventions
and §1.2; Lurie, Higher Algebra, §7.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.HomotopicalAlgebra
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- Actual standard-simplex parameters, contravariant in their family maps. -/
def simplexFamilies (X : Prestack k) : (Families X)ᵒᵖ ⥤ SSet.{u + 1} where
  obj j := SSet.stdSimplex.obj j.unop.obj.2.unop
  map f := SSet.stdSimplex.map f.unop.hom.2.unop
  map_id j := by simp
  map_comp f g := by simp [← Functor.map_comp]

/-- The native mapping-diagram construction is a composition of actual functors. -/
def mappingFamiliesFunctor (X : Prestack k) :
    (Families X ⥤ SSet.{u + 1}) ⥤ (Families X ⥤ SSet.{u + 1}) :=
  (((Functor.const (Families X ⥤ SSet.{u + 1})).obj
      ((opOpEquivalence (Families X)).inverse ⋙ (simplexFamilies X).op)).prod' (𝟭 _)) ⋙
    CategoryTheory.prodFunctor ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag (Families X)) ⋙
    (Functor.whiskeringRight _ _ _).obj
      (Functor.uncurry.obj (SimplicialCategory.sHomFunctor SSet.{u + 1}))

/-- Native mapping diagrams keep every simplex of the varying affine family. -/
def mappingFamilies (X : Prestack k) (F : Families X ⥤ SSet.{u + 1}) :
    Families X ⥤ SSet.{u + 1} := (mappingFamiliesFunctor X).obj F

/-- Native mapping functoriality on the actual full family diagrams. -/
def mappingFamiliesMap (X : Prestack k) {F G : Families X ⥤ SSet.{u + 1}} (t : F ⟶ G) :
    mappingFamilies X F ⟶ mappingFamilies X G := (mappingFamiliesFunctor X).map t

/-- The full diagram of actual lift mapping spaces X(E). -/
def liftDiagram (X : Prestack k) (E : SquareZeroFamily X) : Families X ⥤ SSet.{u + 1} :=
  mappingFamilies X (E.algebra ⋙ X)

/-- The corresponding actual mapping spaces X(A). -/
def baseDiagram (X : Prestack k) : Families X ⥤ SSet.{u + 1} :=
  mappingFamilies X (algebraProjection X ⋙ X)

/-- Actual split algebra projection induces the fixed map of lift diagrams. -/
def liftProjection (X : Prestack k) (E : SquareZeroFamily X) :
    liftDiagram X E ⟶ baseDiagram X :=
  mappingFamiliesMap X (Functor.whiskerRight E.projection X)

/-- The actual tautological simplex in every affine-family mapping space. -/
def familyPoint (X : Prestack k) :
    (Functor.const (Families X)).obj (Δ[0] : SSet.{u + 1}) ⟶ baseDiagram X where
  app j := SSet.const ((SimplicialCategory.homEquiv' _ _) (SSet.yonedaEquiv.symm j.val))
  naturality i j f := by
    apply SSet.yonedaEquiv.injective
    apply (SimplicialCategory.homEquiv' (SSet.stdSimplex.obj j.obj.2.unop)
      (X.obj j.obj.1)).symm.injective
    simp only [Functor.const_obj_map]
    symm
    change SSet.stdSimplex.map f.hom.2.unop ≫ SSet.yonedaEquiv.symm i.val ≫
      X.map f.hom.1 = SSet.yonedaEquiv.symm j.val
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_naturality_left]
    exact congrArg SSet.yonedaEquiv.symm f.map_val

/-- A natural Kan path model for the fixed actual family mapping diagram. -/
structure DerivationBase (X : Prestack k) extends PrepathObject (baseDiagram X) where
  kan : ∀ j : Families X, SSet.KanComplex ((baseDiagram X).obj j)
  diagonal_weak : ∀ j : Families X, WeakEquivalence (ι.app j)
  endpoints_fibration : ∀ j : Families X,
    SSet.modelCategoryQuillen.J.rlp (prod.lift (p₀.app j) (p₁.app j))

/-- Global first-order lifts are the actual functor-category pullback of those endpoints. -/
def derivationDiagram {X : Prestack k} (B : DerivationBase X) (E : SquareZeroFamily X) :
    Families X ⥤ SSet.{u + 1} :=
  pullback (prod.map (liftProjection X E) (familyPoint X)) (prod.lift B.p₀ B.p₁)

/-- The exact global derivation model uses a replacement of that fixed diagram. -/
structure DerivationModel {X : Prestack k} (B : DerivationBase X) (E : SquareZeroFamily X) where
  replacement : SpaceDiagramReplacement.{u, u + 1, u} (derivationDiagram B E)

/-- The actual global derivation space, retaining all affine/simplex compatibility. -/
def derivationSpace {X : Prestack k} {B : DerivationBase X} {E : SquareZeroFamily X}
    (R : DerivationModel B E) : SSet.{u + 1} := limit R.replacement.diagram

/-- The kernel section is fixed by the complete semilinear diagram and localization map. -/
structure KernelQCohModel {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    {X : Prestack k} {E : SquareZeroFamily X} (K : KernelFamily N E) where
  object : (qcoh M X) _⦋0⦌
  normalized : (SimplicialCategory.homEquiv' (nerve (Families X)) M.total).symm object.val =
    nerveMap K.functor ≫ R.map

/-- Actual localization and cocartesian transport construct the whole kernel section.
The full map is fixed; no separate affine fibre choices enter this definition. -/
def kernelQCohModel {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (R : RawModuleRealization M)
    {X : Prestack k} {E : SquareZeroFamily X} (K : KernelFamily N E)
    (base : K.functor ⋙ moduleProjection N = algebraProjection X)
    (cartesian : ∀ e : (nerve (Families X)) _⦋1⦌,
      MathlibExt.AlgebraicTopology.CategoricalCocartesianSections.IsCocartesianEdge M.projection
        ((nerveMap K.functor ≫ R.map).app (op ⦋1⦌) e)) : KernelQCohModel M R K := by
  let f := nerveMap K.functor ≫ R.map
  refine ⟨⟨(SimplicialCategory.homEquiv' (nerve (Families X)) M.total) f, ?_, ?_⟩, ?_⟩
  · intro m g b
    change M.projection.app m (f.app m b) = (nerveMap (algebraProjection X)).app m b
    have hf : f ≫ M.projection = nerveMap (algebraProjection X) := by
      dsimp only [f]
      rw [Category.assoc, R.over]
      change nerveMap (K.functor ⋙ moduleProjection N) = nerveMap (algebraProjection X)
      rw [base]
    exact congrArg (fun t => t.app m b) hf
  · intro i e
    exact cartesian e
  · exact Equiv.symm_apply_apply _ f

end MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
