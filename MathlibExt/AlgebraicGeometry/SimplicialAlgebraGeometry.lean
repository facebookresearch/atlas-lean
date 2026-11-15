/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Whiskering

/-!
# Actual simplicial algebras and derived-affine deformation maps

The domain is native simplicial commutative k-algebras. Mapping spaces
are the native simplicial Hom of an actual cofibrant replacement, and
π₀ is the actual algebra colimit. The underlying normalized cochain
complex uses the native Moore/Dold--Kan functor; a multiplicative shuffle
comparison is a separate model, not an assumed DG-algebra field.

Square-zero representatives have literal algebra terms, augmentation,
degreewise kernel-square-zero and Kan-fibration conditions. Their kernel
is the actual kernel of the module-valued natural transformation.
Deformation fibres and infinitesimal base-change maps use the fixed
space homotopy-pullback comparison, rather than a named tangent oracle.

References: PTVV, arXiv:1111.3209v4, conventions and §1; Toën--Vaquié,
arXiv:math/0503269v5, §§2.1 and 3.1. Classical polynomial resolutions and
the native Dold--Kan constructions are completed public-source support.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

open CategoryTheory Limits Opposite AlgebraicTopology
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits

universe u v

variable (k : Type u) [CommRing k]

/-- The actual simplicial commutative-algebra category. -/
abbrev SAlg := SimplicialObject (CommAlgCat.{u} k)

/-- The actual underlying simplicial sets, with their actual map components. -/
def underlying : SAlg k ⥤ SSet.{u} :=
  (Functor.whiskeringRight _ _ _).obj (forget (CommAlgCat.{u} k))

/-- Actual coefficient-module realization of the simplicial algebra. -/
def toModules : CommAlgCat.{u} k ⥤ ModuleCat.{u} k :=
  forget₂ (CommAlgCat.{u} k) (AlgCat.{u} k) ⋙ forget₂ (AlgCat.{u} k) (ModuleCat.{u} k)

variable {k}

/-- Simplicial algebra weak equivalence is fixed by its underlying realization. -/
def AlgebraWeakEquivalence {A B : SAlg k} (f : A ⟶ B) : Prop :=
  WeakEquivalence ((underlying k).map f)

/-- The actual Kan-fibration lifting property on the underlying map. -/
def IsAlgebraFibration {A B : SAlg k} (f : A ⟶ B) : Prop :=
  SSet.modelCategoryQuillen.J.rlp ((underlying k).map f)

/-- Actual trivial fibrations, used by the algebra cofibrancy criterion. -/
def IsAlgebraTrivialFibration {A B : SAlg k} (f : A ⟶ B) : Prop :=
  IsAlgebraFibration f ∧ AlgebraWeakEquivalence f

/-- The initial-object lifting criterion in the actual simplicial algebra category. -/
def IsAlgebraCofibrant (A : SAlg k) : Prop :=
  ∀ (B C : SAlg k) (p : B ⟶ C), IsAlgebraTrivialFibration p →
    ∀ f : A ⟶ C, ∃ g : A ⟶ B, g ≫ p = f

/-- Actual replacement functor and augmentation, with standard lifting conditions. -/
structure AlgebraReplacementFunctor (k : Type u) [CommRing k] where
  functor : SAlg k ⥤ SAlg k
  augmentation : functor ⟶ 𝟭 (SAlg k)
  cofibrant : ∀ A, IsAlgebraCofibrant (functor.obj A)
  trivialFibration : ∀ A, IsAlgebraTrivialFibration (augmentation.app A)

/-- The derived-affine mapping functor is literally Map(QA,-). -/
def derivedSpecFunctor (Q : AlgebraReplacementFunctor k) (A : SAlg k) :
    SAlg k ⥤ SSet.{u} :=
  (SimplicialCategory.sHomFunctor (SAlg k)).obj (op (Q.functor.obj A))

/-- Ring maps induce the actual contravariant maps of derived affine functors. -/
def derivedSpecMap (Q : AlgebraReplacementFunctor k) {A B : SAlg k} (f : A ⟶ B) :
    derivedSpecFunctor Q B ⟶ derivedSpecFunctor Q A :=
  (SimplicialCategory.sHomFunctor (SAlg k)).map (Q.functor.map f).op

/-- The literal π₀ algebra, computed as the simplicial algebra colimit. -/
def piZero (A : SAlg k) : CommAlgCat.{u} k := colimit A

/-- The actual induced π₀ algebra map. -/
def piZeroMap {A B : SAlg k} (f : A ⟶ B) : piZero A ⟶ piZero B := colim.map f

/-- The actual Moore normalized underlying module complex. Multiplication
is not silently asserted from the underlying module construction. -/
def normalizedChain (A : SAlg k) : ChainComplex (ModuleCat.{u} k) ℕ :=
  (normalizedMooreComplex (ModuleCat.{u} k)).obj (A ⋙ toModules k)

/-- The normalized cochain realization in nonpositive degrees. -/
def normalizedComplex (A : SAlg k) : CochainComplex (ModuleCat.{u} k) ℤ :=
  (normalizedChain A).extend (ComplexShape.embeddingUpIntLE 0)

/-- A strict fibrant representative of a genuine square-zero extension. -/
structure SquareZeroExtension (A : SAlg k) where
  algebra : SAlg k
  projection : algebra ⟶ A
  surjective : ∀ n, Function.Surjective (projection.app n).hom
  fibration : IsAlgebraFibration projection
  square_zero : ∀ n (x y : algebra.obj n),
    (projection.app n).hom x = 0 → (projection.app n).hom y = 0 → x * y = 0

/-- The actual simplicial module kernel of the extension projection. -/
def extensionKernel {A : SAlg k} (E : SquareZeroExtension A) :
    SimplicialObject (ModuleCat.{u} k) :=
  kernel (Functor.whiskerRight E.projection (toModules k))

/-- A space-valued derived prestack, with native functorial maps and
fibrant, homotopy-invariant values. No geometricity theorem is included. -/
structure DerivedPrestack (k : Type u) [CommRing k] where
  functor : SAlg k ⥤ SSet.{v}
  kan : ∀ A, SSet.KanComplex (functor.obj A)
  map_weak : ∀ {A B : SAlg k} (f : A ⟶ B),
    AlgebraWeakEquivalence f → WeakEquivalence (functor.map f)

/-- The actual deformation fibre at a specified affine-family point. -/
def deformationFibre (F : DerivedPrestack.{u, v} k) {A : SAlg k} (E : SquareZeroExtension A)
    (x : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ F.functor.obj A)
    (P : KanPathModel (F.functor.obj A)) : SSet.{v} :=
  homotopyFibre (F.functor.map E.projection) x P

/-- The fixed infinitesimal comparison of a natural map of prestacks. -/
def infinitesimalComparison {F G : DerivedPrestack.{u, v} k} (α : F.functor ⟶ G.functor)
    {A : SAlg k} (E : SquareZeroExtension A) (P : KanPathModel (G.functor.obj A)) :
    F.functor.obj E.algebra ⟶
      homotopyPullback (α.app A) (G.functor.map E.projection) P :=
  comparison (α.app A) (G.functor.map E.projection) P
    (F.functor.map E.projection) (α.app E.algebra) (α.naturality E.projection)

/-- Formal étaleness tests the actual square-zero comparison maps. The
path family is a sourced shared model input, with valid actual path objects. -/
def IsFormallyEtale {F G : DerivedPrestack.{u, v} k}
    (P : ∀ A, KanPathModel (G.functor.obj A)) (α : F.functor ⟶ G.functor) : Prop :=
  ∀ (A : SAlg k) (E : SquareZeroExtension A), WeakEquivalence (infinitesimalComparison α E (P A))

/-- Formal smoothness tests surjectivity on the actual path-component
quotient of the same infinitesimal comparison. -/
def IsFormallySmooth {F G : DerivedPrestack.{u, v} k}
    (P : ∀ A, KanPathModel (G.functor.obj A)) (α : F.functor ⟶ G.functor) : Prop :=
  ∀ (A : SAlg k) (E : SquareZeroExtension A),
    let f := SSet.toTop.map (infinitesimalComparison α E (P A))
    ∀ y, ∃ x, Joined (f x) y

end MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
