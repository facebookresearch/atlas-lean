/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# The actual derived affine étale site and hyperdescent predicates

The site uses actual cofibrant simplicial commutative algebras. Its
covering generators are algebra cofibrations with étale pi-zero scheme
maps and the fixed derived square-zero comparison. Cofibrations are
the native trivial-fibration lifting test, so their strict pushouts
between cofibrant algebras are the intended derived base-change models.

A local trivial fibration is tested by literal simplex-boundary lifting
after a covering presieve on that site. A derived stack is an actual
homotopy-invariant, Kan-valued, injectively fibrant prestack with descent
for these local trivial fibrations, using the native enriched mapping
comparison. No Artin atlas, perfect cotangent or moduli theorem is a field.

Affines use an actual weak augmentation from Map(QA,-) to a stack model.
Injective fibrant replacement is not asserted to leave that raw affine
functor literally unchanged.

References: Toën--Vezzosi, Homotopical Algebraic Geometry II,
arXiv:math/0404373, Part 2; Toën--Vaquié, arXiv:math/0503269v5, §2.1;
PTVV, arXiv:1111.3209v4, conventions and §1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels

open CategoryTheory Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

variable {k : Type u} [CommRing k]

/-- Algebra cofibrancy of a morphism uses its actual square lifting problem. -/
def IsAlgebraCofibration {A B : SAlg k} (f : A ⟶ B) : Prop :=
  ∀ (C D : SAlg k) (p : C ⟶ D), IsAlgebraTrivialFibration p →
    ∀ (a : A ⟶ C) (b : B ⟶ D), a ≫ p = f ≫ b →
      ∃ l : B ⟶ C, f ≫ l = a ∧ l ≫ p = b

/-- The actual cofibrant algebra subcategory, retaining its original arrows. -/
abbrev CofibrantAlgebra (k : Type u) [CommRing k] :=
  (show ObjectProperty (SAlg k) from IsAlgebraCofibrant).FullSubcategory

/-- The literal pi-zero affine scheme. -/
def piZeroScheme (A : SAlg k) : Scheme.{u} :=
  Spec ((forget₂ (CommAlgCat.{u} k) CommRingCat).obj (piZero A))

/-- Its actual contravariant algebra-induced scheme map. -/
def piZeroSchemeMap {A B : SAlg k} (f : A ⟶ B) :
    piZeroScheme B ⟶ piZeroScheme A :=
  Spec.map ((forget₂ (CommAlgCat.{u} k) CommRingCat).map (piZeroMap f))

/-- The actual lifted affine natural map. -/
def affineMap {A B : SAlg k} (Q : AlgebraReplacementFunctor k) (f : A ⟶ B) :
    affineMapping k Q B ⟶ affineMapping k Q A :=
  Functor.whiskerRight (derivedSpecMap Q f) liftSimplicial

/-- The fixed comparison of an affine map on a genuine square-zero extension. -/
def affineInfinitesimalComparison {A B T : SAlg k}
    (Q : AlgebraReplacementFunctor k) (f : A ⟶ B) (E : SquareZeroExtension T)
    (P : KanPathModel ((affineMapping k Q A).obj T)) :
    (affineMapping k Q B).obj E.algebra ⟶
      homotopyPullback ((affineMap Q f).app T)
        ((affineMapping k Q A).map E.projection) P :=
  comparison ((affineMap Q f).app T) ((affineMapping k Q A).map E.projection) P
    ((affineMapping k Q B).map E.projection) ((affineMap Q f).app E.algebra)
    ((affineMap Q f).naturality E.projection)

/-- Derived étaleness of a map of simplicial algebras: its `π₀` scheme map is étale and the
derived square-zero comparison of the replaced affine mapping prestacks is a weak equivalence. Both
conditions are homotopy invariant; no cofibration condition is imposed here. -/
def IsDerivedEtale {A B : SAlg k} (Q : AlgebraReplacementFunctor k) (f : A ⟶ B) : Prop :=
  Etale (piZeroSchemeMap f) ∧
    ∀ (T : CofibrantAlgebra k) (E : SquareZeroExtension T.obj)
      (P : KanPathModel ((affineMapping k Q A).obj T.obj)),
      WeakEquivalence (affineInfinitesimalComparison Q f E P)

/-- A covering generator of the étale site: a derived étale map that is moreover an algebra
cofibration, so that strict pushouts along it model derived base change. This point-set choice of
representatives is separate from the invariant predicate `IsDerivedEtale`. -/
def IsEtaleCoverGenerator {A B : SAlg k} (Q : AlgebraReplacementFunctor k) (f : A ⟶ B) : Prop :=
  IsAlgebraCofibration f ∧ IsDerivedEtale Q f

/-- Joint surjectivity uses the actual pi-zero scheme images. -/
def IsEtaleCover (Q : AlgebraReplacementFunctor k) (A : CofibrantAlgebra k)
    (R : Presieve (op A)) : Prop :=
  (∀ (B : CofibrantAlgebra k) (f : op B ⟶ op A), R f →
    IsEtaleCoverGenerator Q f.unop.hom) ∧
  ∀ x : piZeroScheme A.obj, ∃ (B : CofibrantAlgebra k) (f : op B ⟶ op A),
    R f ∧ ∃ y : piZeroScheme B.obj, piZeroSchemeMap f.unop.hom y = x

/-- The covering precoverage consists of the actual derived étale families. -/
def etalePrecoverage (Q : AlgebraReplacementFunctor k) :
    Precoverage (CofibrantAlgebra k)ᵒᵖ where
  coverings A := {R | IsEtaleCover Q A.unop R}

/-- The actual Grothendieck topology generated by those families. -/
def etaleTopology (Q : AlgebraReplacementFunctor k) :
    GrothendieckTopology (CofibrantAlgebra k)ᵒᵖ :=
  (etalePrecoverage Q).toGrothendieck

/-- Native local boundary lifting, including every comparison after base change. -/
def IsLocalTrivialFibration (Q : AlgebraReplacementFunctor k)
    {U V : DerivedPrestack.{u, u + 1} k} (f : U.functor ⟶ V.functor) : Prop :=
  ∀ (A : CofibrantAlgebra k) (n : ℕ)
    (a : (SSet.boundary.{u + 1} n).toSSet ⟶ U.functor.obj A.obj)
    (b : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ V.functor.obj A.obj),
    a ≫ f.app A.obj = (SSet.boundary n).ι ≫ b →
      ∃ R : Presieve (op A), Sieve.generate R ∈ etaleTopology Q (op A) ∧
        ∀ (B : CofibrantAlgebra k) (g : op B ⟶ op A), R g →
          ∃ l : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ U.functor.obj B.obj,
            (SSet.boundary n).ι ≫ l = a ≫ U.functor.map g.unop.hom ∧
            l ≫ f.app B.obj = b ≫ V.functor.map g.unop.hom

/-- Actual derived stacks on the computed étale site; geometricity is separate. -/
structure DerivedStack (Q : AlgebraReplacementFunctor k)
    extends DerivedPrestack.{u, u + 1} k where
  fibrant : IsInjectivelyFibrant functor
  hyperdescent : ∀ (U V : DerivedPrestack.{u, u + 1} k)
    (f : U.functor ⟶ V.functor), IsLocalTrivialFibration Q f →
      WeakEquivalence (((mappingBifunctor k).map f.op).app functor)

/-- A genuine affine stack model with its actual weak augmentation. -/
structure AffineStackModel (Q : AlgebraReplacementFunctor k) (A : SAlg k) where
  stack : DerivedStack Q
  augmentation : affineMapping k Q A ⟶ stack.functor
  weak : ∀ T, WeakEquivalence (augmentation.app T)

/-- Affineness is comparison to an actual augmented derived affine. -/
def IsAffine (Q : AlgebraReplacementFunctor k) (F : DerivedStack Q) : Prop :=
  ∃ (A : SAlg k) (a : affineMapping k Q A ⟶ F.functor),
    ∀ T, WeakEquivalence (a.app T)

end MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
