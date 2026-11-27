/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# O-compactness on actual base-changed QCoh and coefficient modules

Every coefficient algebra A is retained, including its nilpotent and
simplicial directions. X_A is the literal derived affine product. Its
QCoh category is the actual cocartesian section category and its
coefficient RΓ(E) is the restricted enriched representable module
RHom(O_XA,E), with all A-action maps retained.

The structure object is compact in the actual stable DG homotopy
category when its Hom functor preserves all small coproducts. Together
with the genuine coproduct models this is the standard stable-category
compactness criterion. Perfection is tested for every actual perfect
E, using the native localized finite-cell retraction predicate on the
resulting A-module. Testing only O_XA is not O-compactness.

Reference: PTVV arXiv:1111.3209v4, §2.1, Definition 2.1 and Remark 2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCompactOrientations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The actual product projection preserves every affine and every simplex. -/
def productProjection (X Y : Prestack k) : X ⊗ Y ⟶ X where
  app A :=
    { app n := ↾fun a => a.1
      naturality _ _ _ := rfl }
  naturality _ _ _ := by ext n a; rfl

/-- The source's actual derived base change X×Spec(A). -/
def baseChanged (Q : AlgebraReplacementFunctor k) (X : Prestack k) (A : SAlg k) : Prestack k :=
  affineMapping k Q A ⊗ X

/-- Every coefficient arrow gives its literal affine-product base-change map. -/
def baseChangeMap (Q : AlgebraReplacementFunctor k) (X : Prestack k)
    {A B : SAlg k} (f : A ⟶ B) : baseChanged Q X B ⟶ baseChanged Q X A :=
  (affineYoneda k Q).map f.op ⊗ₘ 𝟙 X

variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k)

/-- A full source-normalized family of actual QCoh/RΓ presentations over every A. -/
structure FamilyModel where
  model : ∀ A : SAlg k, QCohEnhancement M U (baseChanged Q X A)
  affine : ∀ A : SAlg k, AffineQCohNormalization M U Q A
  scalar : ∀ A : SAlg k, CoefficientRealization (model A) L A Q
    (productProjection (affineMapping k Q A) X) V (affine A)
  coproducts : ∀ A : SAlg k,
    HasCoproducts.{u} (DGHomotopyCategory (LargeScalar k) (model A).category)
  pullback : ∀ (A B : SAlg k) (_f : A ⟶ B), (model A).category ⟶ (model B).category
  pullback_normalized : ∀ (A B : SAlg k) (f : A ⟶ B),
    (categoricalQ.{u}).map (dgNerveMap (pullback A B f) ≫ (model B).realization) =
      (categoricalQ.{u}).map
        ((model A).realization ≫ qcohPullback M (baseChangeMap Q X f))
  unit_eq : ∀ (A B : SAlg k) (f : A ⟶ B),
    (pullback A B f).obj (model A).unit = (model B).unit
  coefficient_natural : ∀ (A B : SAlg k) (f : A ⟶ B),
    (scalar A).functor.comp (Cochains (LargeScalar k)) (pullback A B f) =
      (coefficientLargeMap L N f).comp (Cochains (LargeScalar k)) (scalar B).functor

variable {M U Q L V X}

/-- The coefficient global sections module is the actual restricted representable. -/
def gamma (B : FamilyModel M U Q L V X) (A : SAlg k) (E : (B.model A).category) :
    RightModule (LargeScalar k) (coefficientLarge L N A) := globalModule (B.scalar A) E

/-- Coefficient-module values are the same actual global Hom complexes. -/
def gammaValueIso (B : FamilyModel M U Q L V X) (A : SAlg k) (E : (B.model A).category) :
    DerivedCoefficientTensorModels.value (coefficientLarge L N A) (coefficientObject L N A)
        (gamma B A E) ≅ globalHom (B.model A) E :=
  eqToIso (by
    dsimp only [DerivedCoefficientTensorModels.value, gamma, globalModule,
      EnrichedFunctor.comp, EnrichedFunctor.op, globalHom, coefficientObject]
    rw [(B.scalar A).unit_value]
    rfl)

/-- The unit base-change cochain map is the actual DG pullback on global Hom. -/
def unitHomBaseChange (B : FamilyModel M U Q L V X) {A A' : SAlg k} (f : A ⟶ A') :
    globalHom (B.model A) (B.model A).unit ⟶ globalHom (B.model A') (B.model A').unit :=
  (B.pullback A A' f).map (B.model A).unit (B.model A).unit ≫
    eqToHom (by rw [B.unit_eq A A' f]; rfl)

/-- General RΓ base change uses the same actual DG pullback and fixed structure unit. -/
def globalHomBaseChange (B : FamilyModel M U Q L V X) {A A' : SAlg k} (f : A ⟶ A')
    (E : (B.model A).category) : globalHom (B.model A) E ⟶
      globalHom (B.model A') ((B.pullback A A' f).obj E) :=
  (B.pullback A A' f).map (B.model A).unit E ≫
    eqToHom (by rw [B.unit_eq A A' f]; rfl)

/-- The coefficient-module presentation retains this actual RΓ base-change arrow. -/
def gammaBaseChange (B : FamilyModel M U Q L V X) {A A' : SAlg k} (f : A ⟶ A')
    (E : (B.model A).category) :
    DerivedCoefficientTensorModels.value (coefficientLarge L N A) (coefficientObject L N A)
        (gamma B A E) ⟶
      DerivedCoefficientTensorModels.value (coefficientLarge L N A') (coefficientObject L N A')
        (gamma B A' ((B.pullback A A' f).obj E)) :=
  (gammaValueIso B A E).hom ≫ globalHomBaseChange B f E ≫
    (gammaValueIso B A' ((B.pullback A A' f).obj E)).inv

/-- The same actual unit base-change map retains the coefficient module values. -/
def gammaUnitBaseChange (B : FamilyModel M U Q L V X) {A A' : SAlg k} (f : A ⟶ A') :
    DerivedCoefficientTensorModels.value (coefficientLarge L N A) (coefficientObject L N A)
        (gamma B A (B.model A).unit) ⟶
      DerivedCoefficientTensorModels.value (coefficientLarge L N A') (coefficientObject L N A')
        (gamma B A' (B.model A').unit) :=
  (gammaValueIso B A (B.model A).unit).hom ≫ unitHomBaseChange B f ≫
    (gammaValueIso B A' (B.model A').unit).inv

/-- Compactness uses the actual Hom(O_XA,-) and actual coproduct diagrams. -/
def IsCompactAt (B : FamilyModel M U Q L V X) (A : SAlg k) : Prop :=
  letI := B.coproducts A
  ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
    (coyoneda.obj (op (DGHomotopyCategory.of (LargeScalar k) (B.model A).unit)))

/-- PTVV O-compactness quantifies every base algebra and every genuine perfect object. -/
def IsOCompact (B : FamilyModel M U Q L V X) : Prop :=
  (∀ A : SAlg k, IsCompactAt B A) ∧
    ∀ (A : SAlg k) (E : (B.model A).category),
      IsPerfect (B.model A) E → IsPerfectModule (coefficientLarge L N A) (gamma B A E)

end MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
