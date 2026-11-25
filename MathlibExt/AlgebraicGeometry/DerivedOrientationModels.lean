/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
public import MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Actual O-orientation traces and coefficient-linear realization

The absolute trace is a closed degree -d cochain from actual
RHom(O_X,O_X) to the native coefficient unit. Its A-linear realizations
are homogeneous morphisms of actual coefficient DG modules. Scalar
extension is normalized in the coefficient-module Hom complex, so
forgetting A-linearity cannot conceal a different extension class.

All comparisons use the source-normalized enriched adjunction, the
actual global pullback and module augmentations. Nondegeneracy on
every actual perfect E is a separate orientation criterion below,
not a result supplied by generic QCoh models.
Reference: PTVV arXiv:1111.3209v4, §2.1, Definition 2.4, p.33.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedOrientationModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open CochainComplex.HomComplex
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

/-- Every actual closed homogeneous module map yields the same native cochain cocycle. -/
def moduleCocycle {R : Type u} [CommRing R] {C : DGCat R} (o : C)
    {P Z : RightModule R C} {n : ℤ} (f : DGHom R n P Z)
    (h : dgDifferential R n f = 0) : Cocycle (value C o P) (value C o Z) n := by
  apply Cocycle.mk (DGFunctor.dgApp R n (op o) f) (n + 1) rfl
  have hz := congrArg (fun a => DGFunctor.dgApp R (n + 1) (op o) a) h
  rw [DGFunctor.dgApp_dgDifferential, dgDifferential_linearHomComplex] at hz
  simpa only [map_zero] using hz

/-- The actual shifted cochain map of a closed degree-n coefficient-module morphism. -/
def moduleToShift {R : Type u} [CommRing R] {C : DGCat R} (o : C)
    {P Z : RightModule R C} {n : ℤ} (f : DGHom R n P Z)
    (h : dgDifferential R n f = 0) : value C o P ⟶ (value C o Z)⟦n⟧ :=
  Cocycle.equivHomShift.symm (moduleCocycle o f h)

variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} {M : AffineModuleFibration N S}
    {U : RegularUnitSystem M} {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k}
    {V : NerveLiftModel L} {X : Prestack k} (B : FamilyModel M U Q L V X)
    (G : QCohEnhancement M U X) (D : ScalarGlobalModels B G)

/-- The k-linear source trace fixes every A-linear trace class through actual scalar extension. -/
structure TraceSystem (d : ℤ) where
  absolute : Cocycle (globalHom G G.unit) (𝟙_ (Cochains (LargeScalar k))) (-d)
  source : DGHom (LargeScalar k) (-d) D.source.module
    (regularModule (scalarCategory (LargeScalar k)) PUnit.unit)
  source_closed : dgDifferential (LargeScalar k) (-d) source = 0
  source_normalized : ∀ (n : ℤ)
    (m : (value (scalarCategory (LargeScalar k)) PUnit.unit D.source.module).X n),
    mapValue (scalarCategory (LargeScalar k)) PUnit.unit (p := n) (q := n - d)
      source (by omega) m =
      ((absolute : Cochain (globalHom G G.unit)
        (𝟙_ (Cochains (LargeScalar k))) (-d)).v n (n - d) (by omega)).hom
        (((cochainValueIso D.scalarUnit (globalHom G G.unit) D.evaluation).hom.f n).hom
          (((moduleComponent D.source.augmentation (op PUnit.unit)).f n).hom m))
  trace : ∀ A : SAlg k, DGHom (LargeScalar k) (-d) (D.target A).module
    (regularModule (coefficientLarge L N A) (coefficientObject L N A))
  closed : ∀ A : SAlg k, dgDifferential (LargeScalar k) (-d) (trace A) = 0
  scalar_normalized : ∀ A : SAlg k,
    ∃ h : DGHom (LargeScalar k) (-d - 1)
      ((D.extension A).functor.obj ⟨D.source.module, D.source.cofibrant⟩).obj
      (regularModule (coefficientLarge L N A) (coefficientObject L N A)),
    castDeg (LargeScalar k) (show (-d - 1) + 1 = -d by omega)
        (dgDifferential (LargeScalar k) (-d - 1) h) =
      dgComp (LargeScalar k) (D.baseChange A).map (trace A) (zero_add (-d)) -
        dgComp (LargeScalar k)
          (C := RightModule (LargeScalar k) (coefficientLarge L N A))
          (X := ((D.extension A).functor.obj ⟨D.source.module, D.source.cofibrant⟩).obj)
          (Y := ((D.extension A).functor.obj
            ⟨regularModule (scalarCategory (LargeScalar k)) PUnit.unit, D.regular⟩).obj)
          (Z := regularModule (coefficientLarge L N A) (coefficientObject L N A))
          ((D.extension A).functor.dgMap (-d)
            (X := ⟨D.source.module, D.source.cofibrant⟩)
            (Y := ⟨regularModule (scalarCategory (LargeScalar k)) PUnit.unit, D.regular⟩) source)
          (D.regularExtension A).map (add_zero (-d))

/-- The actual scalar extension comparison is a quasi-isomorphism of
coefficient modules. Arbitrary normalized base-change maps do not imply this. -/
def IsScalarBaseChange : Prop :=
  ∀ (A : SAlg k) (x : (coefficientLarge L N A)ᵒᵖ),
    QuasiIso (moduleComponent
      (closedModuleMap (D.baseChange A).map (D.baseChange A).closed) x)

/-- The source trace is the actual morphism RΓ(X,O_X)→k[-d]. -/
def absoluteTrace {d : ℤ} (T : TraceSystem B G D d) :
    globalHom G G.unit ⟶ (𝟙_ (Cochains (LargeScalar k)))⟦-d⟧ := Cocycle.equivHomShift.symm T.absolute

/-- Every A-trace is the corresponding actual shifted coefficient-module cochain map. -/
def coefficientTrace {d : ℤ} (T : TraceSystem B G D d) (A : SAlg k) :
    value (coefficientLarge L N A) (coefficientObject L N A) (D.target A).module ⟶
      (value (coefficientLarge L N A) (coefficientObject L N A)
        (regularModule (coefficientLarge L N A) (coefficientObject L N A)))⟦-d⟧ :=
  moduleToShift (coefficientObject L N A) (T.trace A) (T.closed A)

/-- The same actual global/coefficient tensor and dual models are used throughout the orientation. -/
structure OrientationContext where
  absolute : CoherentMonoidalEnhancement G
  family : ∀ A : SAlg k, CoherentMonoidalEnhancement (B.model A)
  tensor : ∀ A : SAlg k, DerivedTensorModel (coefficientLarge L N A) (coefficientObject L N A)
  opposite : ∀ A : SAlg k, OppositeModel (coefficientLarge L N A) (coefficientObject L N A)

/-- RΓ(E)⊗RΓ(E∨)→RΓ(O_XA) uses the actual global tensor/cup and dual evaluation. -/
def gammaPairing (C : OrientationContext B G) (A : SAlg k) {E : (B.model A).category}
    (P : PerfectDual (C.family A).monoidal E) :
    value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A E) ⊗
        value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A P.object) ⟶
      value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A (B.model A).unit) :=
  ((gammaValueIso B A E).hom ⊗ₘ (gammaValueIso B A P.object).hom) ≫
    sectionPairing (C.family A).monoidal P ≫ (gammaValueIso B A (B.model A).unit).inv

/-- The actual cochain pairing of the two chosen coefficient replacements. -/
def replacementPairing (C : OrientationContext B G) (A : SAlg k)
    {E : (B.model A).category} (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S' : ModuleReplacement (gamma B A P.object)) :
    value (coefficientLarge L N A) (coefficientObject L N A) R.module ⊗
      value (coefficientLarge L N A) (coefficientObject L N A) S'.module ⟶
        value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A (B.model A).unit) :=
  (moduleComponent R.augmentation (op (coefficientObject L N A)) ⊗ₘ
    moduleComponent S'.augmentation (op (coefficientObject L N A))) ≫ gammaPairing B G C A P

/-- Descent of the computed pairing to the actual balanced coefficient tensor.
This is a source linearity condition, distinct from nondegeneracy. -/
def IsBalancedCoefficientPairing (C : OrientationContext B G) (A : SAlg k)
    {E : (B.model A).category} (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S' : ModuleReplacement (gamma B A P.object)) : Prop :=
  relationLeft (coefficientLarge L N A) (coefficientObject L N A)
      (N := S'.module) ((C.tensor A).action R.module) ≫ replacementPairing B G C A P R S' =
    relationRight (coefficientLarge L N A) (coefficientObject L N A)
      (M := R.module) ((C.tensor A).action S'.module) ≫ replacementPairing B G C A P R S'

/-- A homogeneous tensor vector is the actual balanced quotient generator of the same replacements. -/
def tensorRepresentative (C : OrientationContext B G) (A : SAlg k)
    {E F : (B.model A).category} (P : ModuleReplacement (gamma B A E))
    (Q : ModuleReplacement (gamma B A F)) {p q n : ℤ} (h : p + q = n)
    (m : (value (coefficientLarge L N A) (coefficientObject L N A) P.module).X p)
    (v : (value (coefficientLarge L N A) (coefficientObject L N A) Q.module).X q) :
    (value (coefficientLarge L N A) (coefficientObject L N A)
      ((C.tensor A).functor.obj (⟨P.module, P.cofibrant⟩, ⟨Q.module, Q.cofibrant⟩)).obj).X n :=
  (((C.tensor A).value ⟨P.module, P.cofibrant⟩ ⟨Q.module, Q.cofibrant⟩).comparison.inv.f n).hom
    (generator (coefficientLarge L N A) (coefficientObject L N A)
      ((C.tensor A).action P.module) ((C.tensor A).action Q.module) h m v)

/-- The coefficient pairing is the actual global pairing lifted through the fixed unit augmentation. -/
structure CoefficientPairingModel (C : OrientationContext B G) (A : SAlg k)
    {E : (B.model A).category} (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S : ModuleReplacement (gamma B A P.object)) where
  map : DGHom (LargeScalar k) 0
    ((C.tensor A).functor.obj (⟨R.module, R.cofibrant⟩, ⟨S.module, S.cofibrant⟩)).obj
    (D.target A).module
  closed : dgDifferential (LargeScalar k) 0 map = 0
  normalized : ∀ (p q n : ℤ) (h : p + q = n)
    (m : (value (coefficientLarge L N A) (coefficientObject L N A) R.module).X p)
    (v : (value (coefficientLarge L N A) (coefficientObject L N A) S.module).X q),
    (((moduleComponent (D.target A).augmentation (op (coefficientObject L N A))).f n).hom
      (mapValue (coefficientLarge L N A) (coefficientObject L N A) map (add_zero n)
        (tensorRepresentative B G C A R S h m v))) =
    (((HomologicalComplex.ιTensorObj
      (value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A E))
      (value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A P.object)) p q n h) ≫
        (gammaPairing B G C A P).f n).hom
      (TensorProduct.tmul (LargeScalar k)
        (((moduleComponent R.augmentation (op (coefficientObject L N A))).f p).hom m)
        (((moduleComponent S.augmentation (op (coefficientObject L N A))).f q).hom v)))

/-- The adjoint is fixed on every actual vector and actual coefficient-linear dual functional. -/
structure OrientationAdjointModel {d : ℤ} (T : TraceSystem B G D d)
    (C : OrientationContext B G) (A : SAlg k) {E : (B.model A).category}
    (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S : ModuleReplacement (gamma B A P.object))
    (K : CoefficientPairingModel B G D C A P R S) where
  map : DGHom (LargeScalar k) (-d) R.module
    (derivedDual (coefficientLarge L N A) (coefficientObject L N A) (C.opposite A) S)
  closed : dgDifferential (LargeScalar k) (-d) map = 0
  normalized : ∀ (p q n : ℤ) (h : p + q = n)
    (m : (value (coefficientLarge L N A) (coefficientObject L N A) R.module).X p)
    (v : (value (coefficientLarge L N A) (coefficientObject L N A) S.module).X q),
    mapValue (coefficientLarge L N A) (coefficientObject L N A)
      ((((dualValueIso (coefficientLarge L N A) (coefficientObject L N A)
        (C.opposite A) S.module).hom).f (p - d)).hom
        (mapValue (coefficientLarge L N A) (coefficientObject L N A)
          (p := p) (q := p - d) map (by omega) m)) (show q + (p - d) = n - d by omega) v =
      mapValue (coefficientLarge L N A) (coefficientObject L N A)
        (p := n) (q := n - d) (T.trace A) (by omega)
        (mapValue (coefficientLarge L N A) (coefficientObject L N A)
          K.map (add_zero n) (tensorRepresentative B G C A R S h m v))

/-- The actual coefficient-linear adjoint is realized in the native target shift -d. -/
def adjointToShift {d : ℤ} {T : TraceSystem B G D d} {C : OrientationContext B G}
    {A : SAlg k} {E : (B.model A).category} {P : PerfectDual (C.family A).monoidal E}
    {R : ModuleReplacement (gamma B A E)} {S : ModuleReplacement (gamma B A P.object)}
    {K : CoefficientPairingModel B G D C A P R S}
    (J : OrientationAdjointModel B G D T C A P R S K) :
    value (coefficientLarge L N A) (coefficientObject L N A) R.module ⟶
      (value (coefficientLarge L N A) (coefficientObject L N A)
        (derivedDual (coefficientLarge L N A) (coefficientObject L N A) (C.opposite A) S))⟦-d⟧ :=
  moduleToShift (coefficientObject L N A) J.map J.closed

/-- PTVV orientation (Definition 2.4): `X` is O-compact, the scalar extension comparisons are
quasi-isomorphisms (`IsScalarBaseChange`), so that each `A`-linear trace is determined up to
homotopy by the absolute trace through `TraceSystem.scalar_normalized`, and the adjoint of the
trace pairing is a quasi-isomorphism for every `A` and every perfect `E`. -/
def IsOOrientation {d : ℤ} (T : TraceSystem B G D d) (C : OrientationContext B G) : Prop :=
  IsOCompact B ∧ IsScalarBaseChange B G D ∧
    ∀ (A : SAlg k) (E : (B.model A).category), IsPerfect (B.model A) E →
      ∃ (P : PerfectDual (C.family A).monoidal E)
        (R : ModuleReplacement (gamma B A E)) (S : ModuleReplacement (gamma B A P.object))
        (K : CoefficientPairingModel B G D C A P R S)
        (J : OrientationAdjointModel B G D T C A P R S K),
        QuasiIso (adjointToShift B G D J)

end MathlibExt.AlgebraicGeometry.DerivedOrientationModels
