/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Topology.Algebra.Ring.Ideal
public import MathlibExt.Condensed.LocalSolidCoefficientModels
public import MathlibExt.CategoryTheory.CategoricalCoefficientLimits

/-!
# Actual torsion solid coefficients and linearized Frobenius modules

The coefficient ring is the actual A^+/pi of the specified untilt.
Frobenius is its literal p-th-power ring map, including the zero-ring
boundary. The hypothesis pi divides p is retained. The almost ideal is
the image of the original topologically nilpotent ideal.

Local torsion coefficients use actual analytic/compact DG modules.
Frobenius extension retains the full scalar-changing Hom adjunction and
its unit. Linearized structures are closed degree-zero equivalences
from that actual extension. Their infinity-category model is the native
coherent-isomorphism path pullback, rather than a plain endomorphism.

Source: Mann, arXiv:2206.02022v1, Theorem 1.2.7, Definitions 3.9.10
and 3.9.15--3.9.21; Anschuetz--Mann, arXiv:2403.01951v2, Remark 4.5.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.SolidTorsionFrobeniusModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalClosed
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarNerveMaps
open MathlibExt.CategoryTheory.CategoricalCoefficientLimits
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open LocalSolidCoefficientModels GeometricScalarRestriction SolidAnalyticModules
open AdicSolidGenerators GeometricDGModules PerfectoidSolidCoefficientModels
open CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P)

/-- The actual torsion plus ring with its native quotient topology. -/
abbrev TorsionRing := ULift.{1} (P.pair.plus ⧸ Ideal.span {π.element})

/-- The actual integral coefficient reduction. -/
def reduction : Coefficient p P →+* TorsionRing p P π :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.mk (Ideal.span {π.element})).comp ULift.ringEquiv.toRingHom)

/-- The source pi-divides-p convention gives the actual characteristic-p residue condition. -/
theorem prime_zero (h : π.element ∣ (p : P.pair.plus)) : (p : TorsionRing p P π) = 0 := by
  apply ULift.ext
  change (p : P.pair.plus ⧸ Ideal.span {π.element}) = 0
  have hp : Ideal.Quotient.mk (Ideal.span {π.element}) (p : P.pair.plus) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
  simpa only [map_natCast] using hp

/-- Literal residue Frobenius, including the zero-ring boundary. -/
@[irreducible]
def residueFrobenius (R : Type 1) [CommRing R] (hp : (p : R) = 0) : R →+* R := by
  classical
  by_cases h0 : Subsingleton R
  · exact RingHom.id _
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp h0
    letI : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact frobenius R p

/-- Residue Frobenius retains the actual p-th power on every element. -/
theorem residueFrobenius_apply (R : Type 1) [CommRing R] (hp : (p : R) = 0)
    (a : R) : residueFrobenius p R hp a = a ^ p := by
  classical
  unfold residueFrobenius
  split
  · exact Subsingleton.elim _ _
  · rfl

/-- Literal Frobenius on the actual quotient, with no nonempty-space restriction. -/
def coefficientFrobenius (h : π.element ∣ (p : P.pair.plus)) :
    TorsionRing p P π →+* TorsionRing p P π :=
  residueFrobenius p (TorsionRing p P π) (prime_zero p P π h)

/-- Its every element is the original coefficient's actual p-th power. -/
theorem coefficientFrobenius_apply (h : π.element ∣ (p : P.pair.plus))
    (a : TorsionRing p P π) : coefficientFrobenius p P π h a = a ^ p := by
  exact residueFrobenius_apply p _ _ a

/-- Frobenius is continuous on the actual geometric quotient ring. -/
theorem continuous_coefficientFrobenius (h : π.element ∣ (p : P.pair.plus)) :
    Continuous (coefficientFrobenius p P π h) := by
  have e : (coefficientFrobenius p P π h : TorsionRing p P π → TorsionRing p P π) =
      (fun a ↦ a ^ p) :=
    funext (coefficientFrobenius_apply p P π h)
  rw [e]
  exact continuous_id.pow p

/-- The almost ideal comes from the actual original almost ideal by coefficient reduction. -/
def torsionAlmostIdeal (J : AlmostIdealData p P.pair) : Ideal (TorsionRing p P π) :=
  J.ideal.map (reduction p P π)

/-- Actual local torsion solid almost coefficients. -/
structure TorsionModel where
  restriction : RestrictionInput (TorsionRing p P π) ⊤
  analytic : AnalyticReflection (TorsionRing p P π) ⊤ restriction
  compact : CompactDGModel (TorsionRing p P π)
    (analyticGenerator (TorsionRing p P π) ⊤ restriction analytic)
  almost : AlmostIdealData p P.pair
  [analyticShift : analytic.functor.CommShift ℤ]
  [analyticUnitShift : NatTrans.CommShift analytic.unit ℤ]

attribute [instance] TorsionModel.analyticShift TorsionModel.analyticUnitShift

/-- The actual enhanced torsion almost module category. -/
abbrev TorsionCategory (M : TorsionModel p P π) :=
  AlmostModifiedModules (TorsionRing p P π) M.compact (torsionAlmostIdeal p P π M.almost)

/-- Actual infinity-category values retain full torsion DG mapping complexes. -/
def torsionNerve (M : TorsionModel p P π) : SSet.{2} :=
  integerNerve (R := TorsionRing p P π) (TorsionCategory p P π M)

section GeometricFrobenius

variable (h : π.element ∣ (p : P.pair.plus)) (M : TorsionModel p P π)
  [(GeometricTopologicalRestriction.restriction (coefficientFrobenius p P π h)
    (continuous_coefficientFrobenius p P π h)).IsRightAdjoint]
  [GeometricTopologicalRestriction.HasDerivedExtension (coefficientFrobenius p P π h)
    (continuous_coefficientFrobenius p P π h)]

/-- The geometric source is the native derived coefficient-Frobenius extension and analytic unit. -/
def geometricPhi : GeometricDerived (TorsionRing p P π) ⥤
    GeometricDerived (TorsionRing p P π) :=
  GeometricTopologicalRestriction.derivedExtension (coefficientFrobenius p P π h)
    (continuous_coefficientFrobenius p P π h) ⋙ M.analytic.functor

instance geometricPhi_shift
    [(GeometricTopologicalRestriction.derivedExtension (coefficientFrobenius p P π h)
      (continuous_coefficientFrobenius p P π h)).CommShift ℤ] :
    (geometricPhi p P π h M).CommShift ℤ :=
  inferInstanceAs ((GeometricTopologicalRestriction.derivedExtension
    (coefficientFrobenius p P π h) (continuous_coefficientFrobenius p P π h) ⋙
      M.analytic.functor).CommShift ℤ)

end GeometricFrobenius

/-- The actual geometric cochain realizing a torsion compact object. -/
abbrev torsionComplex (M : TorsionModel p P π) (x : M.compact.objects) :=
  (M.compact.realization.obj x).obj

/-- A scalar-Frobenius model is the full actual module adjunction on the fixed coefficient map. -/
structure FrobeniusModel (h : π.element ∣ (p : P.pair.plus)) (M : TorsionModel p P π) where
  compactFunctor : SemilinearFunctor (coefficientFrobenius p P π h)
    M.compact.objectsᵒᵖ M.compact.objectsᵒᵖ
  restriction : RestrictionModel (coefficientFrobenius p P π h) compactFunctor
  extension : ExtensionModel (coefficientFrobenius p P π h) restriction
  almost : ∀ N : DGDerivedModules (TorsionRing p P π) M.compact.objects,
    IsAlmostLocal (TorsionRing p P π) (torsionAlmostIdeal p P π M.almost) N.obj →
      IsAlmostLocal (TorsionRing p P π) (torsionAlmostIdeal p P π M.almost)
        (extension.functor.obj N).obj

/-- Geometric Frobenius normalization uses the fixed native source and all homogeneous classes. -/
def IsGeometricallyNormalized {h : π.element ∣ (p : P.pair.plus)}
    {M : TorsionModel p P π} (F : FrobeniusModel p P π h M) : Prop :=
  ∃ E : GeometricTopologicalRestriction.ShiftedExtensionModel (coefficientFrobenius p P π h)
      (continuous_coefficientFrobenius p P π h),
    let G := E.functor (coefficientFrobenius p P π h)
      (continuous_coefficientFrobenius p P π h) ⋙ M.analytic.functor
    ∃ e : ∀ x : M.compact.objects,
      G.obj (DerivedCategory.Q.obj (torsionComplex p P π M x)) ≅
        DerivedCategory.Q.obj (torsionComplex p P π M (F.compactFunctor.obj (op x)).unop),
      ∀ (x y : M.compact.objects) (n : ℤ)
        (a : DGHom (TorsionRing p P π) n x y) (_ha : dgDifferential (TorsionRing p P π) n a = 0)
        (b : Cocycle (torsionComplex p P π M x) (torsionComplex p P π M y) n)
        (c : Cocycle (torsionComplex p P π M (F.compactFunctor.obj (op x)).unop)
          (torsionComplex p P π M (F.compactFunctor.obj (op y)).unop) n),
        (b : Cochain _ _ n) = M.compact.realization.dgMap n a →
        (c : Cochain _ _ n) = M.compact.realization.dgMap n
          (((F.compactFunctor.map (op y) (op x)).f n) a) →
        G.map (cochainClass b) ≫
          (shiftedComparison G (torsionComplex p P π M y)
            (torsionComplex p P π M (F.compactFunctor.obj (op y)).unop) (e y) n).hom =
          (e x).hom ≫ cochainClass c

/-- The actual enhanced Frobenius scalar extension on almost-local modules. -/
def FrobeniusModel.localExtension {h : π.element ∣ (p : P.pair.plus)}
    {M : TorsionModel p P π} (F : FrobeniusModel p P π h M) :
    SemilinearFunctor (coefficientFrobenius p P π h)
      (TorsionCategory p P π M) (TorsionCategory p P π M) where
  obj N :=
    let N' : DGDerivedModules (TorsionRing p P π) M.compact.objects := ⟨N.obj, N.property.1⟩
    let K := F.extension.functor.obj N'
    ⟨K.obj, K.property, F.almost N' N.property.2⟩
  map K L := F.extension.functor.map ⟨K.obj, K.property.1⟩ ⟨L.obj, L.property.1⟩
  identity K := by
    simpa only [DGFullSubcategory.dgHomComplex_eq, DGFullSubcategory.dgId_eq] using
      F.extension.functor.identity ⟨K.obj, K.property.1⟩
  composition K L N i j k a b e := by
    simpa only [DGFullSubcategory.dgHomComplex_eq, DGFullSubcategory.dgComp_eq] using
      F.extension.functor.composition ⟨K.obj, K.property.1⟩ ⟨L.obj, L.property.1⟩
        ⟨N.obj, N.property.1⟩ i j k a b e

/-- Its actual endomorphism of the full coefficient coherent nerve. -/
def FrobeniusModel.nerveMap {h : π.element ∣ (p : P.pair.plus)}
    {M : TorsionModel p P π} (F : FrobeniusModel p P π h M) :
    torsionNerve p P π M ⟶ torsionNerve p P π M :=
  scalarNerveMap (coefficientFrobenius p P π h) (F.localExtension p P π)

/-- The actual categorical path object, consisting of coherent equivalences. -/
def equivalencePaths (X : SSet.{2}) : SSet.{2} := (ihom SSet.coherentIso.{2}).obj X

/-- Its two prescribed endpoint maps. -/
def pathEndpoint (X : SSet.{2}) (right : Bool) : equivalencePaths X ⟶ X :=
  (MonoidalClosed.pre (SSet.const
    (if right then SSet.coherentIso.x₁ else SSet.coherentIso.x₀))).app X ≫
      (MonoidalClosed.unitIsoSelf X).hom

/-- The actual homotopy equalizer encoding a linearized Frobenius equivalence. -/
def PhiModules {h : π.element ∣ (p : P.pair.plus)} {M : TorsionModel p P π}
    (F : FrobeniusModel p P π h M) : SSet.{2} :=
  pullback (prod.lift (F.nerveMap p P π) (𝟙 _))
    (prod.lift (pathEndpoint (torsionNerve p P π M) false)
      (pathEndpoint (torsionNerve p P π M) true))

end MathlibExt.Condensed.SolidTorsionFrobeniusModels
