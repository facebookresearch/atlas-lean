/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BirationalDualityReferences
public import MathlibExt.AlgebraicGeometry.ModuleDerivedSquares

/-!
# Quasi-coherent derived direct images and proper dualizing references

The functor is the fixed native Rf_* restricted to its actual quasi-coherent
derived subcategories. Preservation is a proof on those fixed objects.
The proper dualizing object is the right adjoint of that actual functor,
applied to the actual quasi-coherent structure unit.

For nonproper varieties, canonical modules are obtained by restriction from
an actual proper compactification. A right adjoint to nonproper RΓ is f×
and is not silently identified with a canonical f! object.

Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/Duality/FiniteTwistedTrace.lean and
Cotangent/SchemeCotangentComplex.lean; Stacks derived quasi-coherent
duality and Nagata compactification. Generic constructors are completed
source integration, with their native normalization inputs explicit.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPushforwards.{0}]

/-- The condition on a morphism of schemes $f : X \to Y$ that the derived direct image preserves
quasi-coherence: for every complex $M$ in the derived category of $\mathcal{O}_X$-modules with
quasi-coherent cohomology sheaves, $Rf_* M$ has quasi-coherent cohomology sheaves (for the derived
direct images given by `HasDerivedPushforwards`). -/
structure DirectImagePreservation {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop where
  preservation : ∀ M : QCohDerived X,
    quasicoherent Y ((derivedPushforward f).obj M.obj)

/-- The actual quasi-coherent derived direct-image functor. -/
def directImage {X Y : Scheme.{0}} (f : X ⟶ Y) (P : DirectImagePreservation f) :
    QCohDerived X ⥤ QCohDerived Y where
  obj M := ⟨(derivedPushforward f).obj M.obj, P.preservation M⟩
  map a := ObjectProperty.homMk ((derivedPushforward f).map a.hom)
  map_id M := by
    apply ObjectProperty.hom_ext
    exact (derivedPushforward f).map_id M.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (derivedPushforward f).map_comp a.hom b.hom

/-- The actual structure unit in the actual quasi-coherent derived subcategory. -/
def unit (X : Scheme.{0}) (h : quasicoherent X (derivedUnit X)) : QCohDerived X :=
  ⟨derivedUnit X, h⟩

/-- Proper-source dualizing reference; the proper guard is explicit and intrinsic to its type. -/
structure ProperReference {X Y : Scheme.{0}} (f : X ⟶ Y) where
  [proper : IsProper f]
  preservation : DirectImagePreservation f
  [adjoint : (directImage f preservation).IsLeftAdjoint]
  unitProof : quasicoherent Y (derivedUnit Y)

/-- Actual proper f!O as the fixed quasi-coherent right adjoint. -/
def properDuality {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f) : D X := by
  letI := P.adjoint
  exact ((directImage f P.preservation).rightAdjoint.obj (unit Y P.unitProof)).obj

/-- Actual proper trace, with its chosen adjunction and no free functional. -/
def properTrace {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f) :
    (derivedPushforward f).obj (properDuality P) ⟶ derivedUnit Y := by
  letI := P.adjoint
  exact ((Adjunction.ofIsLeftAdjoint (directImage f P.preservation)).counit.app
    (unit Y P.unitProof)).hom

/-- H^(-n) of the proper dualizing object, in the native module category. -/
def properCanonicalModule {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f)
    (n : ℕ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj (properDuality P)

/-- The proper QCoh duality base-change arrow is the actual adjunction transpose
of the fixed native base-change inverse and the fixed proper trace. -/
def properBaseChange [HasDerivedPullbacks.{0}] {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (P : ProperReference f) (P' : ProperReference f')
    (AF : ModuleDerivedSquares.PullPushAdjunction f)
    (AF' : ModuleDerivedSquares.PullPushAdjunction f')
    (A : ModuleDerivedSquares.PullbackPasting f' g)
    (B : ModuleDerivedSquares.PullbackPasting p f) (U : ModuleDerivedSquares.UnitPullback g)
    (hL : quasicoherent X' ((derivedPullback p).obj (properDuality P)))
    (hbase : IsIso (ModuleDerivedSquares.baseChangeMap p f' f g comm AF AF' A B
      (properDuality P))) :
    (derivedPullback p).obj (properDuality P) ⟶ properDuality P' := by
  letI := P'.adjoint
  letI := hbase
  let ρ : (derivedPushforward f').obj ((derivedPullback p).obj (properDuality P)) ⟶
      derivedUnit Y' :=
    inv (ModuleDerivedSquares.baseChangeMap p f' f g comm AF AF' A B (properDuality P)) ≫
      (derivedPullback g).map (properTrace P) ≫ U.comparison.hom
  let β := ((Adjunction.ofIsLeftAdjoint (directImage f' P'.preservation)).homEquiv
    (⟨(derivedPullback p).obj (properDuality P), hL⟩ : QCohDerived X')
    (unit Y' P'.unitProof)) (ObjectProperty.homMk ρ)
  exact β.hom

end MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
