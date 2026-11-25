/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientULiftTransport
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.NativeCoefficients

/-!
# Coefficient homology and Tor in independent universes

Universe lifts place Lie coefficients and their Chevalley–Eilenberg complexes in a common
module category while retaining the ground-ring action. Compatible Lie and coefficient maps
induce homology maps and canonical derived balanced-tensor maps.

When the underlying Lie modules are free over the commutative ground ring, the coefficient
homology-to-Tor comparisons are natural through these transports. Lie and coefficient carrier
universes may be independent.
-/

@[expose] public section

noncomputable section

universe u v v' w w' z a b

open CategoryTheory
open scoped ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex HomologicalComplex.homologyFunctor

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- The coefficient-carrier lift at a working universe containing both possible Lie and
coefficient carrier universes. -/
def rawLieCoefficientLiftAt (M : LieModuleCat.{w} R L) : LieModuleCat.{max u v v' w w' z} R L :=
  LieModuleCat.CoefficientULift.obj.{u, v, w, max u v v' w w' z} R L M

/-- Explicit lift of the homology input, transported to CE of the coefficient lift in the
sufficient working universe. -/
def rawCoefficientHomologyTransportAt (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ≅
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology n :=
  coefficientHomologyCoefficientLiftIso.{u, v, w, max u v v' w w' z} R L M n

/-- Linear input/output transport of the lower-universe homology carrier, without placing it
directly in a larger module category. -/
def rawCoefficientHomologyTransportEquivAt (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      (coefficientComplex R L (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)).homology n :=
  coefficientHomologyCoefficientLiftEquiv.{u, v, w, max u v v' w w' z} R L M n

local instance rawCoefficientTensor_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{a} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, v, a, b} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M

/-- The Tor object of the raw coefficient at the common working universe, with its explicit
coefficient-carrier lift. -/
def rawLieCoefficientTorAt (M : LieModuleCat.{w} R L) (n : ℕ) : (ModuleCat.{max u v v' w w' z} R) :=
  (((ModuleCat.BalancedTensor.functor R U
    (LieModuleCat.RightUniversalEnveloping.representObj R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)) :
        ModuleCat.{max u v v' w w' z} U ⥤ (ModuleCat.{max u v v' w w' z} R)).leftDerived n).obj
          (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L))

/-- The categorical CE/Tor comparison on the lift of the raw homology object, using the exact CE
lift comparison. -/
def rawCoefficientHomologyIsoTorAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ≅
      rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n :=
  rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M n ≪≫
    nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n

/-- Categorical output transport to the lift of the raw homology object. -/
def rawCoefficientTorIsoHomologyAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ≅
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
        ((coefficientComplex R L M).homology n) :=
  (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).symm

/-- The exact raw homology carrier computes Tor through input up and the categorical comparison. -/
def rawCoefficientHomologyEquivTorAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientComplex R L M).homology n ≃ₗ[R]
      rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n :=
  (coefficientHomologyCarrierLiftEquiv.{u, v, w, max u v v' w w' z} R L M n).trans
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).toLinearEquiv

@[simp]
theorem rawCoefficientHomologyEquivTorAt_apply [Module.Free R L]
    (M : LieModuleCat.{w} R L) (n : ℕ) (a : (coefficientComplex R L M).homology n) :
    rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n a =
      (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom (ULift.up a) := rfl

/-- Tor output down returns to the exact lower-universe homology carrier by the inverse
independent-universe linear equivalence. -/
def rawCoefficientTorEquivHomologyAt [Module.Free R L] (M : LieModuleCat.{w} R L) (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ≃ₗ[R]
      (coefficientComplex R L M).homology n :=
  (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n).symm

/-- The raw-carrier degree-zero input transport retains the canonical lifted coefficient
coinvariant/unit comparison. -/
theorem rawCoefficientHomologyIsoTorAt_zero_canonical [Module.Free R L]
    (M : LieModuleCat.{w} R L) :
    let M₁ := rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M
    let N₁ := LieModuleCat.RightUniversalEnveloping.representObj R L M₁
    let F := (ModuleCat.BalancedTensor.functor R U N₁ :
      ModuleCat.{max u v v' w w' z} U ⥤ (ModuleCat.{max u v v' w w' z} R))
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom ≫
      F.fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w w' z} R L) ≫
        (rightTrivialTensorLiftEquiv.{u, v, v', max w w' z} R L N₁).toModuleIso.hom =
      (rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0).hom ≫
        (nativeCoefficientHomologyZeroTensorIso.{u, v, v', max w w' z} R L M₁).hom := by
  dsimp only
  let t := rawCoefficientHomologyTransportAt.{u, v, v', w, w', z} R L M 0
  let e := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) 0
  have he : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M 0).hom =
      t.hom ≫ e.hom := rfl
  have h := nativeCoefficientHomologyIsoTor_zero_canonical.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
  exact (congrArg (fun q => q ≫ _ ≫ _) he).trans
    ((Category.assoc _ _ _).trans (congrArg (fun q => t.hom ≫ q) h))

section JointMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L')
  (M : LieModuleCat.{w} R L) (M' : LieModuleCat.{w'} R L')
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- The coefficient map on the two independent coefficient lifts, at the same maximum working
universe. -/
def rawLieCoefficientMapAt :
    rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M →ₗ⁅R,L⁆
      LieModuleCat.restrictObj f (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') :=
  LieModuleCat.CoefficientULift.jointMap.{u, v, w, w', v', max u v v' w w' z} R L f M M' h

@[simp]
theorem rawLieCoefficientMapAt_up (m : M) :
    rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h (ULift.up m) = ULift.up (h m) := rfl

/-- The carrier-universe CE homology map, transported only by the Chevalley–Eilenberg
whole-complex maps and homology up/down comparisons. -/
def rawCoefficientHomologyMapAt (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v w} R).obj
      ((coefficientComplex R L M).homology n) ⟶
    (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
      ((coefficientComplex R L' M').homology n) :=
  coefficientRawHomologyMapAt.{u, v, w, z, v', w'} R L f M M' h n

/-- Raw CE homology map with the independently sized source and target carriers; its definition
uses only CE maps and lifts. -/
def rawOriginalCoefficientHomologyMapAt (n : ℕ) :
    (coefficientComplex R L M).homology n →ₗ[R] (coefficientComplex R L' M').homology n :=
  coefficientOriginalHomologyMapAt.{u, v, w, z, v', w'} R L f M M' h n

/-- The canonical Tor map comes from the independently defined derived scalar-change square on the
lifted coefficient data. -/
def rawLieCoefficientTorMapAt (n : ℕ) :
    rawLieCoefficientTorAt.{u, v, v', w, w', z} R L M n ⟶
      rawLieCoefficientTorAt.{u, v', v, w', w, z} R L' M' n :=
  nativeLieCoefficientTorMap.{u, v, v', max w w' z} R L f
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')
    (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h) n

/-- Full raw-carrier joint naturality: both coefficient carrier universes remain independent and
both sides use their carrier transports. -/
theorem rawCoefficientHomologyIsoTorAt_naturality [Module.Free R L] [Module.Free R L'] (n : ℕ) :
    rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n ≫
      (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom =
    (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom ≫
      rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n := by
  let A := coefficientHomologyULiftIso.{u, v, w, max u v v' w w' z} R L M n
  let A' := coefficientHomologyULiftIso.{u, v', w', max u v v' w w' z} R L' M' n
  let e := coefficientULiftComplexIso.{u, v, w, max u v v' w w' z} R L M
  let e' := coefficientULiftComplexIso.{u, v', w', max u v v' w w' z} R L' M'
  let a := coefficientLieComplexMapULiftAt.{u, v, w, z, v', w'} R L f M M' h
  let b := nativeCoefficientLieComplexMap.{u, v, v', max w w' z} R L f
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h)
  have hC : a ≫ e'.hom = e.hom ≫ b :=
    coefficientULiftComplexIso_joint_naturality.{u, v, w, z, v', w'} R L f M M' h
  have hH : HomologicalComplex.homologyMap a n ≫ HomologicalComplex.homologyMap e'.hom n =
      HomologicalComplex.homologyMap e.hom n ≫ HomologicalComplex.homologyMap b n := by
    exact (HomologicalComplex.homologyMap_comp a e'.hom n).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f n) hC).trans
        (HomologicalComplex.homologyMap_comp e.hom b n))
  let T := nativeCoefficientHomologyIsoTor.{u, v, v', max w w' z} R L
    (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M) n
  let T' := nativeCoefficientHomologyIsoTor.{u, v', v, max w w' z} R L'
    (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M') n
  have hSource : (rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom =
      A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ T.hom := rfl
  have hTarget : (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom =
      A'.hom ≫ HomologicalComplex.homologyMap e'.hom n ≫ T'.hom := rfl
  have hMap : rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n =
      A.hom ≫ HomologicalComplex.homologyMap a n ≫ A'.inv := rfl
  have hNat : HomologicalComplex.homologyMap b n ≫ T'.hom =
      T.hom ≫ rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n :=
    nativeCoefficientHomologyIsoTor_lie_naturality.{u, v, v', max w w' z} R L f
      (rawLieCoefficientLiftAt.{u, v, v', w, w', z} R L M)
      (rawLieCoefficientLiftAt.{u, v', v, w', w, z} R L' M')
      (rawLieCoefficientMapAt.{u, v, v', w, w', z} R L f M M' h) n
  have cancel {W X Y Z V : ModuleCat.{max u v v' w w' z} R}
      (f : W ⟶ X) (g : X ⟶ Y) (e : Z ≅ Y) (h : Y ⟶ V) :
      (f ≫ g ≫ e.inv) ≫ (e.hom ≫ h) = f ≫ g ≫ h := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hCalc :
      (A.hom ≫ HomologicalComplex.homologyMap a n ≫ A'.inv) ≫
          (A'.hom ≫ HomologicalComplex.homologyMap e'.hom n ≫ T'.hom) =
        (A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ T.hom) ≫
          rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n := by
    calc
      _ = A.hom ≫ HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap e'.hom n ≫ T'.hom := cancel _ _ _ _
      _ = A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫
          HomologicalComplex.homologyMap b n ≫ T'.hom := by
        exact congrArg (fun q => A.hom ≫ q ≫ T'.hom) hH
      _ = _ := by
        exact (congrArg (fun q => A.hom ≫ HomologicalComplex.homologyMap e.hom n ≫ q) hNat).trans
          (Category.assoc _ _ _).symm
  exact (congrArg₂ (fun f g => f ≫ g) hMap hTarget).trans
    (hCalc.trans (congrArg (fun q => q ≫
      rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n) hSource).symm)

/-- Full raw-carrier joint naturality as an equality of ground-linear maps across independent raw
coefficient/homology universes. -/
theorem rawCoefficientHomologyEquivTorAt_naturality [Module.Free R L] [Module.Free R L'] (n : ℕ) :
    (rawCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' M' n).toLinearMap.comp
      (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom.comp
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n).toLinearMap := by
  ext a
  have hNat := congrArg
    (fun f => f.hom (ULift.up a)) (rawCoefficientHomologyIsoTorAt_naturality.{u, v, v', w, w', z} R L f M M' h n)
  change (rawCoefficientHomologyIsoTorAt.{u, v', v, w', w, z} R L' M' n).hom
      ((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a)) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom
      ((rawCoefficientHomologyIsoTorAt.{u, v, v', w, w', z} R L M n).hom (ULift.up a)) at hNat
  have hUp : (ULift.up (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n a) :
      (ModuleCat.uliftFunctor.{max u v v' w w' z, max u v' w'} R).obj
        ((coefficientComplex R L' M').homology n)) =
      (rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a) := by
    change ULift.up (((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a)).down) = _
    cases ((rawCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n).hom (ULift.up a))
    rfl
  change rawCoefficientHomologyEquivTorAt.{u, v', v, w', w, z} R L' M' n
      (rawOriginalCoefficientHomologyMapAt.{u, v, v', w, w', z} R L f M M' h n a) =
    (rawLieCoefficientTorMapAt.{u, v, v', w, w', z} R L f M M' h n).hom
      (rawCoefficientHomologyEquivTorAt.{u, v, v', w, w', z} R L M n a)
  rw [rawCoefficientHomologyEquivTorAt_apply, rawCoefficientHomologyEquivTorAt_apply, hUp]
  exact hNat

end JointMaps

end ChevalleyEilenberg
