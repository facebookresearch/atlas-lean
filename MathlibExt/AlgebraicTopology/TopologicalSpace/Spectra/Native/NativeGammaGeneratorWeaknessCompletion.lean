/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeakness
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.ActualFunctionIteration
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.GroupUnitCoherence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Original native Gamma integer representatives and assembly

The original free-sphere, scalar-power, integer-stage, unit-lift and
kernel maps are constructed on the canonical native carrier. The final
integer Gamma isomorphism assembly takes the literal original raw-left
and unit-lift evaluations and the original sphere-face homotopy as its
mathematical premises; the bare Gamma law is not asserted here.
-/

section ActualGammaRepresentatives


/-!
## Actual Gamma representatives in the original integer diagram

The actual free-pair inverse, representation sphere multiplication and original
source label equality identify a mixed free representative with a class at its
original later integer stage. All maps act on the original native orthogonal
carrier and retain its enriched actions and both original universes.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- The original mixed coefficient and original sum of free labels. -/
abbrev mixedFree (n r d : ℕ) : Actual.OrthogonalCarrier.{u, v} :=
  Free.object (OrthogonalOperatorIndex.ofIndex (n + r))
    (PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d)

/-- Both original degree equalities precede the actual representation sphere splitting. -/
def mixedCoefficientIso (n d : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} (d + n) ≅
      PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d :=
  eqToIso (congrArg PointedCGWH.orthogonalSphere (Nat.add_comm d n)) ≪≫
    PointedCGWH.orthogonalSphereTensorIso n d

/-- The unchanged free source retains its actual coefficient and target-label casts. -/
def mixedSourceIso (n r d : ℕ) :
    Free.object (OrthogonalOperatorIndex.ofIndex (r + n))
      (PointedCGWH.orthogonalSphere.{u, v} (d + n)) ≅ mixedFree.{u, v} n r d :=
  (Free.functor (OrthogonalOperatorIndex.ofIndex (r + n))).mapIso
      (mixedCoefficientIso n d) ≪≫
    eqToIso (congrArg (fun a => Free.object (OrthogonalOperatorIndex.ofIndex a)
      (PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d)) (Nat.add_comm r n))

/-- A source label and its sphere degree keep their original equality functions. -/
def freeSourceCast {a b c d : ℕ} (ha : a = b) (hc : c = d) :
    Free.object (OrthogonalOperatorIndex.ofIndex a) (PointedCGWH.orthogonalSphere.{u, v} c) ≅
      Free.object (OrthogonalOperatorIndex.ofIndex b) (PointedCGWH.orthogonalSphere.{u, v} d) := by
  cases ha
  cases hc
  exact Iso.refl _

/-- The exact later integer-stage free source retains both original arithmetic equalities. -/
def integerMixedSourceIso (q : ℤ) (t n : ℕ) :
    Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + (t + n) + 1)) ≅
        mixedFree.{u, v} n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) :=
  freeSourceCast (show integerTailLevel q + (t + n) = integerTailLevel q + t + n by omega)
    (show integerTailPositiveIndex q + (t + n) + 1 = integerTailPositiveIndex q + t + 1 + n by omega) ≪≫
    mixedSourceIso n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1)

section IntegerReadback

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The genuine mixed representative is read through the complete original native sphere correspondence. -/
def mixedIntegerClass (q : ℤ) (t n : ℕ) (X : Actual.OrthogonalCarrier.{u, v})
    (f : mixedFree.{u, v} n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    PointedCGWH.piN (integerTailPositiveIndex q + (t + n) + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))) :=
  (nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
    (integerTailPositiveIndex q + (t + n) + 1) X).symm
      ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map ((integerMixedSourceIso q t n).hom ≫
        f))

/-- Every original native target map retains both directions of the same free-sphere correspondence. -/
theorem nativeSphereClass_postcompose (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (g : X ⟶ Y)
    (f : Free.object a (PointedCGWH.orthogonalSphere.{u, v} d) ⟶ X) :
    (nativeSpherePiHomEquiv a d Y).symm ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (f
      ≫ g)) =
      PointedCGWH.piNMap d (component g a)
        ((nativeSpherePiHomEquiv a d X).symm ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u,
          v}).map f)) := by
  apply (nativeSpherePiHomEquiv a d Y).injective
  rw [Equiv.apply_symm_apply, nativeSpherePiHomEquiv_naturality, Equiv.apply_symm_apply, Functor.map_comp]

/-- Both original integer degrees and source label casts are natural under the same native target map. -/
theorem mixedIntegerClass_postcompose (q : ℤ) (t n : ℕ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (g : X ⟶ Y)
    (f : mixedFree.{u, v} n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    mixedIntegerClass q t n Y (f ≫ g) =
      PointedCGWH.piNMap (integerTailPositiveIndex q + (t + n) + 1)
        (component g (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))))
        (mixedIntegerClass q t n X f) := by
  simpa only [mixedIntegerClass, Category.assoc] using
    nativeSphereClass_postcompose
      (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
      (integerTailPositiveIndex q + (t + n) + 1) g ((integerMixedSourceIso q t n).hom ≫ f)

/-- The same original mixed free map is natural through the actual integer quotient leg. -/
theorem mixedIntegerLeg_postcompose (q : ℤ) (t n : ℕ)
    {X Y : Actual.OrthogonalCarrier.{u, v}} (g : X ⟶ Y)
    (f : mixedFree.{u, v} n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    ((integerPiFunctor q).map g).hom
      ((integerPiLeg q X (t + n)).hom (mixedIntegerClass q t n X f)) =
      (integerPiLeg q Y (t + n)).hom (mixedIntegerClass q t n Y (f ≫ g)) := by
  have h := ConcreteCategory.congr_hom (integerPiLeg_naturality_component q g (t + n))
    (mixedIntegerClass q t n X f)
  have hCube := PointedCGWH.piNPositiveMap_apply (integerTailPositiveIndex q + (t + n))
    (component g (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))))
    (mixedIntegerClass q t n X f)
  exact h.trans ((congrArg (integerPiLeg q Y (t + n)).hom hCube).trans
    (congrArg (integerPiLeg q Y (t + n)).hom (mixedIntegerClass_postcompose q t n g f).symm))

end IntegerReadback
end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

open CategoryTheory.Spectra.SpectrumIndexMaps CategoryTheory.Spectra.OrthogonalSourceRightModule
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Both original coefficient maps from ordered scalar spheres to native representation spheres. -/
def orderedCoefficientIso (n : ℕ) :
    TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} n ≅ PointedCGWH.orthogonalSphere.{u, v} n :=
  originalSymmetricOrthogonalCoefficientIso (Sequential.finiteIndex n)

/-- The actual mapped original target permutation at the same native dimension. -/
def orderedTargetIso (r n : ℕ) :
    ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex (r + n)) ≅
      ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex (r + n)) :=
  symmetricOrthogonalOperatorIndexFunctor.{u, v}.forget.mapIso (Sequential.orderedIndexIso r n)

section SourceWords
universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- Three complete source equations retain both Hom maps, the coefficient map and actual target action. -/
theorem sourceMapComposition {A H T J B K : C}
    (p : A ⟶ H) (sm : H ⟶ T) (tm : T ⟶ K) (ns : A ⟶ J)
    (ss : J ⟶ T) (mm : J ⟶ K) (c : A ⟶ B) (nn : B ⟶ K) (w : K ⟶ K)
    (hSource : p ≫ sm = ns ≫ ss) (hTarget : ss ≫ tm = mm ≫ w)
    (hCoefficient : ns ≫ mm = c ≫ nn) : p ≫ sm ≫ tm = c ≫ nn ≫ w := by
  calc
    _ = (p ≫ sm) ≫ tm := (Category.assoc p sm tm).symm
    _ = (ns ≫ ss) ≫ tm := congrArg (fun f => f ≫ tm) hSource
    _ = ns ≫ (ss ≫ tm) := Category.assoc ns ss tm
    _ = ns ≫ (mm ≫ w) := congrArg (fun f => ns ≫ f) hTarget
    _ = (ns ≫ mm) ≫ w := (Category.assoc ns mm w).symm
    _ = (c ≫ nn) ≫ w := congrArg (fun f => f ≫ w) hCoefficient
    _ = _ := Category.assoc c nn w

end SourceWords

/-- The original composite index embedding retains both complete enriched Hom maps. -/
theorem compositeHomMap (r n : ℕ) :
    sequentialOrthogonalOperatorIndexFunctor.{u, v}.map
        (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) =
      sequentialSymmetricOperatorHomMap.{u, v}
        (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) ≫
      symmetricOrthogonalOperatorHomMap.{u, v}
        (Sequential.finiteIndex r) (Sequential.finiteIndex (r + n)) := rfl

/-- Both original embedding maps keep the full native coefficient and mapped target index action. -/
theorem orderedPowerCompositeCoefficient (r n : ℕ) :
    (Sequential.sequentialPowerIso.{u, v} r n).inv ≫
      sequentialSymmetricOperatorHomMap.{u, v}
        (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) ≫
      symmetricOrthogonalOperatorHomMap.{u, v}
        (Sequential.finiteIndex r) (Sequential.finiteIndex (r + n)) =
      (orderedCoefficientIso.{u, v} n).hom ≫ OrthogonalOperatorIndex.nu.{u, v} r n ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex r))
          (orderedTargetIso.{u, v} r n).hom := by
  have hs := (Sequential.sequentialPower_inclusion_map.{u, v} r n).trans
    (Sequential.ordered_inclusion_factor.{u, v} r n).symm
  have ht := EnrichedFunctor.map_eHomWhiskerLeft_forget symmetricOrthogonalOperatorIndexFunctor.{u, v}
    (PointedCGWH.symmetricOperatorObj (Sequential.finiteIndex r))
    (PointedCGWH.symmetricOperatorObj (Sequential.finiteIndex r ⊗ Sequential.finiteIndex n))
    (PointedCGWH.symmetricOperatorObj (Sequential.finiteIndex (r + n)))
    (Sequential.orderedIndexIso r n).hom
  have hTarget : eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj (Sequential.finiteIndex r)))
      (Sequential.orderedIndexIso r n).hom ≫
      symmetricOrthogonalOperatorHomMap (Sequential.finiteIndex r) (Sequential.finiteIndex (r + n)) =
      symmetricOrthogonalOperatorHomMap (Sequential.finiteIndex r)
        (Sequential.finiteIndex r ⊗ Sequential.finiteIndex n) ≫
      eHomWhiskerLeft PointedCGWH.{u, v}
        (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex r))
        (orderedTargetIso r n).hom := ht
  have hc := symmetricOrthogonal_inclusion.{u, v} (Sequential.finiteIndex r) (Sequential.finiteIndex n)
  have hAll := sourceMapComposition
    (Sequential.sequentialPowerIso.{u, v} r n).inv
    (sequentialSymmetricOperatorHomMap (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)))
    (symmetricOrthogonalOperatorHomMap (Sequential.finiteIndex r) (Sequential.finiteIndex (r + n)))
    (Actual.symmetricNu (Sequential.finiteIndex r) (Sequential.finiteIndex n))
    (eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (PointedCGWH.symmetricOperatorObj (Sequential.finiteIndex r)))
      (Sequential.orderedIndexIso r n).hom)
    (symmetricOrthogonalOperatorHomMap (Sequential.finiteIndex r) (Sequential.finiteIndex r ⊗ Sequential.finiteIndex n))
    (orderedCoefficientIso n).hom (OrthogonalOperatorIndex.nu r n)
    (eHomWhiskerLeft PointedCGWH.{u, v}
      (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex r))
      (orderedTargetIso r n).hom) hs hTarget hc
  exact hAll

/-- The actual composed index embedding retains every original coefficient and target map. -/
theorem orderedPowerCoefficient (r n : ℕ) :
    (Sequential.sequentialPowerIso.{u, v} r n).inv ≫
      sequentialOrthogonalOperatorIndexFunctor.{u, v}.map
        (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) =
      (orderedCoefficientIso.{u, v} n).hom ≫ OrthogonalOperatorIndex.nu.{u, v} r n ≫
        eHomWhiskerLeft PointedCGWH.{u, v}
          (ForgetEnrichment.of PointedCGWH.{u, v} (OrthogonalOperatorIndex.ofIndex r))
          (orderedTargetIso.{u, v} r n).hom :=
  (congrArg (fun f => (Sequential.sequentialPowerIso.{u, v} r n).inv ≫ f)
    (compositeHomMap r n)).trans (orderedPowerCompositeCoefficient r n)

/-- The complete original coefficient-first native action uses the actual right sphere action. -/
theorem nativeNuLeftAction (X : Actual.OrthogonalCarrier.{u, v}) (r n : ℕ) :
    CurrentFree.action (OrthogonalOperatorIndex.ofIndex r) (OrthogonalOperatorIndex.ofIndex (r + n))
      (PointedCGWH.orthogonalSphere n) (OrthogonalOperatorIndex.nu r n) X =
      (β_ (PointedCGWH.orthogonalSphere n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r))).hom ≫
          sphereAction X r n := by
  let A := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)
  let K := PointedCGWH.orthogonalSphere.{u, v} n
  let H := OrthogonalOperatorIndex.ofIndex r ⟶[PointedCGWH.{u, v}]
    OrthogonalOperatorIndex.ofIndex (r + n)
  let D := OrthogonalOperatorIndex.nu.{u, v} r n
  have hb := BraidedCategory.braiding_inv_naturality_left D A
  have hs := SymmetricCategory.braiding_swap_eq_inv_braiding A K
  have h : (D ▷ A) ≫ (β_ A H).inv = (β_ K A).hom ≫ (A ◁ D) :=
    hb.trans (congrArg (fun f => f ≫ (A ◁ D)) hs.symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ MonoidalClosed.uncurry (X.toEnrichedFunctor.map
      (OrthogonalOperatorIndex.ofIndex r) (OrthogonalOperatorIndex.ofIndex (r + n)))) h).trans
        (Category.assoc _ _ _))

/-- Changing only the original coefficient retains the same full native action. -/
theorem action_coefficient {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
    (a b : I) {K L : PointedCGWH.{u, v}} (e : K ⟶ L)
    (D : L ⟶ (a ⟶[PointedCGWH.{u, v}] b)) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    CurrentFree.action a b K (e ≫ D) X =
      (e ▷ X.toEnrichedFunctor.obj a) ≫ CurrentFree.action a b L D X := by
  simp only [CurrentFree.action, comp_whiskerRight, Category.assoc]

/-- The whole original higher transpose has the same complete native action word. -/
theorem orderedPowerUncurry (X : Actual.OrthogonalCarrier.{u, v}) (r n : ℕ) :
    MonoidalClosed.uncurry (Sequential.sequentialPowerAdjoint
      ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) r n) =
      ((orderedCoefficientIso n).hom ▷ X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)) ≫
      CurrentFree.action (OrthogonalOperatorIndex.ofIndex r) (OrthogonalOperatorIndex.ofIndex (r + n))
        (PointedCGWH.orthogonalSphere n) (OrthogonalOperatorIndex.nu r n) X ≫
      Sequential.indexMap X (orderedTargetIso r n).hom := by
  let P := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} n
  let i := OrthogonalOperatorIndex.ofIndex.{u, v} r
  let j := OrthogonalOperatorIndex.ofIndex.{u, v} (r + n)
  let L := PointedCGWH.orthogonalSphere.{u, v} n
  let c := (orderedCoefficientIso.{u, v} n).hom
  let D := OrthogonalOperatorIndex.nu.{u, v} r n
  let q := (orderedTargetIso.{u, v} r n).hom
  let post := eHomWhiskerLeft PointedCGWH.{u, v} (ForgetEnrichment.of PointedCGWH.{u, v} i) q
  have hu := CurrentFree.adjoint_uncurry
    (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) P
    (Sequential.sequentialPowerIso r n).inv
    ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X)
  have hr := restriction_action sequentialOrthogonalOperatorIndexFunctor.{u, v}
    (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) P
    (Sequential.sequentialPowerIso r n).inv X
  have hd := congrArg (fun d => CurrentFree.action i j P d X) (orderedPowerCoefficient r n)
  have ha := action_coefficient i j c (D ≫ post) X
  have hp := Sequential.action_postcompose i j j L D q X
  exact hu.trans (hr.trans (hd.trans (ha.trans
    (congrArg (fun f => (c ▷ X.toEnrichedFunctor.obj i) ≫ f) hp))))

/-- The exact original equality functions invert in the same source order. -/
theorem sourceEqualityInverse {C : Type*} [Category C] {A B D : C} (h : A = B) (k : B = D) :
    (eqToIso (h.trans k)).inv = eqToHom k.symm ≫ (eqToIso h).inv := by
  cases h
  cases k
  simp only [eqToIso_refl, Iso.refl_inv, eqToHom_refl, Category.id_comp]

/-- Reindexing an original finite structure map retains its same complete source and target functions. -/
theorem iteratedStructureDegreeCast (Y : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v} PointedCGWH.sphereOne)
    (r n m k : ℕ) (hm : n = m) (hk : n + r = k) (hmk : m + r = k) :
    (eqToHom (congrArg (TensorPower.tensorPowObj PointedCGWH.sphereOne) hm) ▷ Y.level r) ≫
      CategoryTheory.SequentialSpectrum.iteratedStructureMap Y m r ≫ eqToHom (congrArg Y.level hmk) =
      CategoryTheory.SequentialSpectrum.iteratedStructureMap Y n r ≫ eqToHom (congrArg Y.level hk) := by
  cases hm
  simp only [eqToHom_refl, id_whiskerRight, Category.id_comp]

/-- Every original sequential higher action is its unchanged finite successor iteration and target cast. -/
theorem sequentialPowerAction (X : PointedCGWH.SequentialSpectrum.{u, v}) (r n : ℕ) :
    CurrentFree.action (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n))
      (TensorPower.tensorPowObj PointedCGWH.sphereOne n) (Sequential.sequentialPowerIso r n).inv X =
      CategoryTheory.SequentialSpectrum.iteratedStructureMap
        (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X) n r ≫
          eqToHom (congrArg X.level (Nat.add_comm n r)) := by
  let Y := CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X
  let P := TensorPower.tensorPowObj PointedCGWH.sphereOne
  let h := Nat.add_sub_cancel_left r n
  let e := Sequential.sequentialForwardIso r (r + n) (Nat.le_add_right r n)
  have he : (Sequential.sequentialPowerIso.{u, v} r n).inv =
      eqToHom (congrArg P h.symm) ≫ e.inv :=
    sourceEqualityInverse
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le PointedCGWH.sphereOne
        (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) (Nat.le_add_right r n))
      (congrArg P h)
  have hs := congrArg (fun f => CurrentFree.action
    (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n)) (P n) f X) he
  have hw : CurrentFree.action (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n))
      (P n) (eqToHom (congrArg P h.symm) ≫ e.inv) X =
      (eqToHom (congrArg P h.symm) ▷ X.level r) ≫
      CurrentFree.action (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n))
        (P ((r + n) - r)) e.inv X := by
    simp only [CurrentFree.action, comp_whiskerRight, Category.assoc]
  have hf := Sequential.sequentialForward_action X r (r + n) (Nat.le_add_right r n)
  have hp := congrArg (fun f => (eqToHom (congrArg P h.symm) ▷ X.level r) ≫ f) hf
  have hc := iteratedStructureDegreeCast Y r n ((r + n) - r) (r + n) h.symm
    (Nat.add_comm n r) (Nat.sub_add_cancel (Nat.le_add_right r n))
  exact hs.trans (hw.trans (hp.trans hc))

/-- The finite successor iteration is the actual native nu action, coefficient comparison and target permutation. -/
theorem finiteNativeAction (X : Actual.OrthogonalCarrier.{u, v}) (r n : ℕ) :
    let S : PointedCGWH.SequentialSpectrum.{u, v} :=
      (restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X
    CategoryTheory.SequentialSpectrum.iteratedStructureMap
      (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne S) n r ≫
        eqToHom (congrArg S.level (Nat.add_comm n r)) =
      ((orderedCoefficientIso n).hom ▷ X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)) ≫
      (β_ (PointedCGWH.orthogonalSphere n)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r))).hom ≫ sphereAction X r n ≫
      Sequential.indexMap X (orderedTargetIso r n).hom := by
  dsimp only
  have hs := sequentialPowerAction ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) r n
  have hu : MonoidalClosed.uncurry (Sequential.sequentialPowerAdjoint
      ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) r n) =
      CurrentFree.action (Sequential.sequentialDegree r) (Sequential.sequentialDegree (r + n))
        (TensorPower.tensorPowObj PointedCGWH.sphereOne n) (Sequential.sequentialPowerIso r n).inv
        ((restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}).obj X) :=
    CurrentFree.adjoint_uncurry _ _ _ _ _
  have hn := congrArg (fun f =>
    ((orderedCoefficientIso n).hom ▷ X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)) ≫ f ≫
      Sequential.indexMap X (orderedTargetIso r n).hom) (nativeNuLeftAction X r n)
  exact hs.symm.trans (hu.symm.trans ((orderedPowerUncurry X r n).trans hn))

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

open PointedCGWH.SphereHom

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf

/-- Original identity evaluation retains the full coefficient precomposition. -/
theorem evaluate_coefficient (a : OrthogonalOperatorIndex.{u, v})
    {K L : PointedCGWH.{u, v}} (e : K ⟶ L) (X : Actual.OrthogonalCarrier.{u, v})
    (f : Free.object a L ⟶ X) :
    Free.evaluate a K X ((Free.functor a).map e ≫ f) = e ≫ Free.evaluate a L X f := by
  simp only [Free.evaluate, component_comp, Free.coefficientMap_component]
  rw [whisker_exchange_assoc, rightUnitor_inv_naturality_assoc]

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The complete native representative retains its same original scalar sphere and actual free evaluation. -/
theorem nativeSphereClass_evaluate
    (a : OrthogonalOperatorIndex.{u, v}) (d : ℕ) (X : Actual.OrthogonalCarrier.{u, v})
    (f : Free.object a (PointedCGWH.orthogonalSphere.{u, v} d) ⟶ X) :
    (nativeSpherePiHomEquiv a d X).symm
      ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f) =
      (spherePiHomEquiv d (X.toEnrichedFunctor.obj a)).symm
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH.{u, v}).map
          ((nativeSphereSourceIso d).hom ≫ Free.evaluate a (PointedCGWH.orthogonalSphere.{u, v} d) X f)) := by
  let _ : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    freeAtEvaluation_isQuillenAdjunction a
  change (spherePiHomEquiv d (X.toEnrichedFunctor.obj a)).symm
      (FreeSphereHom.freeHoHomEquiv a (sphere d) X
        ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
          ((Free.functor a).map (nativeSphereSourceIso d).hom) ≫
          (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Functor.map_comp]
  let g := (Free.functor a).map (nativeSphereSourceIso d).hom ≫ f
  have h := QuillenOrdinaryHoHom.homEquiv_map (Free.adjunction (V := PointedCGWH.{u, v}) a)
    (sphere d) X g
  have hFree := congrFun (congrFun (Free.adjunction_homEquiv (V := PointedCGWH.{u, v}) a)
    (sphere d)) X
  have hOrdinary : (Free.adjunction (V := PointedCGWH.{u, v}) a).homEquiv (sphere d) X g =
      (nativeSphereSourceIso d).hom ≫ Free.evaluate a (PointedCGWH.orthogonalSphere.{u, v} d) X f := by
    have he := congrArg (fun e => e g) hFree
    exact he.trans (evaluate_coefficient a (nativeSphereSourceIso d).hom X f)
  exact congrArg (spherePiHomEquiv d (X.toEnrichedFunctor.obj a)).symm
    (h.trans ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH.{u, v}).congr_map hOrdinary))

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end ActualGammaRepresentatives

section NativeGammaGroupBridge


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open PointedCGWH.SphereHom PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- Positive degree casts keep the actual underlying cube function. -/
theorem positiveDegreeCast (a b : ℕ) (h : a = b) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN (a + 1) X) :
    ((eqToIso (congrArg PointedCGWH.piNPositiveFunctor h)).hom.app X).hom x =
      (eqToIso (congrArg PointedCGWH.piNFunctor
        (congrArg (fun k => k + 1) h))).hom.app X x := by
  cases h
  rfl

/-- The actual Type degree-Iso component is its full original dependent cast. -/
theorem originalTypeDegreeCast (a b : ℕ) (h : a = b) (X : PointedCGWH.{u, v})
    (z : PointedCGWH.piN a X) :
    (eqToIso (congrArg PointedCGWH.piNFunctor h)).hom.app X z =
      Equiv.cast (congrArg (fun d => PointedCGWH.piN d X) h) z := by
  cases h
  rfl

/-- The full group shift followed by its actual positive-degree cast is an equivalence. -/
def positiveOrderedShiftEquiv (n k : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN (k + 1) ((loopPower n).obj X) ≃
      PointedCGWH.piN (k + 1 + n) X :=
  ((forget GrpCat).mapIso ((loopPowerGroupShiftNatIso n k).app X)).toEquiv.trans
    (Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
      (show k + n + 1 = k + 1 + n by omega)))

/-- Every complete positive group map retains its actual degree cast. -/
theorem positiveOrderedShiftEquiv_apply (n k : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN (k + 1) ((loopPower n).obj X)) :
    positiveOrderedShiftEquiv n k X x =
      (Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
        (show k + n + 1 = k + 1 + n by omega)))
      (((loopPowerGroupShiftNatIso n k).hom.app X).hom x) := rfl

/-- The whole group successor has the exact three original component maps. -/
theorem originalGroupSuccessorHom (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerGroupShiftNatIso (n + 1) k).hom.app X =
      (nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj X) ≫
        (loopPowerGroupShiftNatIso n (k + 1)).hom.app X ≫
        (eqToIso (congrArg PointedCGWH.piNPositiveFunctor
          (show k + 1 + n = k + (n + 1) by omega))).hom.app X := by
  change 𝟙 _ ≫ (nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj X) ≫
    (loopPowerGroupShiftNatIso n (k + 1)).hom.app X ≫ _ = _
  exact Category.id_comp _

/-- The whole Type successor keeps the same actual shift, previous power and degree cast. -/
theorem originalTypeSuccessorHom (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (loopPowerPiShift (n + 1) k).hom.app X =
      (nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) ≫
        (loopPowerPiShift n (k + 1)).hom.app X ≫
        (eqToIso (congrArg PointedCGWH.piNFunctor
          (show k + 1 + n = k + (n + 1) by omega))).hom.app X := by
  change 𝟙 _ ≫ (nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) ≫
    (loopPowerPiShift n (k + 1)).hom.app X ≫ _ = _
  exact Category.id_comp _

/-- A complete square of actual degree casts retains the same given intermediate class. -/
theorem originalDegreeCastSquare {a b c d : ℕ}
    (hab : a = b) (hbd : b = d) (hac : a = c) (hcd : c = d)
    (X : PointedCGWH.{u, v}) (z : PointedCGWH.piN a X) (w : PointedCGWH.piN c X)
    (hw : Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) hac) z = w) :
    Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) hbd)
        (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) hab) z) =
      (eqToIso (congrArg PointedCGWH.piNFunctor hcd)).hom.app X w := by
  cases hab
  cases hac
  cases hbd
  cases hcd
  exact hw

/-- Every whole ordered group shift has the same underlying original all-degree function. -/
theorem loopPowerGroupShift_hom_eq_allDegree (n k : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN (k + 1) ((loopPower n).obj X)) :
    positiveOrderedShiftEquiv n k X x =
      (loopPowerPiShift n (k + 1)).hom.app X x := by
  induction n generalizing k with
  | zero =>
    simp only [positiveOrderedShiftEquiv_apply, loopPowerGroupShiftNatIsoZero,
      loopPowerPiShiftZero]
    rfl
  | succ n ih =>
    rw [positiveOrderedShiftEquiv_apply]
    have hg := ConcreteCategory.congr_hom (originalGroupSuccessorHom n k X) x
    have ht := ConcreteCategory.congr_hom (originalTypeSuccessorHom n (k + 1) X) x
    change ((loopPowerGroupShiftNatIso (n + 1) k).hom.app X).hom x =
      ((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom
        (((loopPowerGroupShiftNatIso n (k + 1)).hom.app X).hom
          (((nativeLoopGroupShiftNatIso k).hom.app ((loopPower n).obj X)).hom x)) at hg
    change (loopPowerPiShift (n + 1) (k + 1)).hom.app X x =
      (eqToIso (congrArg PointedCGWH.piNFunctor
        (show k + 1 + 1 + n = k + 1 + (n + 1) by omega))).hom.app X
        ((loopPowerPiShift n (k + 1 + 1)).hom.app X
          ((nativeLoopPiShiftNatIso (k + 1)).hom.app ((loopPower n).obj X) x)) at ht
    rw [hg, ht]
    have hstep := nativeLoopGroupShiftNatIso_hom_eq_allDegree k ((loopPower n).obj X) x
    have hprior := ih (k + 1)
      ((nativeLoopPiShiftNatIso (k + 1)).hom.app ((loopPower n).obj X) x)
    change (Equiv.cast (congrArg (fun d => PointedCGWH.piN d X)
        (show k + 1 + n + 1 = k + 1 + 1 + n by omega)))
      (((loopPowerGroupShiftNatIso n (k + 1)).hom.app X).hom
        ((nativeLoopPiShiftNatIso (k + 1)).hom.app ((loopPower n).obj X) x)) =
      (loopPowerPiShift n (k + 1 + 1)).hom.app X
        ((nativeLoopPiShiftNatIso (k + 1)).hom.app ((loopPower n).obj X) x) at hprior
    rw [hstep]
    let y : PointedCGWH.piN (k + 1 + 1) ((loopPower n).obj X) :=
      (nativeLoopPiShiftNatIso (k + 1)).hom.app ((loopPower n).obj X) x
    let z : PointedCGWH.piN (k + 1 + n + 1) X :=
      ((loopPowerGroupShiftNatIso n (k + 1)).hom.app X).hom y
    let w : PointedCGWH.piN (k + 1 + 1 + n) X :=
      (loopPowerPiShift n (k + 1 + 1)).hom.app X y
    have hc : ((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom z =
      Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show k + 1 + n + 1 = k + (n + 1) + 1 by omega)) z := by
      exact (positiveDegreeCast (k + 1 + n) (k + (n + 1)) (by omega) X z).trans
        (originalTypeDegreeCast (k + 1 + n + 1) (k + (n + 1) + 1) (by omega) X z)
    have hp : Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show k + 1 + n + 1 = k + 1 + 1 + n by omega)) z = w := hprior
    have hs := originalDegreeCastSquare
      (a := k + 1 + n + 1) (b := k + (n + 1) + 1)
      (c := k + 1 + 1 + n) (d := k + 1 + (n + 1))
      (by omega) (by omega) (by omega) (by omega) X z w hp
    change (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show k + (n + 1) + 1 = k + 1 + (n + 1) by omega)))
      (((eqToIso (congrArg PointedCGWH.piNPositiveFunctor
        (show k + 1 + n = k + (n + 1) by omega))).hom.app X).hom z) =
      (eqToIso (congrArg PointedCGWH.piNFunctor
        (show k + 1 + 1 + n = k + 1 + (n + 1) by omega))).hom.app X w
    exact (congrArg (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
      (show k + (n + 1) + 1 = k + 1 + (n + 1) by omega))) hc).trans hs


/-- Both entire comparison directions are the same original sphere-Hom shift functions. -/
theorem positiveOrderedShiftEquiv_eq_allDegree (n k : ℕ) (X : PointedCGWH.{u, v}) :
    positiveOrderedShiftEquiv n k X = ((loopPowerPiShift n (k + 1)).app X).toEquiv := by
  apply Equiv.ext
  exact loopPowerGroupShift_hom_eq_allDegree n k X

/-- The full inverse original group function keeps the same actual sphere-Hom source shift. -/
theorem positiveOrderedShiftEquiv_inverse_eq_allDegree (n k : ℕ) (X : PointedCGWH.{u, v}) :
    (positiveOrderedShiftEquiv n k X).symm =
      (((loopPowerPiShift n (k + 1)).app X).toEquiv).symm :=
  congrArg Equiv.symm (positiveOrderedShiftEquiv_eq_allDegree n k X)


end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaGroupBridge

section NativeGammaPowerAdjunction


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- The whole original loop power retains both complete original functor maps. -/
theorem originalLoopPowerAdd (a b : ℕ) :
    loopPower.{u, v} (a + b) = loopPower b ⋙ loopPower a := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    change loopPower b = loopPower b ⋙ 𝟭 _
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    change loopPower (a + b) ⋙ PointedCGWH.loop =
      loopPower b ⋙ (loopPower a ⋙ PointedCGWH.loop)
    exact (congrArg (fun F => F ⋙ PointedCGWH.loop) ih).trans (by rfl)

/-- Every whole original suspension power is the exact composition of its
given original factors, before any source sphere object is projected. -/
theorem originalSphereTensorPowerAdd (a b : ℕ) :
    sphereTensorPower.{u, v} (a + b) = sphereTensorPower a ⋙ sphereTensorPower b := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    change sphereTensorPower b = 𝟭 _ ⋙ sphereTensorPower b
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    change PointedCGWH.suspension ⋙ sphereTensorPower (a + b) =
      (PointedCGWH.suspension ⋙ sphereTensorPower a) ⋙ sphereTensorPower b
    exact (congrArg (fun F => PointedCGWH.suspension ⋙ F) ih).trans (by rfl)

/-- The tensor-power and loop-power adjunction transported along the original addition equalities
for both power functors. -/
def originalTransportedPowerAdjunction (a b : ℕ) :
    sphereTensorPower a ⋙ sphereTensorPower b ⊣ loopPower b ⋙ loopPower a :=
  ((powerAdjunction (a + b)).ofNatIsoLeft
    (eqToIso (originalSphereTensorPowerAdd a b))).ofNatIsoRight
      (eqToIso (originalLoopPowerAdd a b))

/-- The actual original transported source/target maps retain the whole native power-Hom function. -/
theorem originalTransportedPowerHom (a b : ℕ) (X Y : PointedCGWH.{u, v})
    (f : (sphereTensorPower a ⋙ sphereTensorPower b).obj X ⟶ Y) :
    (originalTransportedPowerAdjunction a b).homEquiv X Y f =
      (powerAdjunction (a + b)).homEquiv X Y
        (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd a b) X) ≫ f) ≫
      eqToHom (Functor.congr_obj (originalLoopPowerAdd a b) Y) := by
  have hL : (eqToIso (originalSphereTensorPowerAdd a b)).hom.app X =
      eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd a b) X) :=
    eqToHom_app (originalSphereTensorPowerAdd a b) X
  have hR : (eqToIso (originalLoopPowerAdd a b)).hom.app Y =
      eqToHom (Functor.congr_obj (originalLoopPowerAdd a b) Y) :=
    eqToHom_app (originalLoopPowerAdd a b) Y
  have h := Adjunction.homEquiv_ofNatIsoRight_apply
    ((powerAdjunction (a + b)).ofNatIsoLeft (eqToIso (originalSphereTensorPowerAdd a b)))
    (eqToIso (originalLoopPowerAdd a b)) f
  have hInner := Adjunction.homEquiv_ofNatIsoLeft_apply (powerAdjunction (a + b))
    (eqToIso (originalSphereTensorPowerAdd a b)) f
  exact h.trans ((congrArg₂ (fun z t => z ≫ t) hInner hR).trans
    (congrArg (fun z => (powerAdjunction (a + b)).homEquiv X Y (z ≫ f) ≫
      eqToHom (Functor.congr_obj (originalLoopPowerAdd a b) Y)) hL))

/-- Both entire inverse power-Hom functions retain the actual source and target transports. -/
theorem originalTransportedPowerHom_inverse (a b : ℕ) (X Y : PointedCGWH.{u, v})
    (g : X ⟶ (loopPower b ⋙ loopPower a).obj Y) :
    ((originalTransportedPowerAdjunction a b).homEquiv X Y).symm g =
      eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd a b).symm X) ≫
        ((powerAdjunction (a + b)).homEquiv X Y).symm
          (g ≫ eqToHom (Functor.congr_obj (originalLoopPowerAdd a b).symm Y)) := by
  have hL : (eqToIso (originalSphereTensorPowerAdd a b)).inv.app X =
      eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd a b).symm X) :=
    eqToHom_app (originalSphereTensorPowerAdd a b).symm X
  have hR : (eqToIso (originalLoopPowerAdd a b)).inv.app Y =
      eqToHom (Functor.congr_obj (originalLoopPowerAdd a b).symm Y) :=
    eqToHom_app (originalLoopPowerAdd a b).symm Y
  simp only [originalTransportedPowerAdjunction, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply, hL, hR]

universe uC vC uA uD uF
variable {C : Type uC} [Category.{vC} C]

/-- An actual equality of both functors retains the entire Hom equivalence. -/
theorem originalAdjunctionHom_transport {L M R S : C ⥤ C}
    (hL : L = M) (hR : R = S) (adj : L ⊣ R) (X Y : C) :
    HEq (adj.homEquiv X Y)
      ((((adj.ofNatIsoLeft (eqToIso hL)).ofNatIsoRight (eqToIso hR)).homEquiv X Y)) := by
  subst M
  subst S
  apply heq_of_eq
  apply Equiv.ext
  intro f
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_ofNatIsoLeft_apply, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- The actual iterated left functor retains all its original maps. -/
def originalAdjunctionLeftPower (L : C ⥤ C) : ℕ → (C ⥤ C) :=
  Nat.rec (𝟭 C) (fun _ previous => L ⋙ previous)

/-- The actual iterated right functor retains all its original maps. -/
def originalAdjunctionRightPower (R : C ⥤ C) : ℕ → (C ⥤ C) :=
  Nat.rec (𝟭 C) (fun _ previous => previous ⋙ R)

/-- The actual ordered power adjunction retains the complete unit and counit recursion. -/
def originalAdjunctionPower {L R : C ⥤ C} (adj : L ⊣ R) :
    ∀ n, originalAdjunctionLeftPower L n ⊣ originalAdjunctionRightPower R n :=
  Nat.rec (motive := fun n => originalAdjunctionLeftPower L n ⊣ originalAdjunctionRightPower R n)
    Adjunction.id (fun _ previous => adj.comp previous)

/-- Full zero and successor adjunctions retain their original Hom equivalences. -/
theorem originalAdjunctionPowerZero {L R : C ⥤ C} (adj : L ⊣ R) :
    originalAdjunctionPower adj 0 = Adjunction.id := rfl

/-- Both actual successor Hom functions are the original two-factor composite. -/
theorem originalAdjunctionPowerSucc {L R : C ⥤ C} (adj : L ⊣ R) (n : ℕ) :
    originalAdjunctionPower adj (n + 1) = adj.comp (originalAdjunctionPower adj n) := rfl

/-- Whole left powers preserve their literal ordered addition comparison. -/
theorem originalAdjunctionLeftPowerAdd (L : C ⥤ C) (b a : ℕ) :
    originalAdjunctionLeftPower L (b + a) =
      originalAdjunctionLeftPower L a ⋙ originalAdjunctionLeftPower L b := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg (fun F => L ⋙ F) ih

/-- Whole right powers preserve their literal ordered addition comparison. -/
theorem originalAdjunctionRightPowerAdd (R : C ⥤ C) (b a : ℕ) :
    originalAdjunctionRightPower R (b + a) =
      originalAdjunctionRightPower R b ⋙ originalAdjunctionRightPower R a := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg (fun F => F ⋙ R) ih

/-- The full two equivalence maps preserve an actual dependent comparison of their source. -/
theorem originalEquivTrans_heq {A B : Type uA} {D E : Type uD} {F G : Type uF}
    (hA : A = B) (hD : D = E) (hF : F = G)
    (f : A ≃ D) (g : B ≃ E) (k : D ≃ F) (l : E ≃ G)
    (h : HEq f g) (j : HEq k l) : HEq (f.trans k) (g.trans l) := by
  subst B
  subst E
  subst G
  cases h
  cases j
  rfl

/-- Both full Hom functions of the same iterated adjunction preserve every ordered split. -/
theorem originalAdjunctionPowerHomAdd_heq {L R : C ⥤ C} (adj : L ⊣ R)
    (b a : ℕ) (X Y : C) :
    HEq ((originalAdjunctionPower adj (b + a)).homEquiv X Y)
      (((originalAdjunctionPower adj a).comp (originalAdjunctionPower adj b)).homEquiv X Y) := by
  induction a generalizing X with
  | zero =>
    have h :
        ((Adjunction.id (C := C)).comp (originalAdjunctionPower adj b)).homEquiv X Y =
        (originalAdjunctionPower adj b).homEquiv X Y := by
      have hComp := congrFun (congrFun (Adjunction.comp_homEquiv
        (Adjunction.id (C := C)) (originalAdjunctionPower adj b)) X) Y
      have hId : (Adjunction.id (C := C)).homEquiv X
          ((originalAdjunctionRightPower R b).obj Y) = Equiv.refl _ := by
        apply Equiv.ext
        intro f
        change 𝟙 X ≫ f = f
        exact Category.id_comp f
      exact hComp.trans ((congrArg (fun e =>
        ((originalAdjunctionPower adj b).homEquiv X Y).trans e) hId).trans
          (Equiv.trans_refl _))
    exact heq_of_eq h.symm
  | succ a ih =>
    have h := ih (L.obj X)
    have hA :
        ((originalAdjunctionLeftPower L (b + a)).obj (L.obj X) ⟶ Y) =
        (((originalAdjunctionLeftPower L a ⋙ originalAdjunctionLeftPower L b).obj (L.obj X)) ⟶ Y) :=
      congrArg (fun F : C ⥤ C => F.obj (L.obj X) ⟶ Y)
        (originalAdjunctionLeftPowerAdd L b a)
    have hR : (originalAdjunctionRightPower R (b + a)).obj Y =
        (originalAdjunctionRightPower R a).obj ((originalAdjunctionRightPower R b).obj Y) :=
      Functor.congr_obj (originalAdjunctionRightPowerAdd R b a) Y
    have hD : (L.obj X ⟶ (originalAdjunctionRightPower R (b + a)).obj Y) =
        (L.obj X ⟶ (originalAdjunctionRightPower R a).obj
          ((originalAdjunctionRightPower R b).obj Y)) :=
      congrArg (fun Z => L.obj X ⟶ Z) hR
    have hF : (X ⟶ R.obj ((originalAdjunctionRightPower R (b + a)).obj Y)) =
        (X ⟶ R.obj ((originalAdjunctionRightPower R a).obj
          ((originalAdjunctionRightPower R b).obj Y))) :=
      congrArg (fun Z => X ⟶ R.obj Z) hR
    have hOuter :
        HEq (adj.homEquiv X ((originalAdjunctionRightPower R (b + a)).obj Y))
          (adj.homEquiv X ((originalAdjunctionRightPower R a).obj
            ((originalAdjunctionRightPower R b).obj Y))) := by
      exact (show ∀ {U V : C}, U = V → HEq (adj.homEquiv X U) (adj.homEquiv X V) from
        fun h => by cases h; rfl) hR
    have hTrans := originalEquivTrans_heq hA hD hF
      ((originalAdjunctionPower adj (b + a)).homEquiv (L.obj X) Y)
      (((originalAdjunctionPower adj a).comp (originalAdjunctionPower adj b)).homEquiv (L.obj X) Y)
      (adj.homEquiv X ((originalAdjunctionRightPower R (b + a)).obj Y))
      (adj.homEquiv X ((originalAdjunctionRightPower R a).obj
        ((originalAdjunctionRightPower R b).obj Y))) h hOuter
    have hTotal :
        (originalAdjunctionPower adj (b + (a + 1))).homEquiv X Y =
          ((originalAdjunctionPower adj (b + a)).homEquiv (L.obj X) Y).trans
            (adj.homEquiv X ((originalAdjunctionRightPower R (b + a)).obj Y)) :=
      congrFun (congrFun (Adjunction.comp_homEquiv adj
        (originalAdjunctionPower adj (b + a))) X) Y
    have hParts :
        ((originalAdjunctionPower adj (a + 1)).comp (originalAdjunctionPower adj b)).homEquiv X Y =
          ((originalAdjunctionPower adj b).homEquiv
            ((originalAdjunctionLeftPower L a).obj (L.obj X)) Y).trans
            (((originalAdjunctionPower adj a).homEquiv (L.obj X)
              ((originalAdjunctionRightPower R b).obj Y)).trans
              (adj.homEquiv X ((originalAdjunctionRightPower R a).obj
                ((originalAdjunctionRightPower R b).obj Y)))) := by
      have hComp := congrFun (congrFun (Adjunction.comp_homEquiv
        (adj.comp (originalAdjunctionPower adj a)) (originalAdjunctionPower adj b)) X) Y
      have hInside := congrFun (congrFun (Adjunction.comp_homEquiv adj
        (originalAdjunctionPower adj a)) X) ((originalAdjunctionRightPower R b).obj Y)
      exact hComp.trans (congrArg (fun e =>
        ((originalAdjunctionPower adj b).homEquiv
          ((originalAdjunctionLeftPower L a).obj (L.obj X)) Y).trans e) hInside)
    have hTransExpanded :
        HEq (((originalAdjunctionPower adj (b + a)).homEquiv (L.obj X) Y).trans
            (adj.homEquiv X ((originalAdjunctionRightPower R (b + a)).obj Y)))
          ((((originalAdjunctionPower adj b).homEquiv
              ((originalAdjunctionLeftPower L a).obj (L.obj X)) Y).trans
            ((originalAdjunctionPower adj a).homEquiv (L.obj X)
              ((originalAdjunctionRightPower R b).obj Y))).trans
            (adj.homEquiv X ((originalAdjunctionRightPower R a).obj
              ((originalAdjunctionRightPower R b).obj Y)))) := by
      have hComp := congrFun (congrFun (Adjunction.comp_homEquiv
        (originalAdjunctionPower adj a) (originalAdjunctionPower adj b)) (L.obj X)) Y
      exact hTrans.trans (heq_of_eq (congrArg (fun e => e.trans
        (adj.homEquiv X ((originalAdjunctionRightPower R a).obj
          ((originalAdjunctionRightPower R b).obj Y)))) hComp))
    exact (heq_of_eq hTotal).trans
      ((hTransExpanded.trans (heq_of_eq (Equiv.trans_assoc _ _ _))).trans (heq_of_eq hParts.symm))

/-- Equality of both complete Hom functions identifies the entire actual adjunction. -/
theorem originalAdjunction_ext_of_homEquiv {L R : C ⥤ C} (adj other : L ⊣ R)
    (h : ∀ X Y, adj.homEquiv X Y = other.homEquiv X Y) : adj = other := by
  apply Adjunction.ext
  apply NatTrans.ext
  funext X
  have hUnit := congrArg (fun e => e (𝟙 (L.obj X))) (h X (L.obj X))
  have hMap : R.map (𝟙 (L.obj X)) = 𝟙 (R.obj (L.obj X)) := R.map_id _
  have hLeft : adj.homEquiv X (L.obj X) (𝟙 (L.obj X)) = adj.unit.app X :=
    (congrArg (fun z => adj.unit.app X ≫ z) hMap).trans (Category.comp_id _)
  have hRight : other.homEquiv X (L.obj X) (𝟙 (L.obj X)) = other.unit.app X :=
    (congrArg (fun z => other.unit.app X ≫ z) hMap).trans (Category.comp_id _)
  exact hLeft.symm.trans (hUnit.trans hRight)

/-- Both entire Hom functions identify the actual ordered composite power adjunction. -/
theorem originalAdjunctionPowerAdd {L R : C ⥤ C} (adj : L ⊣ R) (b a : ℕ) :
    ((originalAdjunctionPower adj (b + a)).ofNatIsoLeft
      (eqToIso (originalAdjunctionLeftPowerAdd L b a))).ofNatIsoRight
        (eqToIso (originalAdjunctionRightPowerAdd R b a)) =
      (originalAdjunctionPower adj a).comp (originalAdjunctionPower adj b) := by
  apply originalAdjunction_ext_of_homEquiv
  intro X Y
  exact eq_of_heq ((originalAdjunctionHom_transport
    (originalAdjunctionLeftPowerAdd L b a) (originalAdjunctionRightPowerAdd R b a)
    (originalAdjunctionPower adj (b + a)) X Y).symm.trans
      (originalAdjunctionPowerHomAdd_heq adj b a X Y))

/-- Actual source and target equality preserve the entire same composite adjunction. -/
theorem originalAdjunctionComp_heq {L R A B A' B' : C ⥤ C}
    (hA : A = A') (hB : B = B') (adj : L ⊣ R)
    (a : A ⊣ B) (b : A' ⊣ B') (h : HEq a b) : HEq (adj.comp a) (adj.comp b) := by
  subst A'
  subst B'
  cases h
  rfl

/-- Actual functor and adjunction equalities preserve both complete Hom functions. -/
theorem originalAdjunctionHom_heq {L R M S : C ⥤ C}
    (hL : L = M) (hR : R = S) (j : L ⊣ R) (k : M ⊣ S) (h : HEq j k) (X Y : C) :
    HEq (j.homEquiv X Y) (k.homEquiv X Y) := by
  subst M
  subst S
  cases h
  rfl

/-- Two entire actual adjunction comparisons retain the full composite Hom functions. -/
theorem originalAdjunctionPairHom_heq {L R M S L' R' M' S' : C ⥤ C}
    (hL : L = L') (hR : R = R') (hM : M = M') (hS : S = S')
    (j : L ⊣ R) (k : M ⊣ S) (j' : L' ⊣ R') (k' : M' ⊣ S')
    (hj : HEq j j') (hk : HEq k k') (X Y : C) :
    HEq ((j.comp k).homEquiv X Y) ((j'.comp k').homEquiv X Y) := by
  subst L'
  subst R'
  subst M'
  subst S'
  cases hj
  cases hk
  rfl

section ActualSpherePowerAdjunction
open PointedCGWH.SphereHom

/-- Both actual sphere-power source functors are the same complete suspension recursor. -/
theorem originalAdjunctionLeftPower_eq_sphere (n : ℕ) :
    originalAdjunctionLeftPower PointedCGWH.suspension.{u, v} n = sphereTensorPower n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun F => PointedCGWH.suspension ⋙ F) ih

/-- Both actual loop-power target functors retain their complete original recursion. -/
theorem originalAdjunctionRightPower_eq_loop (n : ℕ) :
    originalAdjunctionRightPower PointedCGWH.loop.{u, v} n = loopPower n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun F => F ⋙ PointedCGWH.loop) ih

/-- Both complete original power adjunction functions agree after the actual original source equality. -/
theorem originalAdjunctionPower_heq_sphere (n : ℕ) :
    HEq (originalAdjunctionPower PointedCGWH.suspensionLoopAdjunction.{u, v} n)
      (powerAdjunction.{u, v} n) := by
  induction n with
  | zero =>
    change HEq (Adjunction.id (C := PointedCGWH.{u, v}))
      (Adjunction.id (C := PointedCGWH.{u, v}))
    rfl
  | succ n ih =>
    have h := originalAdjunctionComp_heq (originalAdjunctionLeftPower_eq_sphere n)
      (originalAdjunctionRightPower_eq_loop n) PointedCGWH.suspensionLoopAdjunction.{u, v}
      (originalAdjunctionPower PointedCGWH.suspensionLoopAdjunction.{u, v} n) (powerAdjunction.{u, v} n) ih
    exact h

/-- The exact ordered power-Hom equivalence preserves the actual original suspension and loop maps. -/
theorem originalSpherePowerHomAdd_heq (b a : ℕ) (X Y : PointedCGWH.{u, v}) :
    HEq ((powerAdjunction.{u, v} (b + a)).homEquiv X Y)
      (((powerAdjunction.{u, v} a).comp (powerAdjunction.{u, v} b)).homEquiv X Y) := by
  have h := originalAdjunctionPowerHomAdd_heq PointedCGWH.suspensionLoopAdjunction.{u, v} b a X Y
  have hTotal : HEq
      ((originalAdjunctionPower PointedCGWH.suspensionLoopAdjunction.{u, v} (b + a)).homEquiv X Y)
      ((powerAdjunction.{u, v} (b + a)).homEquiv X Y) := by
    exact originalAdjunctionHom_heq
      (originalAdjunctionLeftPower_eq_sphere (b + a))
      (originalAdjunctionRightPower_eq_loop (b + a)) _ _
      (originalAdjunctionPower_heq_sphere (b + a)) X Y
  have hParts : HEq
      (((originalAdjunctionPower PointedCGWH.suspensionLoopAdjunction.{u, v} a).comp
        (originalAdjunctionPower PointedCGWH.suspensionLoopAdjunction.{u, v} b)).homEquiv X Y)
      (((powerAdjunction.{u, v} a).comp (powerAdjunction.{u, v} b)).homEquiv X Y) := by
    exact originalAdjunctionPairHom_heq
      (originalAdjunctionLeftPower_eq_sphere a) (originalAdjunctionRightPower_eq_loop a)
      (originalAdjunctionLeftPower_eq_sphere b) (originalAdjunctionRightPower_eq_loop b)
      _ _ _ _ (originalAdjunctionPower_heq_sphere a) (originalAdjunctionPower_heq_sphere b) X Y
  exact hTotal.symm.trans (h.trans hParts)

/-- The complete original two-power adjunction is the actual whole transported power adjunction. -/
theorem originalSpherePowerAdjunctionAdd (a b : ℕ) :
    (originalTransportedPowerAdjunction a b :
      sphereTensorPower.{u, v} a ⋙ sphereTensorPower b ⊣ loopPower b ⋙ loopPower a) =
      (powerAdjunction.{u, v} a).comp (powerAdjunction.{u, v} b) := by
  apply originalAdjunction_ext_of_homEquiv
  intro X Y
  have hOriginal := originalSpherePowerHomAdd_heq b a X Y
  have hIndex : a + b = b + a := Nat.add_comm a b
  have hCount : HEq ((powerAdjunction.{u, v} (a + b)).homEquiv X Y)
      ((powerAdjunction.{u, v} (b + a)).homEquiv X Y) := by
    exact (show ∀ {n m : ℕ}, n = m →
      HEq ((powerAdjunction.{u, v} n).homEquiv X Y) ((powerAdjunction.{u, v} m).homEquiv X Y) from
      fun h => by cases h; rfl) hIndex
  exact eq_of_heq ((originalAdjunctionHom_transport
    (originalSphereTensorPowerAdd a b) (originalLoopPowerAdd a b)
    (powerAdjunction.{u, v} (a + b)) X Y).symm.trans (hCount.trans hOriginal))

end ActualSpherePowerAdjunction


end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaPowerAdjunction

section NativeGammaPowerValues


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- Complete scalar source naturality preserves the actual associator. -/
theorem originalAssociatorSourceNaturality {C : Type*} [Category C] [MonoidalCategory C]
    (P K X Y A B : C) (f : X ⟶ Y) (m : A ⟶ B)
    (eX : A ⟶ P ⊗ (K ⊗ X)) (eY : B ⟶ P ⊗ (K ⊗ Y))
    (h : m ≫ eY = eX ≫ (P ◁ (K ◁ f))) :
    m ≫ eY ≫ (α_ P K Y).inv =
      eX ≫ (α_ P K X).inv ≫ ((P ⊗ K) ◁ f) := by
  calc
    _ = (m ≫ eY) ≫ (α_ P K Y).inv := (Category.assoc _ _ _).symm
    _ = (eX ≫ (P ◁ (K ◁ f))) ≫ (α_ P K Y).inv :=
      congrArg (fun z => z ≫ (α_ P K Y).inv) h
    _ = eX ≫ ((P ◁ (K ◁ f)) ≫ (α_ P K Y).inv) := Category.assoc _ _ _
    _ = _ := congrArg (fun z => eX ≫ z) (associator_inv_naturality_right P K f)

/-- Every complete original pointed map preserves the full original sphere-power value Iso. -/
theorem originalSpherePowerValueIso_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (sphereTensorPower n).map f ≫ (spherePowerValueIso n Y).hom =
      (spherePowerValueIso n X).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ f) := by
  induction n generalizing X Y with
  | zero =>
    rw [spherePowerValueIsoZero, spherePowerValueIsoZero]
    exact leftUnitor_inv_naturality f
  | succ n ih =>
    exact originalAssociatorSourceNaturality
      (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)
      PointedCGWH.sphereOne X Y
      ((sphereTensorPower n).obj (PointedCGWH.suspension.obj X))
      ((sphereTensorPower n).obj (PointedCGWH.suspension.obj Y))
      f ((sphereTensorPower n).map (PointedCGWH.sphereOne ◁ f))
      (spherePowerValueIso n (PointedCGWH.suspension.obj X)).hom
      (spherePowerValueIso n (PointedCGWH.suspension.obj Y)).hom
      (ih (PointedCGWH.sphereOne ◁ f))

/-- The whole inverse value function retains those same original pointed maps. -/
theorem originalSpherePowerValueIso_inverse_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) :
    (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ f) ≫
        (spherePowerValueIso n Y).inv =
      (spherePowerValueIso n X).inv ≫ (sphereTensorPower n).map f := by
  apply (cancel_mono (spherePowerValueIso n Y).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    originalSpherePowerValueIso_naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] (K : C)

/-- The actual left-tensor functor recursor, retaining all original maps. -/
def originalTensorSourcePower : ℕ → (C ⥤ C) :=
  Nat.rec (𝟭 C) (fun _ previous => (tensorLeft K) ⋙ previous)

/-- The whole actual zero source power is the original identity functor. -/
theorem originalTensorSourcePowerZero : originalTensorSourcePower K 0 = 𝟭 C := rfl

/-- The whole actual successor source retains its original tensor functor and previous power. -/
theorem originalTensorSourcePowerSucc (n : ℕ) :
    originalTensorSourcePower K (n + 1) = tensorLeft K ⋙ originalTensorSourcePower K n := rfl

/-- Both complete power-value maps retain the original associators and unitors. -/
def originalTensorSourcePowerValue : ∀ n : ℕ, ∀ X : C,
    (originalTensorSourcePower K n).obj X ≅
      MonoidalCategory.TensorPower.tensorPowObj K n ⊗ X :=
  Nat.rec
    (motive := fun n => ∀ X : C, (originalTensorSourcePower K n).obj X ≅
      MonoidalCategory.TensorPower.tensorPowObj K n ⊗ X)
    (fun X => (λ_ X).symm)
    (fun n previous X => previous (K ⊗ X) ≪≫
      (α_ (MonoidalCategory.TensorPower.tensorPowObj K n) K X).symm)

/-- Both original zero value maps are the inverse original source unitor. -/
theorem originalTensorSourcePowerValueZero (X : C) :
    originalTensorSourcePowerValue K 0 X = (λ_ X).symm := rfl

/-- Both complete successor value maps retain the original associator. -/
theorem originalTensorSourcePowerValueSucc (n : ℕ) (X : C) :
    originalTensorSourcePowerValue K (n + 1) X =
      originalTensorSourcePowerValue K n (K ⊗ X) ≪≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj K n) K X).symm := rfl

/-- The same original source recursor retains its full ordered power addition equality. -/
theorem originalTensorSourcePowerAdd (b a : ℕ) :
    originalTensorSourcePower K (b + a) =
      originalTensorSourcePower K a ⋙ originalTensorSourcePower K b := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change tensorLeft K ⋙ originalTensorSourcePower K (b + a) =
      (tensorLeft K ⋙ originalTensorSourcePower K a) ⋙ originalTensorSourcePower K b
    exact congrArg (fun F => tensorLeft K ⋙ F) ih

/-- The full original source-add equality acts on the SAME actual successor source map. -/
theorem originalTensorSourcePowerAddSucc_obj (b a : ℕ) (X : C) :
    eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd K b (a + 1)) X) =
      eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd K b a) (K ⊗ X)) := rfl

/-- The complete actual tensor-power split successor keeps the original tensor Iso and associator. -/
theorem originalTensorPowerAddSucc (b a : ℕ) :
    MonoidalCategory.TensorPower.tensorPowObj_add K b (a + 1) =
      tensorIso (MonoidalCategory.TensorPower.tensorPowObj_add K b a) (Iso.refl K) ≪≫
        α_ (MonoidalCategory.TensorPower.tensorPowObj K b)
          (MonoidalCategory.TensorPower.tensorPowObj K a) K := rfl

/-- Every complete original source map preserves the actual tensor-power value comparison. -/
theorem originalTensorSourcePowerValueNaturality (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (originalTensorSourcePower K n).map f ≫ (originalTensorSourcePowerValue K n Y).hom =
      (originalTensorSourcePowerValue K n X).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj K n ◁ f) := by
  induction n generalizing X Y with
  | zero => exact leftUnitor_inv_naturality f
  | succ n ih =>
    rw [originalTensorSourcePowerValueSucc, originalTensorSourcePowerValueSucc]
    change (originalTensorSourcePower K n).map (K ◁ f) ≫
        (originalTensorSourcePowerValue K n (K ⊗ Y)).hom ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj K n) K Y).inv = _
    have h := originalAssociatorSourceNaturality (MonoidalCategory.TensorPower.tensorPowObj K n) K X Y
      ((originalTensorSourcePower K n).obj (K ⊗ X))
      ((originalTensorSourcePower K n).obj (K ⊗ Y)) f
      ((originalTensorSourcePower K n).map (K ◁ f))
      (originalTensorSourcePowerValue K n (K ⊗ X)).hom
      (originalTensorSourcePowerValue K n (K ⊗ Y)).hom (ih (K ◁ f))
    have hAssoc : (originalTensorSourcePowerValue K n (K ⊗ X)).hom ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj K n) K X).inv ≫
          ((MonoidalCategory.TensorPower.tensorPowObj K n ⊗ K) ◁ f) =
        ((originalTensorSourcePowerValue K n (K ⊗ X)).hom ≫
          (α_ (MonoidalCategory.TensorPower.tensorPowObj K n) K X).inv) ≫
          ((MonoidalCategory.TensorPower.tensorPowObj K n ⊗ K) ◁ f) :=
      (Category.assoc _ _ _).symm
    exact h.trans hAssoc

/-- The exact original source split propagates through the complete associator square. -/
theorem originalSourceSplitStep {A B P Q K X : C}
    (s : A ⟶ B) (e : B ⟶ P ⊗ (Q ⊗ (K ⊗ X)))
    (c : A ⟶ (P ⊗ Q) ⊗ (K ⊗ X))
    (h : s ≫ e ≫ (α_ P Q (K ⊗ X)).inv = c) :
    s ≫ e ≫ (P ◁ (α_ Q K X).inv) ≫ (α_ P (Q ⊗ K) X).inv =
      c ≫ (α_ (P ⊗ Q) K X).inv ≫ ((α_ P Q K).hom ▷ X) := by
  calc
    _ = s ≫ e ≫ ((P ◁ (α_ Q K X).inv) ≫ (α_ P (Q ⊗ K) X).inv) :=
      by rfl
    _ = s ≫ e ≫ ((α_ P Q (K ⊗ X)).inv ≫
        (α_ (P ⊗ Q) K X).inv ≫ ((α_ P Q K).hom ▷ X)) :=
      congrArg (fun t => s ≫ e ≫ t) ((pentagon_inv_inv_hom_inv_inv (W := P) (X := Q) (Y := K) (Z := X))).symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (α_ (P ⊗ Q) K X).inv ≫ ((α_ P Q K).hom ▷ X)) h

/-- The full original value-Iso ordered split is the actual tensor-power addition map. -/
theorem originalTensorSourcePowerValueAdd (b a : ℕ) (X : C) :
    eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd K b a) X) ≫
        (originalTensorSourcePowerValue K b ((originalTensorSourcePower K a).obj X)).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj K b ◁
          (originalTensorSourcePowerValue K a X).hom) ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj K b)
          (MonoidalCategory.TensorPower.tensorPowObj K a) X).inv =
      (originalTensorSourcePowerValue K (b + a) X).hom ≫
        ((MonoidalCategory.TensorPower.tensorPowObj_add K b a).hom ▷ X) := by
  induction a generalizing X with
  | zero =>
    change 𝟙 _ ≫ (originalTensorSourcePowerValue K b X).hom ≫
      (MonoidalCategory.TensorPower.tensorPowObj K b ◁ (λ_ X).inv) ≫
      (α_ (MonoidalCategory.TensorPower.tensorPowObj K b) (𝟙_ C) X).inv =
      (originalTensorSourcePowerValue K b X).hom ≫
        ((ρ_ (MonoidalCategory.TensorPower.tensorPowObj K b)).inv ▷ X)
    exact (Category.id_comp _).trans
      (congrArg (fun f => (originalTensorSourcePowerValue K b X).hom ≫ f)
        (triangle_assoc_comp_left_inv (MonoidalCategory.TensorPower.tensorPowObj K b) X))
  | succ a ih =>
    let P := MonoidalCategory.TensorPower.tensorPowObj K b
    let Q := MonoidalCategory.TensorPower.tensorPowObj K a
    let E := originalTensorSourcePower K a
    let F := originalTensorSourcePower K b
    let t := (originalTensorSourcePowerValue K a (K ⊗ X)).hom
    let e := (originalTensorSourcePowerValue K b (E.obj (K ⊗ X))).hom
    let c := (originalTensorSourcePowerValue K (b + a) (K ⊗ X)).hom
    let d := (MonoidalCategory.TensorPower.tensorPowObj_add K b a).hom
    let s := eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd K b a) (K ⊗ X))
    have h : s ≫ (e ≫ (P ◁ t)) ≫ (α_ P Q (K ⊗ X)).inv = c ≫ (d ▷ (K ⊗ X)) := by
      simpa only [Category.assoc] using ih (K ⊗ X)
    have hStep := originalSourceSplitStep (K := K)
      (s := s) (e := e ≫ (P ◁ t)) (c := c ≫ (d ▷ (K ⊗ X))) h
    have hTarget : (d ▷ (K ⊗ X)) ≫ (α_ (P ⊗ Q) K X).inv =
        (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv ≫
          (d ▷ K ▷ X) :=
      associator_inv_naturality_left d K X
    have h1 : s ≫ e ≫ (P ◁ t) ≫ (P ◁ (α_ Q K X).inv) ≫ (α_ P (Q ⊗ K) X).inv =
        c ≫ (d ▷ (K ⊗ X)) ≫ (α_ (P ⊗ Q) K X).inv ≫ ((α_ P Q K).hom ▷ X) := by
      simpa only [Category.assoc] using hStep
    have h2 : c ≫ (d ▷ (K ⊗ X)) ≫ (α_ (P ⊗ Q) K X).inv ≫ ((α_ P Q K).hom ▷ X) =
        c ≫ (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv ≫
          (d ▷ K ▷ X) ≫ ((α_ P Q K).hom ▷ X) := by
      simpa only [Category.assoc] using congrArg
        (fun z => c ≫ z ≫ ((α_ P Q K).hom ▷ X)) hTarget
    have hNormalized : s ≫ e ≫ (P ◁ (t ≫ (α_ Q K X).inv)) ≫
        (α_ P (Q ⊗ K) X).inv =
        (c ≫ (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv) ≫
          (((d ▷ K) ≫ (α_ P Q K).hom) ▷ X) := by
      simpa only [whiskerLeft_comp, comp_whiskerRight, Category.assoc] using h1.trans h2
    have hLeftWhole :
        eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd K b (a + 1)) X) ≫
          (originalTensorSourcePowerValue K b ((originalTensorSourcePower K (a + 1)).obj X)).hom ≫
          (P ◁ (originalTensorSourcePowerValue K (a + 1) X).hom) ≫
          (α_ P (MonoidalCategory.TensorPower.tensorPowObj K (a + 1)) X).inv =
        s ≫ e ≫ (P ◁ (t ≫ (α_ Q K X).inv)) ≫ (α_ P (Q ⊗ K) X).inv := by
      rw [originalTensorSourcePowerValueSucc]
      rfl
    have hRightWhole :
        (originalTensorSourcePowerValue K (b + (a + 1)) X).hom ≫
          ((MonoidalCategory.TensorPower.tensorPowObj_add K b (a + 1)).hom ▷ X) =
        (c ≫ (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv) ≫
          (((d ▷ K) ≫ (α_ P Q K).hom) ▷ X) := by
      have hValue : (originalTensorSourcePowerValue K (b + (a + 1)) X).hom =
          c ≫ (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv :=
        congrArg Iso.hom (originalTensorSourcePowerValueSucc K (b + a) X)
      have hAdd : (MonoidalCategory.TensorPower.tensorPowObj_add K b (a + 1)).hom =
          (d ▷ K) ≫ (α_ P Q K).hom := by
        simp only [originalTensorPowerAddSucc, Iso.trans_hom, tensorIso_hom,
          Iso.refl_hom, tensorHom_id]
        rfl
      exact (congrArg (fun z => z ≫
          ((MonoidalCategory.TensorPower.tensorPowObj_add K b (a + 1)).hom ▷ X)) hValue).trans
        (congrArg (fun z =>
          (c ≫ (α_ (MonoidalCategory.TensorPower.tensorPowObj K (b + a)) K X).inv) ≫
            (z ▷ X)) hAdd)
    exact hLeftWhole.trans (hNormalized.trans hRightWhole.symm)



/-- The same full Iso maps retain a genuine source equality through postcomposition. -/
theorem originalIsoTrans_heq {D : Type*} [Category D] {A B T U : D}
    (h : A = B) (e : A ≅ T) (f : B ≅ T) (g : T ≅ U) (j : HEq e f) :
    HEq (e ≪≫ g) (f ≪≫ g) := by
  subst B
  cases j
  rfl

/-- The full original Iso Hom functions retain a genuine source equality through postcomposition. -/
theorem originalIsoHomComp_heq {D : Type*} [Category D] {A B T U : D}
    (h : A = B) (e : A ≅ T) (f : B ≅ T) (g : T ⟶ U) (j : HEq e f) :
    HEq (e.hom ≫ g) (f.hom ≫ g) := by
  subst B
  cases j
  rfl

/-- Both actual equality arrows preserve the same source and target endpoints. -/
theorem originalEqToHom_heq {D : Type*} [Category D] {A A' B B' : D}
    (hA : A = A') (hB : B = B') (h : A = B) (j : A' = B') :
    HEq (eqToHom h) (eqToHom j) := by
  subst A'
  subst B'
  have hj : h = j := Subsingleton.elim _ _
  cases hj
  rfl

section OriginalSphereSpecialization
open PointedCGWH.SphereHom

/-- The entire generic recursor specializes to the actual original one-sphere suspension power. -/
theorem originalTensorSourcePower_eq_sphere (n : ℕ) :
    originalTensorSourcePower PointedCGWH.sphereOne.{u, v} n = sphereTensorPower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (MonoidalCategory.tensorLeft PointedCGWH.sphereOne) ⋙
      originalTensorSourcePower PointedCGWH.sphereOne n = PointedCGWH.suspension ⋙ sphereTensorPower n
    exact congrArg (fun F => PointedCGWH.suspension ⋙ F) ih

/-- The actual whole power commutes with its original one-sphere suspension factor. -/
theorem originalSphereTensorPower_commuteSuspension (n : ℕ) :
    sphereTensorPower.{u, v} n ⋙ PointedCGWH.suspension =
      PointedCGWH.suspension ⋙ sphereTensorPower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (PointedCGWH.suspension ⋙ sphereTensorPower n) ⋙ PointedCGWH.suspension =
      PointedCGWH.suspension ⋙ (PointedCGWH.suspension ⋙ sphereTensorPower n)
    exact congrArg (fun F => PointedCGWH.suspension ⋙ F) ih

/-- Both entire actual successor source functors retain the same original suspension maps. -/
theorem originalSphereTensorPowerSuccRight (n : ℕ) :
    sphereTensorPower.{u, v} (n + 1) = sphereTensorPower n ⋙ PointedCGWH.suspension :=
  (originalSphereTensorPower_commuteSuspension n).symm

/-- The whole actual ordered sum of powers keeps its original source-side map order. -/
theorem originalSphereTensorPowerOrderedAdd (b a : ℕ) :
    sphereTensorPower.{u, v} (b + a) = sphereTensorPower a ⋙ sphereTensorPower b := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change sphereTensorPower (b + a + 1) =
      (PointedCGWH.suspension ⋙ sphereTensorPower a) ⋙ sphereTensorPower b
    rw [sphereTensorPowerSucc]
    exact (congrArg (fun F => PointedCGWH.suspension ⋙ F) ih)


/-- Both original suspension recursors retain the full dependent value-Iso family. -/
theorem originalTensorSourcePowerValue_heq_sphere (n : ℕ) (X : PointedCGWH.{u, v}) :
    HEq (originalTensorSourcePowerValue PointedCGWH.sphereOne n X)
      (spherePowerValueIso n X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    have h := ih (PointedCGWH.suspension.obj X)
    have hSource :
        (originalTensorSourcePower PointedCGWH.sphereOne n).obj (PointedCGWH.suspension.obj X) =
        (sphereTensorPower n).obj (PointedCGWH.suspension.obj X) :=
      Functor.congr_obj (originalTensorSourcePower_eq_sphere n) (PointedCGWH.suspension.obj X)
    have hStep :
        HEq ((originalTensorSourcePowerValue PointedCGWH.sphereOne n
          (PointedCGWH.suspension.obj X)) ≪≫
          (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)
            PointedCGWH.sphereOne X).symm)
          ((spherePowerValueIso n (PointedCGWH.suspension.obj X)) ≪≫
          (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)
            PointedCGWH.sphereOne X).symm) := by
      exact originalIsoTrans_heq hSource _ _ _ h
    exact hStep

/-- Actual endpoint equality inserts the full source equality-Iso and keeps both original maps. -/
theorem originalIso_eqToIso_of_heq {D : Type*} [Category D] {A B T : D}
    (h : A = B) (e : A ≅ T) (f : B ≅ T) (j : HEq e f) :
    e = eqToIso h ≪≫ f := by
  subst B
  have hSame := eq_of_heq j
  exact hSame.trans (Iso.refl_trans f).symm

/-- The full generic source value comparison is the actual original sphere value Iso after its exact source map. -/
theorem originalTensorSourcePowerValue_eq_sphere (n : ℕ) (X : PointedCGWH.{u, v}) :
    originalTensorSourcePowerValue PointedCGWH.sphereOne n X =
      eqToIso (Functor.congr_obj (originalTensorSourcePower_eq_sphere n) X) ≪≫
        spherePowerValueIso n X :=
  originalIso_eqToIso_of_heq
    (Functor.congr_obj (originalTensorSourcePower_eq_sphere n) X) _ _
    (originalTensorSourcePowerValue_heq_sphere n X)

/-- The same complete source word retains both actual value Isos through genuine source equality. -/
theorem originalValueSplitWord_heq {D : Type*} [Category D] [MonoidalCategory D]
    {A A' B B' T U P Q X : D}
    (hA : A = A') (hB : B = B') (hT : T = U)
    (s : A ⟶ B) (s' : A' ⟶ B')
    (e : B ≅ P ⊗ T) (e' : B' ≅ P ⊗ U)
    (f : T ≅ Q ⊗ X) (f' : U ≅ Q ⊗ X)
    (hs : HEq s s') (he : HEq e e') (hf : HEq f f') :
    HEq (s ≫ e.hom ≫ (P ◁ f.hom) ≫ (α_ P Q X).inv)
      (s' ≫ e'.hom ≫ (P ◁ f'.hom) ≫ (α_ P Q X).inv) := by
  subst A'
  subst B'
  subst U
  cases hs
  cases he
  cases hf
  rfl

/-- The actual complete original sphere split is the full tensor addition map in its ordered degree. -/
theorem originalSpherePowerValueIso_ordered_add (b a : ℕ) (X : PointedCGWH.{u, v}) :
    eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd b a) X) ≫
        (spherePowerValueIso b ((sphereTensorPower a).obj X)).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b ◁
          (spherePowerValueIso a X).hom) ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b)
          (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne a) X).inv =
      (spherePowerValueIso (b + a) X).hom ≫
        ((MonoidalCategory.TensorPower.tensorPowObj_add PointedCGWH.sphereOne b a).hom ▷ X) := by
  have h := originalTensorSourcePowerValueAdd PointedCGWH.sphereOne b a X
  have hFull : HEq
      (eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd PointedCGWH.sphereOne b a) X) ≫
        (originalTensorSourcePowerValue PointedCGWH.sphereOne b
          ((originalTensorSourcePower PointedCGWH.sphereOne a).obj X)).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b ◁
          (originalTensorSourcePowerValue PointedCGWH.sphereOne a X).hom) ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b)
          (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne a) X).inv)
      (eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd b a) X) ≫
        (spherePowerValueIso b ((sphereTensorPower a).obj X)).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b ◁
          (spherePowerValueIso a X).hom) ≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b)
          (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne a) X).inv) := by
    have hA := Functor.congr_obj (originalTensorSourcePower_eq_sphere (b + a)) X
    have hInner := Functor.congr_obj (originalTensorSourcePower_eq_sphere a) X
    have hB :
        (originalTensorSourcePower PointedCGWH.sphereOne b).obj
          ((originalTensorSourcePower PointedCGWH.sphereOne a).obj X) =
        (sphereTensorPower b).obj ((sphereTensorPower a).obj X) :=
      (Functor.congr_obj (originalTensorSourcePower_eq_sphere b)
        ((originalTensorSourcePower PointedCGWH.sphereOne a).obj X)).trans
          (congrArg (sphereTensorPower b).obj hInner)
    have hCast :
        HEq (eqToHom (Functor.congr_obj (originalTensorSourcePowerAdd PointedCGWH.sphereOne b a) X))
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd b a) X)) := by
      exact originalEqToHom_heq hA hB _ _
    have hEval :
        HEq (originalTensorSourcePowerValue PointedCGWH.sphereOne b
          ((originalTensorSourcePower PointedCGWH.sphereOne a).obj X))
          (spherePowerValueIso b ((sphereTensorPower a).obj X)) :=
      (originalTensorSourcePowerValue_heq_sphere b
        ((originalTensorSourcePower PointedCGWH.sphereOne a).obj X)).trans
          ((show ∀ {Y Z : PointedCGWH.{u, v}}, Y = Z →
            HEq (spherePowerValueIso b Y) (spherePowerValueIso b Z) from
            fun h => by cases h; rfl) hInner)
    exact originalValueSplitWord_heq hA hB hInner _ _ _ _ _ _ hCast hEval
      (originalTensorSourcePowerValue_heq_sphere a X)
  have hRight : HEq
      ((originalTensorSourcePowerValue PointedCGWH.sphereOne (b + a) X).hom ≫
        ((MonoidalCategory.TensorPower.tensorPowObj_add PointedCGWH.sphereOne b a).hom ▷ X))
      ((spherePowerValueIso (b + a) X).hom ≫
        ((MonoidalCategory.TensorPower.tensorPowObj_add PointedCGWH.sphereOne b a).hom ▷ X)) := by
    exact originalIsoHomComp_heq
      (Functor.congr_obj (originalTensorSourcePower_eq_sphere (b + a)) X) _ _ _
        (originalTensorSourcePowerValue_heq_sphere (b + a) X)
  exact eq_of_heq (hFull.symm.trans ((heq_of_eq h).trans hRight))

end OriginalSphereSpecialization

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaPowerValues

section NativeGammaLoopPowerClass


set_option autoImplicit false
noncomputable section
universe u v u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open PointedCGWH.SphereHom PointedCGWH.NativeLoopShiftGeometry
open HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

theorem sameSphereWhiskeredCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : C ⥤ D) {P R : C ⥤ C} (h : P = R) (X : C) :
    (Functor.isoWhiskerRight (eqToIso h) Q).hom.app X =
      Q.map (eqToHom (Functor.congr_obj h X)) := by
  change Q.map ((eqToHom h).app X) = _
  exact congrArg Q.map (eqToHom_app h X)

theorem sameSphereWhiskeredInverseCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : C ⥤ D) {P R : C ⥤ C} (h : P = R) (X : C) :
    (Functor.isoWhiskerRight (eqToIso h).symm Q).hom.app X =
      Q.map (eqToHom (Functor.congr_obj h.symm X)) :=
  sameSphereWhiskeredCastHom Q h.symm X

theorem sameSphereCoefficientCastHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (Q : ℕ → (C ⥤ D)) {a b : ℕ} (h : a = b) (X : C) :
    (eqToIso (congrArg Q h)).hom.app X =
      eqToHom (congrArg (fun j => (Q j).obj X) h) :=
  eqToHom_app (congrArg Q h) X

theorem sameSphereGradedShiftZeroHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n)) (hP0 : P 0 = 𝟭 C)
    (hZero : ∀ k, H 0 k =
      Functor.isoWhiskerRight (eqToIso hP0) (Q k) ≪≫ (Q k).leftUnitor)
    (k : ℕ) (X : C) :
    (H 0 k).hom.app X = (Q k).map (eqToHom (Functor.congr_obj hP0 X)) := by
  exact (congrArg (fun e => e.hom.app X) (hZero k)).trans
    ((congrArg (fun f => f ≫ 𝟙 ((Q k).obj X)) (sameSphereWhiskeredCastHom (Q k) hP0 X)).trans
      (Category.comp_id _))

theorem sameSphereGradedShiftSuccessorHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ C) (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (S : ∀ k, L ⋙ Q k ≅ Q (k + 1))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n))
    (hPSucc : ∀ n, P (n + 1) = P n ⋙ L)
    (hSucc : ∀ n k, H (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (hPSucc n)) (Q k) ≪≫
        Functor.associator (P n) L (Q k) ≪≫
        Functor.isoWhiskerLeft (P n) (S k) ≪≫ H n (k + 1) ≪≫
        eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega)))
    (n k : ℕ) (X : C) :
    (H (n + 1) k).hom.app X =
      (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
        (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫
          eqToHom (congrArg (fun j => (Q j).obj X)
            (show k + 1 + n = k + (n + 1) by omega)) := by
  have h := congrArg (fun e => e.hom.app X) (hSucc n k)
  have hBody : (H (n + 1) k).hom.app X =
      (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
        (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫
          (eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega))).hom.app X := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, sameSphereWhiskeredCastHom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] using h
  exact hBody.trans (congrArg (fun f =>
    (Q k).map (eqToHom (Functor.congr_obj (hPSucc n) X)) ≫
      (S k).hom.app ((P n).obj X) ≫ (H n (k + 1)).hom.app X ≫ f)
        (sameSphereCoefficientCastHom Q
          (show k + 1 + n = k + (n + 1) by omega) X))

theorem sameSphereAssociatedShiftHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P R : C ⥤ C) (Q : C ⥤ D) {A B B' : C ⥤ D}
    (h : R ⋙ Q ≅ A) (j : P ⋙ A ≅ B) (e : B = B') (X : C) :
    (Functor.associator P R Q ≪≫ Functor.isoWhiskerLeft P h ≪≫ j ≪≫ eqToIso e).hom.app X =
      h.hom.app (P.obj X) ≫ j.hom.app X ≫ eqToHom (Functor.congr_obj e X) := by
  change 𝟙 _ ≫ h.hom.app (P.obj X) ≫ j.hom.app X ≫ (eqToHom e).app X = _
  exact (Category.id_comp _).trans (congrArg
    (fun f => h.hom.app (P.obj X) ≫ j.hom.app X ≫ f) (eqToHom_app e X))

theorem sameSphereGradedShiftReindexHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n)) (n : ℕ) {a b : ℕ} (h : a = b) (X : C) :
    eqToHom (congrArg (fun j => (Q j).obj ((P n).obj X)) h) ≫ (H n b).hom.app X =
      (H n a).hom.app X ≫ eqToHom (congrArg (fun j => (Q (j + n)).obj X) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sameSphereWholeGradedShiftAssociationHom
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (L : C ⥤ C) (P : ℕ → (C ⥤ C)) (Q : ℕ → (C ⥤ D))
    (S : ∀ k, L ⋙ Q k ≅ Q (k + 1))
    (H : ∀ n k, P n ⋙ Q k ≅ Q (k + n))
    (hP0 : P 0 = 𝟭 C) (hPSucc : ∀ n, P (n + 1) = P n ⋙ L)
    (hPAdd : ∀ n m, P (n + m) = P n ⋙ P m)
    (hZero : ∀ k, H 0 k =
      Functor.isoWhiskerRight (eqToIso hP0) (Q k) ≪≫ (Q k).leftUnitor)
    (hSucc : ∀ n k, H (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (hPSucc n)) (Q k) ≪≫
        Functor.associator (P n) L (Q k) ≪≫
        Functor.isoWhiskerLeft (P n) (S k) ≪≫ H n (k + 1) ≪≫
        eqToIso (congrArg Q (show k + 1 + n = k + (n + 1) by omega)))
    (n m k : ℕ) (X : C) :
    (Q k).map (eqToHom (Functor.congr_obj (hPAdd n m).symm X)) ≫
        (H (n + m) k).hom.app X =
      (H m k).hom.app ((P n).obj X) ≫ (H n (k + m)).hom.app X ≫
        eqToHom (congrArg (fun j => (Q j).obj X)
          (show k + m + n = k + (n + m) by omega)) := by
  induction m generalizing k X with
  | zero =>
    have hCast : eqToHom (Functor.congr_obj (hPAdd n 0).symm X) =
        eqToHom (Functor.congr_obj hP0 ((P n).obj X)) := rfl
    have hZeroHom := sameSphereGradedShiftZeroHom P Q H hP0 hZero k ((P n).obj X)
    change (Q k).map _ ≫ (H n k).hom.app X =
      (H 0 k).hom.app ((P n).obj X) ≫ (H n k).hom.app X ≫ 𝟙 _
    rw [hCast, ← hZeroHom, Category.comp_id]
  | succ m hm =>
    let c : (P m).obj ((P n).obj X) ⟶ (P (n + m)).obj X :=
      eqToHom (Functor.congr_obj (hPAdd n m).symm X)
    let e : (P ((n + m) + 1)).obj X ⟶ L.obj ((P (n + m)).obj X) :=
      eqToHom (Functor.congr_obj (hPSucc (n + m)) X)
    let d : (P (m + 1)).obj ((P n).obj X) ⟶ L.obj ((P m).obj ((P n).obj X)) :=
      eqToHom (Functor.congr_obj (hPSucc m) ((P n).obj X))
    let cNext : (P (m + 1)).obj ((P n).obj X) ⟶ (P (n + (m + 1))).obj X :=
      eqToHom (Functor.congr_obj (hPAdd n (m + 1)).symm X)
    have hCast : cNext ≫ e = d ≫ L.map c := by
      change eqToHom _ ≫ eqToHom _ = eqToHom _ ≫ L.map (eqToHom _)
      rw [eqToHom_map, eqToHom_trans, eqToHom_trans]
    have hCastQ : (Q k).map cNext ≫ (Q k).map e =
        (Q k).map d ≫ (Q k).map (L.map c) :=
      ((Q k).map_comp cNext e).symm.trans
        ((congrArg (Q k).map hCast).trans ((Q k).map_comp d (L.map c)))
    have hNatural : (Q k).map (L.map c) ≫ (S k).hom.app ((P (n + m)).obj X) =
        (S k).hom.app ((P m).obj ((P n).obj X)) ≫ (Q (k + 1)).map c :=
      (S k).hom.naturality c
    let cIH := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + 1 + m + n = k + 1 + (n + m) by omega))
    let cSum := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + 1 + (n + m) = k + ((n + m) + 1) by omega))
    have hDegree : k + 1 + m = k + (m + 1) := by omega
    let cM := eqToHom (congrArg (fun j => (Q j).obj ((P n).obj X)) hDegree)
    let cN := eqToHom (congrArg (fun j => (Q (j + n)).obj X) hDegree)
    let cTotal := eqToHom (congrArg (fun j => (Q j).obj X)
      (show k + (m + 1) + n = k + (n + (m + 1)) by omega))
    have hPaths : cIH ≫ cSum = cN ≫ cTotal := by
      change eqToHom _ ≫ eqToHom _ = eqToHom _ ≫ eqToHom _
      rw [eqToHom_trans, eqToHom_trans]
    have hReindex : cM ≫ (H n (k + (m + 1))).hom.app X =
        (H n (k + 1 + m)).hom.app X ≫ cN :=
      sameSphereGradedShiftReindexHom P Q H n hDegree X
    have hIH : (Q (k + 1)).map c ≫ (H (n + m) (k + 1)).hom.app X =
        (H m (k + 1)).hom.app ((P n).obj X) ≫
          (H n (k + 1 + m)).hom.app X ≫ cIH := hm (k + 1) X
    have hSum : (H ((n + m) + 1) k).hom.app X =
        (Q k).map e ≫ (S k).hom.app ((P (n + m)).obj X) ≫
          (H (n + m) (k + 1)).hom.app X ≫ cSum :=
      sameSphereGradedShiftSuccessorHom L P Q S H hPSucc hSucc (n + m) k X
    have hM : (H (m + 1) k).hom.app ((P n).obj X) =
        (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫ cM :=
      sameSphereGradedShiftSuccessorHom L P Q S H hPSucc hSucc m k ((P n).obj X)
    calc
      (Q k).map cNext ≫ (H ((n + m) + 1) k).hom.app X =
          (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            ((Q (k + 1)).map c ≫ (H (n + m) (k + 1)).hom.app X) ≫ cSum := by
        rw [hSum]
        rw [← Category.assoc ((Q k).map cNext) ((Q k).map e)
          ((S k).hom.app ((P (n + m)).obj X) ≫
            (H (n + m) (k + 1)).hom.app X ≫ cSum), hCastQ, Category.assoc]
        rw [← Category.assoc ((Q k).map (L.map c)) ((S k).hom.app ((P (n + m)).obj X))
          ((H (n + m) (k + 1)).hom.app X ≫ cSum), hNatural]
        simp only [Category.assoc]
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            (H n (k + 1 + m)).hom.app X ≫ cIH ≫ cSum := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫ a ≫ cSum) hIH
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            (H n (k + 1 + m)).hom.app X ≫ cN ≫ cTotal := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            (H m (k + 1)).hom.app ((P n).obj X) ≫ (H n (k + 1 + m)).hom.app X ≫ a) hPaths
      _ = (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
          (H m (k + 1)).hom.app ((P n).obj X) ≫
            cM ≫ (H n (k + (m + 1))).hom.app X ≫ cTotal := by
        simpa only [Category.assoc] using congrArg
          (fun a => (Q k).map d ≫ (S k).hom.app ((P m).obj ((P n).obj X)) ≫
            (H m (k + 1)).hom.app ((P n).obj X) ≫ a ≫ cTotal) hReindex.symm
      _ = (H (m + 1) k).hom.app ((P n).obj X) ≫
          (H n (k + (m + 1))).hom.app X ≫ cTotal := by
        simpa only [Category.assoc] using
          congrArg (fun a => a ≫ (H n (k + (m + 1))).hom.app X ≫ cTotal) hM.symm

section ActualAllDegreeSphereLoop
open PointedCGWH.SphereHom PointedCGWH.NativeLoopShiftGeometry

/-- The whole original all-degree zero comparison keeps its actual left unitor. -/
theorem sameSphereLoopPiZeroClause (k : ℕ) :
    loopPowerPiShift.{u, v} 0 k =
      Functor.isoWhiskerRight (eqToIso (show loopPower 0 = 𝟭 PointedCGWH.{u, v} from rfl))
        (PointedCGWH.piNFunctor k) ≪≫ (PointedCGWH.piNFunctor k).leftUnitor := by
  change (PointedCGWH.piNFunctor k).leftUnitor =
    Functor.isoWhiskerRight (Iso.refl (𝟭 PointedCGWH.{u, v})) (PointedCGWH.piNFunctor k) ≪≫
      (PointedCGWH.piNFunctor k).leftUnitor
  rw [Functor.isoWhiskerRight_refl, Iso.refl_trans]

/-- The whole original all-degree successor retains its actual native shift and degree transport. -/
theorem sameSphereLoopPiSuccClause (n k : ℕ) :
    loopPowerPiShift.{u, v} (n + 1) k =
      Functor.isoWhiskerRight (eqToIso (show loopPower (n + 1) = loopPower n ⋙ PointedCGWH.loop from rfl))
        (PointedCGWH.piNFunctor k) ≪≫
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
      Functor.isoWhiskerLeft (loopPower n) (nativeLoopPiShiftNatIso k) ≪≫
      loopPowerPiShift n (k + 1) ≪≫ eqToIso (congrArg PointedCGWH.piNFunctor
        (show k + 1 + n = k + (n + 1) by omega)) := by
  have hPrefix : Functor.isoWhiskerRight
      (eqToIso (show loopPower (n + 1) = loopPower n ⋙ PointedCGWH.loop from rfl))
      (PointedCGWH.piNFunctor k) =
      Iso.refl ((loopPower n ⋙ PointedCGWH.loop) ⋙ PointedCGWH.piNFunctor k) :=
    Functor.isoWhiskerRight_refl _ _
  let b : (loopPower n ⋙ PointedCGWH.loop) ⋙ PointedCGWH.piNFunctor k ≅
      PointedCGWH.piNFunctor (k + (n + 1)) :=
    Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
      Functor.isoWhiskerLeft (loopPower n) (nativeLoopPiShiftNatIso k) ≪≫
      loopPowerPiShift n (k + 1) ≪≫ eqToIso (congrArg PointedCGWH.piNFunctor
        (show k + 1 + n = k + (n + 1) by omega))
  have hOriginal : loopPowerPiShift (n + 1) k = b := rfl
  have hWhole : Functor.isoWhiskerRight
      (eqToIso (show loopPower (n + 1) = loopPower n ⋙ PointedCGWH.loop from rfl))
      (PointedCGWH.piNFunctor k) ≪≫ b = b :=
    (congrArg (fun e => e ≪≫ b) hPrefix).trans (Iso.refl_trans b)
  exact hOriginal.trans hWhole.symm

/-- Both complete all-degree native loop-shift functions preserve the original ordered power split. -/
theorem sameSphereLoopPiAssociationHom (n m k : ℕ) (X : PointedCGWH.{u, v}) :
    (PointedCGWH.piNFunctor k).map
        (eqToHom (Functor.congr_obj ((congrArg loopPower (Nat.add_comm n m)).trans
          (originalLoopPowerAdd m n)).symm X)) ≫
      (loopPowerPiShift (n + m) k).hom.app X =
    (loopPowerPiShift m k).hom.app ((loopPower n).obj X) ≫
      (loopPowerPiShift n (k + m)).hom.app X ≫
      eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj X)
        (show k + m + n = k + (n + m) by omega)) := by
  have hAdd : ∀ n m : ℕ, loopPower.{u, v} (n + m) = loopPower n ⋙ loopPower m := by
    intro n m
    exact (congrArg loopPower (Nat.add_comm n m)).trans (originalLoopPowerAdd m n)
  exact sameSphereWholeGradedShiftAssociationHom PointedCGWH.loop loopPower PointedCGWH.piNFunctor
    nativeLoopPiShiftNatIso loopPowerPiShift rfl (fun _ => rfl) hAdd
    sameSphereLoopPiZeroClause sameSphereLoopPiSuccClause n m k X
/-- The actual Type equality arrow is the complete original cast function. -/
theorem originalTypeEqToHom_apply {A B : Type v} (h : A = B) (x : A) :
    (eqToHom h) x = Equiv.cast h x := by
  cases h
  rfl

/-- The complete original composite Type-arrow function retains every actual factor. -/
theorem originalTypeComp_apply {A B D E : Type v}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (x : A) :
    (f ≫ g ≫ h) x = h (g (f x)) := rfl

/-- The original associated zero-loop comparison is the same full all-degree shift function. -/
theorem sameSphereZeroLoopPowerAssociation (n d : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN 0 ((loopPower d).obj ((loopPower n).obj X))) :
    zeroLoopPowerPiShift (n + d) X
      (PointedCGWH.piNMap 0
        (eqToHom (Functor.congr_obj ((congrArg loopPower (Nat.add_comm n d)).trans
          (originalLoopPowerAdd d n)).symm X)) x) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show d + n = n + d by omega)))
        (((loopPowerPiShift n d).app X).toEquiv
          (zeroLoopPowerPiShift d ((loopPower n).obj X) x)) := by
  have h := ConcreteCategory.congr_hom (sameSphereLoopPiAssociationHom n d 0 X) x
  have hNatCast : ∀ {a b : ℕ} (h : a = b)
      (z : PointedCGWH.piN a ((loopPower n).obj X)),
      (((loopPowerPiShift n b).app X).toEquiv)
        ((Equiv.cast (congrArg (fun j => PointedCGWH.piN j ((loopPower n).obj X)) h)) z) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN (j + n) X) h))
        ((((loopPowerPiShift n a).app X).toEquiv) z) := by
    intro a b h z
    cases h
    rfl
  have hCast : ∀ {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c)
      (z : PointedCGWH.piN a X),
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h₂))
        ((Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h₁)) z) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h₃)) z := by
    intro a b c h₁ h₂ h₃ z
    cases h₁
    cases h₂
    rfl
  have hRaw :
      ((loopPowerPiShift (n + d) 0).app X).toEquiv
        (PointedCGWH.piNMap 0
          (eqToHom (Functor.congr_obj ((congrArg loopPower (Nat.add_comm n d)).trans
            (originalLoopPowerAdd d n)).symm X)) x) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
          (show 0 + d + n = 0 + (n + d) by omega)))
        (((loopPowerPiShift n (0 + d)).app X).toEquiv
          (((loopPowerPiShift d 0).app ((loopPower n).obj X)).toEquiv x)) := by
    have hCastArrow := originalTypeEqToHom_apply
      (congrArg (fun j => (PointedCGWH.piNFunctor j).obj X)
        (show 0 + d + n = 0 + (n + d) by omega))
      (((loopPowerPiShift n (0 + d)).app X).toEquiv
        (((loopPowerPiShift d 0).app ((loopPower n).obj X)).toEquiv x))
    exact h.trans hCastArrow
  have hRawCast := congrArg
    (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) (Nat.zero_add (n + d)))) hRaw
  have hDegree := hNatCast (Nat.zero_add d)
    (((loopPowerPiShift d 0).app ((loopPower n).obj X)).toEquiv x)
  let z := ((loopPowerPiShift d 0).app ((loopPower n).obj X)).toEquiv x
  let w := ((loopPowerPiShift n (0 + d)).app X).toEquiv z
  have hFirst :
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) (Nat.zero_add (n + d))))
        ((Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
            (show 0 + d + n = 0 + (n + d) by omega))) w) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show 0 + d + n = n + d by omega))) w :=
    hCast (show 0 + d + n = 0 + (n + d) by omega)
      (Nat.zero_add (n + d)) (show 0 + d + n = n + d by omega) w
  have hSecond :
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) (Nat.add_comm d n)))
        (((loopPowerPiShift n d).app X).toEquiv
          ((Equiv.cast (congrArg (fun j => PointedCGWH.piN j ((loopPower n).obj X))
            (Nat.zero_add d))) z)) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show 0 + d + n = n + d by omega))) w := by
    have h := congrArg
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) (Nat.add_comm d n))) hDegree
    exact h.trans (hCast (congrArg (fun j => j + n) (Nat.zero_add d))
      (Nat.add_comm d n) (show 0 + d + n = n + d by omega) w)
  exact hRawCast.trans (hFirst.trans hSecond.symm)

end ActualAllDegreeSphereLoop
section EntireQuillenComposition
universe uC vC uD vD uE vE

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  {M : D ⥤ E} {S : E ⥤ D} (b : M ⊣ S) [b.IsQuillenAdjunction]

/-- Both original full localized Hom functions compose on the original Quillen pair. -/
theorem quillenHoHomComposition (X : C) [IsCofibrant X] (Y : E) [IsFibrant Y] :
    letI : IsCofibrant (L.obj X) :=
      Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := a) inferInstance
    letI : IsFibrant (S.obj Y) :=
      Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := b) inferInstance
    QuillenOrdinaryHoHom.homEquiv (a.comp b) X Y =
      (QuillenOrdinaryHoHom.homEquiv b (L.obj X) Y).trans
        (QuillenOrdinaryHoHom.homEquiv a X (S.obj Y)) := by
  let _ : IsCofibrant (L.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := a) inferInstance
  let _ : IsCofibrant (M.obj (L.obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := b) inferInstance
  let _ : IsFibrant (S.obj Y) :=
    Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := b) inferInstance
  apply Equiv.ext
  intro g
  obtain ⟨f, hf⟩ := map_surjective_of_isLocalization (HomotopicalAlgebra.toHomotopyCategory E)
    (M.obj (L.obj X)) Y g
  subst g
  simp only [Equiv.trans_apply, QuillenOrdinaryHoHom.homEquiv_map]
  have h := congrFun (congrFun (Adjunction.comp_homEquiv a b) X) Y
  exact congrArg (fun e : (M.obj (L.obj X) ⟶ Y) ≃ (X ⟶ R.obj (S.obj Y)) =>
    (HomotopicalAlgebra.toHomotopyCategory C).map (e f)) h

end EntireQuillenComposition

section OriginalScalarPowers

open PointedCGWH.SphereHom

attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant

private instance originalFreePointCofibrant : IsCofibrant freePoint.{u, v} := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant

private instance originalSphereCofibrant (d : ℕ) : IsCofibrant (sphere.{u, v} d) :=
  FreeSphereHom.sphere_isCofibrant d

/-- The actual composed sphere adjunction keeps both original power-Hom
functions at the freely pointed source and arbitrary original endpoint. -/
theorem originalPowerHoHomComposition (d n : ℕ) (X : PointedCGWH.{u, v}) :
    QuillenOrdinaryHoHom.homEquiv ((powerAdjunction d).comp (powerAdjunction n))
        freePoint X =
      (QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) (sphere d) X).trans
        (QuillenOrdinaryHoHom.homEquiv (powerAdjunction d) freePoint
          ((loopPower n).obj X)) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  let _ : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
  let _ : IsFibrant ((loopPower n).obj X) := inferInstance
  exact quillenHoHomComposition (powerAdjunction d) (powerAdjunction n) freePoint X

end OriginalScalarPowers


end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaLoopPowerClass

section NativeGammaSpherePowerClass


set_option autoImplicit false
noncomputable section
universe u v uC vC uD vD
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

section QuillenHomTransport
variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L M : C ⥤ D} {R S : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenAdjunction]

theorem originalQuillenHomIsoTransport (e : L ≅ M) (j : R ≅ S)
    (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y]
    (f : (HomotopicalAlgebra.toHomotopyCategory D).obj (M.obj X) ⟶ (HomotopicalAlgebra.toHomotopyCategory D).obj Y) :
    QuillenOrdinaryHoHom.homEquiv ((adj.ofNatIsoLeft e).ofNatIsoRight j) X Y f =
      QuillenOrdinaryHoHom.homEquiv adj X Y
        ((HomotopicalAlgebra.toHomotopyCategory D).map (e.hom.app X) ≫ f) ≫
      (HomotopicalAlgebra.toHomotopyCategory C).map (j.hom.app Y) := by
  let _ : IsCofibrant (M.obj X) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := (adj.ofNatIsoLeft e).ofNatIsoRight j) inferInstance
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization (HomotopicalAlgebra.toHomotopyCategory D) (M.obj X) Y f
  rw [QuillenOrdinaryHoHom.homEquiv_map, ← Functor.map_comp,
    QuillenOrdinaryHoHom.homEquiv_map]
  have hRight := Adjunction.homEquiv_ofNatIsoRight_apply (adj.ofNatIsoLeft e) j g
  have hLeft := Adjunction.homEquiv_ofNatIsoLeft_apply adj e g
  exact ((HomotopicalAlgebra.toHomotopyCategory C).congr_map
    (hRight.trans (congrArg (fun z => z ≫ j.hom.app Y) hLeft))).trans
      ((HomotopicalAlgebra.toHomotopyCategory C).map_comp _ _)


end QuillenHomTransport
theorem originalQuillenHom_eq_of_adjunction_eq
    {C : Type uC} [Category.{vC} C] [ModelCategory C]
    {D : Type uD} [Category.{vD} D] [ModelCategory D]
    {L : C ⥤ D} {R : D ⥤ C} (adj other : L ⊣ R)
    [adj.IsQuillenAdjunction] [other.IsQuillenAdjunction] (h : adj = other)
    (X : C) [IsCofibrant X] (Y : D) [IsFibrant Y] :
    QuillenOrdinaryHoHom.homEquiv adj X Y = QuillenOrdinaryHoHom.homEquiv other X Y := by
  cases h
  rfl


attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant

theorem originalSphereHoHomPowerComposition (n d : ℕ) (X : PointedCGWH.{u, v})
    (f : (sphereTensorPower n).obj (sphere d) ⟶ X) :
    letI : IsCofibrant freePoint.{u, v} := by
      let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
        Under.costarAdjForget_isQuillenAdjunction CGWH.point
      exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
        (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
    letI : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
    sphereHoHomEquiv (d + n) X
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f)) ≫
      (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
        (eqToHom (Functor.congr_obj (originalLoopPowerAdd d n) X)) =
    sphereHoHomEquiv d ((loopPower n).obj X)
      (QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) (sphere d) X
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  let _ : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
  have hTransport := originalQuillenHomIsoTransport (powerAdjunction (d + n))
    (eqToIso (originalSphereTensorPowerAdd d n)) (eqToIso (originalLoopPowerAdd d n))
    freePoint X ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)
  let _ : (originalTransportedPowerAdjunction d n).IsQuillenAdjunction := by
    change (((powerAdjunction (d + n)).ofNatIsoLeft
      (eqToIso (originalSphereTensorPowerAdd d n))).ofNatIsoRight
        (eqToIso (originalLoopPowerAdd d n))).IsQuillenAdjunction
    infer_instance
  have hAdj := originalSpherePowerAdjunctionAdd d n
  have hComp := originalPowerHoHomComposition d n X
  have hL : (eqToIso (originalSphereTensorPowerAdd d n)).hom.app freePoint =
      eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) :=
    eqToHom_app (originalSphereTensorPowerAdd d n) freePoint
  have hR : (eqToIso (originalLoopPowerAdd d n)).hom.app X =
      eqToHom (Functor.congr_obj (originalLoopPowerAdd d n) X) :=
    eqToHom_app (originalLoopPowerAdd d n) X
  have hWhole :
      QuillenOrdinaryHoHom.homEquiv ((powerAdjunction d).comp (powerAdjunction n)) freePoint X
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f) =
      sphereHoHomEquiv (d + n) X
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f)) ≫
        (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalLoopPowerAdd d n) X)) := by
    have hSame := originalQuillenHom_eq_of_adjunction_eq
      (originalTransportedPowerAdjunction d n) ((powerAdjunction d).comp (powerAdjunction n))
      hAdj freePoint X
    have hTransported :
        QuillenOrdinaryHoHom.homEquiv (originalTransportedPowerAdjunction d n) freePoint X
          ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f) =
        sphereHoHomEquiv (d + n) X
          ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
            (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f)) ≫
          (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
            (eqToHom (Functor.congr_obj (originalLoopPowerAdd d n) X)) := by
      have hSource : (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map ((eqToIso
          (originalSphereTensorPowerAdd d n)).hom.app freePoint) ≫
          (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f =
        (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f) :=
        (congrArg (fun z => (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map z ≫
          (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f) hL).trans
          ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map_comp _ _).symm
      have hTarget := (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).congr_map hR
      exact hTransport.trans (congrArg₂ (fun z t =>
        QuillenOrdinaryHoHom.homEquiv (powerAdjunction (d + n)) freePoint X z ≫ t)
          hSource hTarget)
    exact (congrArg (fun e => e ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) hSame).symm.trans
      hTransported
  exact hWhole.symm.trans (congrArg
    (fun e => e ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) hComp)
/-- Both complete inverse point-class functions retain every original pointed target map. -/
theorem originalPointClassInverse_naturality {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (g : (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).obj freePoint ⟶
      (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).obj A) :
    (PointedCGWH.piNZeroEquivPiZero B).symm
      ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv B).symm
        (g ≫ (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) =
    PointedCGWH.piNMap 0 f
      ((PointedCGWH.piNZeroEquivPiZero A).symm
        ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv A).symm g)) := by
  apply (PointedCGWH.piNZeroEquivPiZero B).injective
  rw [Equiv.apply_symm_apply,
    PointedCGWH.PointComponentHom.pointedPointClassHomEquiv_inverse_naturality,
    PointedCGWH.piNZeroEquivPiZero_naturality, Equiv.apply_symm_apply]

/-- The original full sphere class under a power adjunct retains the SAME pointed source and target map. -/
theorem originalSpherePiHomEquiv_power_adjunct (n d : ℕ) (X : PointedCGWH.{u, v})
    (f : (sphereTensorPower n).obj (sphere d) ⟶ X) :
    letI : IsCofibrant freePoint.{u, v} := by
      let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
        Under.costarAdjForget_isQuillenAdjunction CGWH.point
      exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
        (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
    letI : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
    (spherePiHomEquiv (d + n) X).symm
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f)) =
      ((loopPowerPiShift n d).app X).toEquiv
          ((spherePiHomEquiv d ((loopPower n).obj X)).symm
            (QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) (sphere d) X
              ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f))) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  let _ : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
  let eR := eqToHom (Functor.congr_obj (originalLoopPowerAdd d n) X)
  let h := QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) (sphere d) X
    ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)
  let z := (PointedCGWH.piNZeroEquivPiZero ((loopPower d).obj ((loopPower n).obj X))).symm
    ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv
      ((loopPower d).obj ((loopPower n).obj X))).symm
      (sphereHoHomEquiv d ((loopPower n).obj X) h))
  have hHo := originalSphereHoHomPowerComposition n d X f
  let whole := sphereHoHomEquiv (d + n) X
    ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
      (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f))
  let zWhole := (PointedCGWH.piNZeroEquivPiZero ((loopPower (d + n)).obj X)).symm
    ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv ((loopPower (d + n)).obj X)).symm whole)
  have hz : PointedCGWH.piNMap 0 eR zWhole = z := by
    have hPoint := originalPointClassInverse_naturality eR whole
    have hImage := congrArg (fun g =>
      (PointedCGWH.piNZeroEquivPiZero ((loopPower d).obj ((loopPower n).obj X))).symm
        ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv
          ((loopPower d).obj ((loopPower n).obj X))).symm g)) hHo
    exact hPoint.symm.trans hImage
  let invR := eqToHom (Functor.congr_obj (originalLoopPowerAdd d n).symm X)
  have hBack : PointedCGWH.piNMap 0 invR z = zWhole := by
    have hMap := congrArg (PointedCGWH.piNMap 0 invR) hz
    have hId : eR ≫ invR = 𝟙 ((loopPower (d + n)).obj X) := by
      dsimp only [eR, invR]
      rw [eqToHom_trans]
      rfl
    have hComp := ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor 0).map_comp eR invR) zWhole
    have hIdentity := ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor 0).map_id
      ((loopPower (d + n)).obj X)) zWhole
    exact hMap.symm.trans (hComp.symm.trans
      ((congrArg (fun g => PointedCGWH.piNMap 0 g zWhole) hId).trans hIdentity))
  have hShift := sameSphereZeroLoopPowerAssociation n d X z
  have hDegree := Nat.add_comm n d
  have hCount : ∀ {a b : ℕ} (h : a = b) (z : PointedCGWH.piN 0 ((loopPower a).obj X)),
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h)) (zeroLoopPowerPiShift a X z) =
      zeroLoopPowerPiShift b X
        (PointedCGWH.piNMap 0 (eqToHom (congrArg (fun j => (loopPower j).obj X) h)) z) := by
    intro a b h z
    cases h
    have hId := ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor 0).map_id
      ((loopPower a).obj X)) z
    exact congrArg (zeroLoopPowerPiShift a X) hId.symm
  let castTotal := eqToHom (congrArg (fun j => (loopPower j).obj X) (Nat.add_comm n d))
  let rawInv := eqToHom (Functor.congr_obj ((congrArg loopPower (Nat.add_comm n d)).trans
    (originalLoopPowerAdd d n)).symm X)
  have hPath : rawInv ≫ castTotal = invR := by
    dsimp only [rawInv, castTotal, invR]
    rw [eqToHom_trans]
  have hCountApplied := hCount (Nat.add_comm n d) (PointedCGWH.piNMap 0 rawInv z)
  have hStage : PointedCGWH.piNMap 0 castTotal (PointedCGWH.piNMap 0 rawInv z) = zWhole := by
    have hComp := ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor 0).map_comp rawInv castTotal) z
    exact hComp.symm.trans
      ((congrArg (fun g => PointedCGWH.piNMap 0 g z) hPath).trans hBack)
  have hWholeClass :
      (Equiv.cast (congrArg (fun k => PointedCGWH.piN k X) (Nat.add_comm n d)))
        (zeroLoopPowerPiShift (n + d) X (PointedCGWH.piNMap 0 rawInv z)) =
      (spherePiHomEquiv (d + n) X).symm
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫ f)) :=
    hCountApplied.trans (congrArg (zeroLoopPowerPiShift (d + n) X) hStage)
  have hCastCancel : ∀ (a b : ℕ) (h : a = b) (x : PointedCGWH.piN a X),
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h.symm))
        ((Equiv.cast (congrArg (fun j => PointedCGWH.piN j X) h)) x) = x := by
    intro a b h x
    cases h
    rfl
  have hShiftCast := congrArg
    (Equiv.cast (congrArg (fun k => PointedCGWH.piN k X) (Nat.add_comm n d))) hShift
  have hCancel := hCastCancel (d + n) (n + d) (Nat.add_comm d n)
    (((loopPowerPiShift n d).app X).toEquiv (zeroLoopPowerPiShift d ((loopPower n).obj X) z))
  exact hWholeClass.symm.trans (hShiftCast.trans hCancel)



end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaSpherePowerClass

section NativeGammaDiagonalPower


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SphereHom
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

theorem originalIsoCancelSourceWord {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (j : D ≅ B) (f : B ⟶ E) :
    (e ≪≫ j.symm).hom ≫ j.hom ≫ f = e.hom ≫ f := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- The whole original successor source word retains its value Iso and actual structure map. -/
theorem originalIsoIterationSourceWord {C : Type*} [Category C]
    {A B D E F : C} (v : A ≅ B) (j : D ≅ B) (f : B ⟶ E) (g : E ⟶ F)
    (z : D ⟶ F) (h : z = j.hom ≫ f ≫ g) :
    (v ≪≫ j.symm).hom ≫ z = v.hom ≫ f ≫ g := by
  rw [h]
  exact originalIsoCancelSourceWord v j (f ≫ g)

/-- The complete original repeated source action uses the original finite iteration and exact level cast. -/
def originalRepeatedSphereStructure (X : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v} PointedCGWH.sphereOne) (r
  n : ℕ) :
    (sphereTensorPower n).obj (X.level r) ⟶ X.level (r + n) :=
  (spherePowerValueIso n (X.level r)).hom ≫
    CategoryTheory.SequentialSpectrum.iteratedStructureMap X n r ≫
    eqToHom (congrArg X.level (Nat.add_comm n r))

/-- The whole original zero action retains its genuine source map. -/
theorem originalRepeatedSphereStructureZero (X : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v}
  PointedCGWH.sphereOne) (r : ℕ) :
    originalRepeatedSphereStructure X r 0 = 𝟙 (X.level r) := by
  change (λ_ (X.level r)).inv ≫ (λ_ (X.level r)).hom ≫ eqToHom _ ≫ eqToHom _ = _
  rw [Iso.inv_hom_id_assoc, eqToHom_trans]
  rfl

/-- Every entire successor source action retains the original scalar structure map and whole prior iterate. -/
theorem originalRepeatedSphereStructureSucc (X : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v}
  PointedCGWH.sphereOne) (r n : ℕ) :
    originalRepeatedSphereStructure X r (n + 1) =
      (sphereTensorPower n).map (X.structureMap r) ≫
        originalRepeatedSphereStructure X (r + 1) n ≫
        eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega)) := by
  let Y := X
  let sigma := X.structureMap r
  let P := MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n
  have hNat := originalSpherePowerValueIso_naturality n sigma
  have hWord :
      (spherePowerValueIso (n + 1) (X.level r)).hom ≫
        CategoryTheory.SequentialSpectrum.iteratedStructureMap Y (n + 1) r =
      (spherePowerValueIso n (PointedCGWH.suspension.obj (X.level r))).hom ≫
        (P ◁ sigma) ≫ CategoryTheory.SequentialSpectrum.iteratedStructureMap Y n (r + 1) ≫
        eqToHom (congrArg Y.level
          ((Nat.add_succ n r).trans (Nat.succ_add n r).symm)) := by
    have hValue := congrArg Iso.hom (spherePowerValueIsoSucc n (X.level r))
    have hIteration := CategoryTheory.SequentialSpectrum.iteratedStructureMap_succ Y n r
    have hNormalized :
        CategoryTheory.SequentialSpectrum.iteratedStructureMap X (n + 1) r =
          (α_ P PointedCGWH.sphereOne (X.level r)).hom ≫
          (P ◁ sigma) ≫ CategoryTheory.SequentialSpectrum.iteratedStructureMap X n (r + 1) ≫
          eqToHom (congrArg X.level ((Nat.add_succ n r).trans (Nat.succ_add n r).symm)) := by
      simpa only [id_tensorHom, P, sigma, Y] using hIteration
    have hCancel := originalIsoIterationSourceWord
      (spherePowerValueIso n (PointedCGWH.suspension.obj (X.level r)))
      (α_ P PointedCGWH.sphereOne (X.level r)) (P ◁ sigma)
      (CategoryTheory.SequentialSpectrum.iteratedStructureMap X n (r + 1) ≫
        eqToHom (congrArg X.level ((Nat.add_succ n r).trans (Nat.succ_add n r).symm)))
      (CategoryTheory.SequentialSpectrum.iteratedStructureMap X (n + 1) r) hNormalized
    exact (congrArg (fun z => z ≫ CategoryTheory.SequentialSpectrum.iteratedStructureMap X (n + 1) r)
      hValue).trans hCancel
  have hPaths :
      eqToHom (congrArg Y.level ((Nat.add_succ n r).trans (Nat.succ_add n r).symm)) ≫
        eqToHom (congrArg X.level (Nat.add_comm (n + 1) r)) =
      eqToHom (congrArg X.level (Nat.add_comm n (r + 1))) ≫
        eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega)) := by
    rw [eqToHom_trans, eqToHom_trans]
  have h := congrArg (fun z => z ≫ eqToHom (congrArg X.level (Nat.add_comm (n + 1) r))) hWord
  have hRest :
      (spherePowerValueIso n (PointedCGWH.suspension.obj (X.level r))).hom ≫
        (P ◁ sigma) ≫ CategoryTheory.SequentialSpectrum.iteratedStructureMap Y n (r + 1) ≫
        eqToHom (congrArg Y.level ((Nat.add_succ n r).trans (Nat.succ_add n r).symm)) ≫
        eqToHom (congrArg X.level (Nat.add_comm (n + 1) r)) =
      (sphereTensorPower n).map sigma ≫ originalRepeatedSphereStructure X (r + 1) n ≫
        eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega)) := by
    have hNatPost := congrArg (fun z => z ≫
      CategoryTheory.SequentialSpectrum.iteratedStructureMap Y n (r + 1) ≫
      eqToHom (congrArg X.level (Nat.add_comm n (r + 1))) ≫
      eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega))) hNat.symm
    have hCastPost := congrArg (fun z =>
      (spherePowerValueIso n (PointedCGWH.suspension.obj (X.level r))).hom ≫
        (P ◁ sigma) ≫ CategoryTheory.SequentialSpectrum.iteratedStructureMap Y n (r + 1) ≫ z) hPaths
    exact hCastPost.trans hNatPost
  exact h.trans hRest

/-- Every full original higher structure adjunct is the same recursively composed original pointed map. -/
theorem originalRepeatedSphereAdjunctSucc (X : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v}
  PointedCGWH.sphereOne) (r n : ℕ) :
    (powerAdjunction (n + 1)).homEquiv (X.level r) (X.level (r + (n + 1)))
        (originalRepeatedSphereStructure X r (n + 1)) =
      PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r) (X.level (r + 1)) (X.structureMap r) ≫
        PointedCGWH.loop.map
          ((powerAdjunction n).homEquiv (X.level (r + 1)) (X.level (r + 1 + n))
            (originalRepeatedSphereStructure X (r + 1) n)) ≫
        (loopPower (n + 1)).map
          (eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega))) := by
  have hSource := originalRepeatedSphereStructureSucc X r n
  have hComp := congrFun (congrFun (Adjunction.comp_homEquiv PointedCGWH.suspensionLoopAdjunction
    (powerAdjunction n)) (X.level r)) (X.level (r + (n + 1)))
  let cast := eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega))
  let prior := originalRepeatedSphereStructure X (r + 1) n
  let sigma := X.structureMap r
  have hOuter := congrArg (fun f => (powerAdjunction (n + 1)).homEquiv (X.level r)
    (X.level (r + (n + 1))) f) hSource
  have hHom := congrArg (fun e => e
    ((sphereTensorPower n).map sigma ≫ prior ≫ cast)) hComp
  have hFirst := (powerAdjunction n).homEquiv_naturality_left sigma (prior ≫ cast)
  have hTarget := (powerAdjunction n).homEquiv_naturality_right prior cast
  have hScalar := PointedCGWH.suspensionLoopAdjunction.homEquiv_naturality_right sigma
    ((powerAdjunction n).homEquiv (X.level (r + 1)) (X.level (r + (n + 1))) (prior ≫ cast))
  have hMap := PointedCGWH.loop.map_comp
    ((powerAdjunction n).homEquiv (X.level (r + 1)) (X.level (r + 1 + n)) prior)
    ((loopPower n).map cast)
  have hWhole :
      PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r)
        ((loopPower n).obj (X.level (r + (n + 1))))
        ((powerAdjunction n).homEquiv (PointedCGWH.suspension.obj (X.level r))
          (X.level (r + (n + 1))) ((sphereTensorPower n).map sigma ≫ prior ≫ cast)) =
      PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r) (X.level (r + 1)) sigma ≫
        PointedCGWH.loop.map
          ((powerAdjunction n).homEquiv (X.level (r + 1)) (X.level (r + 1 + n)) prior) ≫
        (loopPower (n + 1)).map cast := by
    have hFirstOuter := congrArg
      (PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r)
        ((loopPower n).obj (X.level (r + (n + 1))))) hFirst
    have hTargetOuter := congrArg (fun f =>
      PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r) (X.level (r + 1)) sigma ≫
        PointedCGWH.loop.map f) hTarget
    have hMapOuter := congrArg (fun f =>
      PointedCGWH.suspensionLoopAdjunction.homEquiv (X.level r) (X.level (r + 1)) sigma ≫ f) hMap
    exact hFirstOuter.trans (hScalar.trans (hTargetOuter.trans hMapOuter))
  exact hOuter.trans (hHom.trans hWhole)

section ActualEnrichedSourceSpecialization

/-- The same original repeated structure source acts on the original enriched spectrum's full level values. -/
def originalEnrichedRepeatedSphereStructure (X : PointedCGWH.SequentialSpectrum.{u, v}) (r n : ℕ) :
    (sphereTensorPower n).obj (X.level r) ⟶ X.level (r + n) :=
  originalRepeatedSphereStructure
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X) r n

/-- Both complete original successor words preserve the literal enriched structure map. -/
theorem originalEnrichedRepeatedSphereStructureSucc (X : PointedCGWH.SequentialSpectrum.{u, v})
    (r n : ℕ) :
    originalEnrichedRepeatedSphereStructure X r (n + 1) =
      (sphereTensorPower n).map (PointedCGWH.SequentialSpectrum.structureMap X r) ≫
        originalEnrichedRepeatedSphereStructure X (r + 1) n ≫
        eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega)) := by
  exact originalRepeatedSphereStructureSucc
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X) r n

end ActualEnrichedSourceSpecialization

/-- The exact actual repeated enriched adjunct is the original sphere-power Hom action. -/
def originalEnrichedRepeatedSphereAdjunct (X : PointedCGWH.SequentialSpectrum.{u, v}) (r n : ℕ) :
    X.level r ⟶ (loopPower n).obj (X.level (r + n)) :=
  (powerAdjunction n).homEquiv (X.level r) (X.level (r + n))
    (originalEnrichedRepeatedSphereStructure X r n)

/-- The complete original enriched zero adjunct is the actual identity on its source level. -/
theorem originalEnrichedRepeatedSphereAdjunctZero (X : PointedCGWH.SequentialSpectrum.{u, v}) (r : ℕ) :
    originalEnrichedRepeatedSphereAdjunct X r 0 = 𝟙 (X.level r) := by
  have hZero := originalRepeatedSphereStructureZero
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X) r
  have hMap := congrArg ((powerAdjunction 0).homEquiv (X.level r) (X.level r)) hZero
  have hId : (powerAdjunction 0).homEquiv (X.level r) (X.level r) (𝟙 (X.level r)) =
      𝟙 (X.level r) := by
    change 𝟙 (X.level r) ≫ 𝟙 (X.level r) = 𝟙 (X.level r)
    exact Category.id_comp _
  exact hMap.trans hId

/-- Every whole original enriched power adjunct keeps the literal successor and its actual target level cast. -/
theorem originalEnrichedRepeatedSphereAdjunctSucc (X : PointedCGWH.SequentialSpectrum.{u, v})
    (r n : ℕ) :
    originalEnrichedRepeatedSphereAdjunct X r (n + 1) =
      PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫
        PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
        (loopPower (n + 1)).map
          (eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega))) :=
  originalRepeatedSphereAdjunctSucc
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne X) r n

/-- The complete original higher adjunct map keeps every actual source and target level equality. -/
theorem originalRepeatedSphereAdjunctIndexCast (X : PointedCGWH.SequentialSpectrum.{u, v})
    (n : ℕ) {r s : ℕ} (h : r = s) :
    eqToHom (congrArg X.level h) ≫ originalEnrichedRepeatedSphereAdjunct X s n =
      originalEnrichedRepeatedSphereAdjunct X r n ≫
        (loopPower n).map (eqToHom (congrArg X.level (congrArg (fun i => i + n) h))) := by
  cases h
  have hCast : eqToHom (congrArg X.level (congrArg (fun i => i + n) (Eq.refl r))) =
      𝟙 (X.level (r + n)) := rfl
  have hMap := congrArg (loopPower n).map hCast
  have hId := (loopPower n).map_id (X.level (r + n))
  exact (Category.id_comp _).trans
    ((congrArg (fun z => originalEnrichedRepeatedSphereAdjunct X r n ≫ z)
      (hMap.trans hId)).trans (Category.comp_id _)).symm

/-- The full original shifted homotopy word retains all actual source and target degree casts. -/
theorem originalPowerShiftDegreeCast (n : ℕ) {i j : ℕ} (h : i = j)
    (X : PointedCGWH.{u, v}) :
    eqToHom (congrArg (fun k => PointedCGWH.piN k ((loopPower n).obj X)) h) ≫
        (loopPowerPiShift n j).hom.app X =
      (loopPowerPiShift n i).hom.app X ≫
        eqToHom (congrArg (fun k => PointedCGWH.piN (k + n) X) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Every full original degree comparison passes through the SAME actual higher adjunct map. -/
theorem originalPowerSourceDegreeCast {i j : ℕ} (h : i = j)
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B) :
    eqToHom (congrArg (fun k => PointedCGWH.piN k A) h) ≫ (PointedCGWH.piNFunctor j).map f =
      (PointedCGWH.piNFunctor i).map f ≫ eqToHom (congrArg (fun k => PointedCGWH.piN k B) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm
open PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.GroupUnitCoherenceGeometry

/-- The actual original diagonal successor retains the original native shift, target level, and homotopy degree cast. -/
theorem originalDiagonalSuccessor_apply (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m k t : ℕ) (x : PointedCGWH.piN (k + t + 1) (X.level (m + t))) :
    ((diagonalDiagram X m k).map (homOfLE (Nat.le_succ t))).hom x =
      (Equiv.cast (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + 1))))
        (show k + t + 1 + 1 = k + (t + 1) + 1 by omega)))
      (PointedCGWH.piNMap (k + t + 1 + 1)
        (eqToHom (congrArg X.level (show m + t + 1 = m + (t + 1) by omega)))
        ((nativeLoopPiShiftNatIso (k + t + 1)).hom.app (X.level (m + t + 1))
          (PointedCGWH.piNMap (k + t + 1)
            (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) x))) := by
  have hStep := diagonalDiagram_map_succ X m k t
  have hNative := diagonalTransition_eq_cube t m k X x
  have hIndex := groupUnitIndexNatIso_hom_app t m k X
  have hWhole := (congrArg (fun f => f.hom x) hStep).trans hNative
  have hDegree :
      ((groupPrefixIndexNatIso t k).hom.app (X.level (m + t + 1))).hom
        ((nativeLoopPiShiftNatIso (k + t + 1)).hom.app (X.level (m + t + 1))
          (PointedCGWH.piNMap (k + t + 1)
            (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) x)) =
      (Equiv.cast (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + t + 1)))
        (show k + t + 1 + 1 = k + (t + 1) + 1 by omega)))
        ((nativeLoopPiShiftNatIso (k + t + 1)).hom.app (X.level (m + t + 1))
          (PointedCGWH.piNMap (k + t + 1)
            (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) x)) := by
    have h := positiveDegreeCast (k + t + 1) (k + (t + 1))
      (show k + t + 1 = k + (t + 1) by omega) (X.level (m + t + 1))
      ((nativeLoopPiShiftNatIso (k + t + 1)).hom.app (X.level (m + t + 1))
        (PointedCGWH.piNMap (k + t + 1)
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) x))
    exact h
  have hLevel : (levelUnitIndexNatIso t m).hom.app X =
      eqToHom (congrArg X.level (show m + t + 1 = m + (t + 1) by omega)) :=
    eqToHom_app (congrArg (CategoryTheory.Spectra.Sequential.evaluation PointedCGWH.sphereOne)
      (show m + t + 1 = m + (t + 1) by omega)) X
  have hCastMap : ∀ {i j : ℕ} (h : i = j) {A B : PointedCGWH.{u, v}}
      (f : A ⟶ B) (z : PointedCGWH.piN i A),
      PointedCGWH.piNMap j f ((Equiv.cast (congrArg (fun k => PointedCGWH.piN k A) h)) z) =
      (Equiv.cast (congrArg (fun k => PointedCGWH.piN k B) h)) (PointedCGWH.piNMap i f z) := by
    intro i j h A B f z
    cases h
    rfl
  have hIndexFunction := congrArg (fun f => f.hom
    ((nativeLoopPiShiftNatIso (k + t + 1)).hom.app (X.level (m + t + 1))
      (PointedCGWH.piNMap (k + t + 1)
        (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) x))) hIndex
  exact hWhole

/-- The full original source-degree equality commutes with the whole higher Hom and native power shift. -/
theorem originalShiftedDegreeSourceWord (n : ℕ) {i j : ℕ} (h : i = j)
    {A B : PointedCGWH.{u, v}} (f : A ⟶ (loopPower n).obj B) :
    eqToHom (congrArg (fun k => PointedCGWH.piN k A) h) ≫
        (PointedCGWH.piNFunctor j).map f ≫ (loopPowerPiShift n j).hom.app B =
    (PointedCGWH.piNFunctor i).map f ≫ (loopPowerPiShift n i).hom.app B ≫
      eqToHom (congrArg (fun k => PointedCGWH.piN (k + n) B) h) := by
  cases h
  have hCast : eqToHom (congrArg (fun k => PointedCGWH.piN (k + n) B) (Eq.refl i)) =
      𝟙 (PointedCGWH.piN (i + n) B) := rfl
  have hId : (PointedCGWH.piNFunctor i).map f ≫
        (loopPowerPiShift n i).hom.app B ≫ 𝟙 (PointedCGWH.piN (i + n) B) =
      (PointedCGWH.piNFunctor i).map f ≫ (loopPowerPiShift n i).hom.app B :=
    congrArg (fun z => (PointedCGWH.piNFunctor i).map f ≫ z)
      (Category.comp_id ((loopPowerPiShift n i).hom.app B))
  exact (Category.id_comp _).trans
    ((congrArg (fun z => (PointedCGWH.piNFunctor i).map f ≫
      (loopPowerPiShift n i).hom.app B ≫ z) hCast).trans hId).symm

/-- The entire original level equality commutes with the same higher source adjunct and native shift. -/
theorem originalShiftedLevelSourceWord (n i : ℕ) {A A' B B' : PointedCGWH.{u, v}}
    (hA : A = A') (hB : B = B') (f : A ⟶ (loopPower n).obj B)
    (f' : A' ⟶ (loopPower n).obj B')
    (hf : eqToHom hA ≫ f' = f ≫ (loopPower n).map (eqToHom hB)) :
    (PointedCGWH.piNFunctor i).map (eqToHom hA) ≫
        (PointedCGWH.piNFunctor i).map f' ≫ (loopPowerPiShift n i).hom.app B' =
      (PointedCGWH.piNFunctor i).map f ≫ (loopPowerPiShift n i).hom.app B ≫
        (PointedCGWH.piNFunctor (i + n)).map (eqToHom hB) := by
  have hMap : (PointedCGWH.piNFunctor i).map (eqToHom hA) ≫
        (PointedCGWH.piNFunctor i).map f' =
      (PointedCGWH.piNFunctor i).map f ≫
        (PointedCGWH.piNFunctor i).map ((loopPower n).map (eqToHom hB)) :=
    ((PointedCGWH.piNFunctor i).map_comp _ _).symm.trans
      (((PointedCGWH.piNFunctor i).congr_map hf).trans ((PointedCGWH.piNFunctor i).map_comp _ _))
  have hNatural := (loopPowerPiShift n i).hom.naturality (eqToHom hB)
  have hPost := congrArg (fun z => z ≫ (loopPowerPiShift n i).hom.app B') hMap
  have hNatPost := congrArg (fun z => (PointedCGWH.piNFunctor i).map f ≫ z) hNatural
  have hPostNormalized :
      (PointedCGWH.piNFunctor i).map (eqToHom hA) ≫
        (PointedCGWH.piNFunctor i).map f' ≫ (loopPowerPiShift n i).hom.app B' =
      (PointedCGWH.piNFunctor i).map f ≫
        (PointedCGWH.piNFunctor i).map ((loopPower n).map (eqToHom hB)) ≫
        (loopPowerPiShift n i).hom.app B' := by
    simpa only [Category.assoc] using hPost
  exact hPostNormalized.trans hNatPost

/-- The actual complete Type identity word equals its original identity. -/
theorem originalTypeFourIdentities (A : Type v) :
    (𝟙 A) ≫ (𝟙 A) ≫ (𝟙 A) ≫ (𝟙 A) = 𝟙 A := by
  simp only [Category.id_comp]



/-- The whole one-loop source comparison is the original native shift Iso. -/
theorem originalAllDegreeLoopShiftOne (k : ℕ) :
    loopPowerPiShift.{u, v} 1 k = nativeLoopPiShiftNatIso k := by
  let b := nativeLoopPiShiftNatIso.{u, v} k
  have h : loopPowerPiShift.{u, v} 1 k =
      Functor.associator (𝟭 PointedCGWH.{u, v}) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
      Functor.isoWhiskerLeft (𝟭 PointedCGWH.{u, v}) b ≪≫
      (PointedCGWH.piNFunctor (k + 1)).leftUnitor ≪≫ eqToIso rfl := rfl
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hValue := congrArg (fun e => e.hom.app X) h
  change 𝟙 _ ≫ b.hom.app X ≫ 𝟙 _ ≫ 𝟙 _ = b.hom.app X
  simp only [Category.id_comp, Category.comp_id]

/-- The full actual power-shift function retains the original one-loop prefix and arithmetic map. -/
theorem originalPowerShiftPrefix (n k : ℕ) (X : PointedCGWH.{u, v})
    (x : PointedCGWH.piN k (PointedCGWH.loop.obj ((loopPower n).obj X))) :
    ((loopPowerPiShift (n + 1) k).app X).toEquiv x =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j X)
        (show k + 1 + n = k + (n + 1) by omega)))
        (((loopPowerPiShift n (k + 1)).app X).toEquiv
          ((nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) x)) := by
  have hWhole : (loopPowerPiShift (n + 1) k).hom.app X =
      (nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) ≫
      (loopPowerPiShift n (k + 1)).hom.app X ≫
      eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj X)
        (show k + 1 + n = k + (n + 1) by omega)) := by
    let source := Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
      Functor.isoWhiskerLeft (loopPower n) (nativeLoopPiShiftNatIso k) ≪≫
      loopPowerPiShift n (k + 1) ≪≫ eqToIso (congrArg PointedCGWH.piNFunctor
        (show k + 1 + n = k + (n + 1) by omega))
    have hWord : loopPowerPiShift (n + 1) k = source := rfl
    have h := congrArg (fun e => e.hom.app X) hWord
    have hCast := eqToHom_app (congrArg PointedCGWH.piNFunctor
      (show k + 1 + n = k + (n + 1) by omega)) X
    exact h.trans (by
      change 𝟙 _ ≫ (nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) ≫
        (loopPowerPiShift n (k + 1)).hom.app X ≫ (eqToHom (congrArg PointedCGWH.piNFunctor
          (show k + 1 + n = k + (n + 1) by omega))).app X = _
      rw [Category.id_comp]
      exact congrArg (fun f => (nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) ≫
        (loopPowerPiShift n (k + 1)).hom.app X ≫ f) hCast)
  have h := ConcreteCategory.congr_hom hWhole x
  have hCast := originalTypeEqToHom_apply
    (congrArg (fun j => (PointedCGWH.piNFunctor j).obj X)
      (show k + 1 + n = k + (n + 1) by omega))
    (((loopPowerPiShift n (k + 1)).app X).toEquiv
      ((nativeLoopPiShiftNatIso k).hom.app ((loopPower n).obj X) x))
  exact h.trans hCast
/-- The complete original all-power forward shift retains every actual pointed target map. -/
theorem originalAllPowerShift_naturality (n d : ℕ) {A B : PointedCGWH.{u, v}}
    (f : A ⟶ B) (x : PointedCGWH.piN d ((loopPower n).obj A)) :
    ((loopPowerPiShift n d).app B).toEquiv
      (PointedCGWH.piNMap d ((loopPower n).map f) x) =
    PointedCGWH.piNMap (d + n) f (((loopPowerPiShift n d).app A).toEquiv x) :=
  ConcreteCategory.congr_hom ((loopPowerPiShift n d).hom.naturality f) x

/-- The whole original shift retains the actual inverse source map and all class representatives. -/
theorem originalAllPowerShift_inverse_naturality (n d : ℕ) {A B : PointedCGWH.{u, v}}
    (f : A ⟶ B) (x : PointedCGWH.piN (d + n) A) :
    (((loopPowerPiShift n d).app B).toEquiv).symm (PointedCGWH.piNMap (d + n) f x) =
      PointedCGWH.piNMap d ((loopPower n).map f)
        ((((loopPowerPiShift n d).app A).toEquiv).symm x) := by
  let eA := ((loopPowerPiShift n d).app A).toEquiv
  let eB := ((loopPowerPiShift n d).app B).toEquiv
  apply eB.injective
  have hNatural := originalAllPowerShift_naturality n d f (eA.symm x)
  have hLeft := eB.apply_symm_apply (PointedCGWH.piNMap (d + n) f x)
  have hRight := congrArg (PointedCGWH.piNMap (d + n) f) (eA.apply_symm_apply x)
  exact hLeft.trans (hNatural.trans hRight).symm

/-- The original one-loop then n-loop action retains the actual input map and original native shift. -/
theorem originalCompositeNativeShift (n d : ℕ) {A B D E : PointedCGWH.{u, v}}
    (a : A ⟶ PointedCGWH.loop.obj B) (b : B ⟶ (loopPower n).obj D) (c : D ⟶ E)
    (x : PointedCGWH.piN d A) :
    (Equiv.cast (congrArg (fun j => PointedCGWH.piN j E)
        (show d + 1 + n = d + (n + 1) by omega)))
      (PointedCGWH.piNMap (d + 1 + n) c
        (((loopPowerPiShift n (d + 1)).app D).toEquiv
          (PointedCGWH.piNMap (d + 1) b
            ((nativeLoopPiShiftNatIso d).hom.app B (PointedCGWH.piNMap d a x))))) =
    ((loopPowerPiShift (n + 1) d).app E).toEquiv
      (PointedCGWH.piNMap d
        (a ≫ PointedCGWH.loop.map b ≫ (loopPower (n + 1)).map c) x) := by
  have hNative := ConcreteCategory.congr_hom ((nativeLoopPiShiftNatIso d).hom.naturality b)
    (PointedCGWH.piNMap d a x)
  have hComposite : PointedCGWH.piNMap d (a ≫ PointedCGWH.loop.map b) x =
      PointedCGWH.piNMap d (PointedCGWH.loop.map b) (PointedCGWH.piNMap d a x) :=
    ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor d).map_comp a (PointedCGWH.loop.map b)) x
  have hPrefix := originalPowerShiftPrefix n d D
    (PointedCGWH.piNMap d (a ≫ PointedCGWH.loop.map b) x)
  have hInner :
      ((loopPowerPiShift (n + 1) d).app D).toEquiv
        (PointedCGWH.piNMap d (a ≫ PointedCGWH.loop.map b) x) =
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j D)
        (show d + 1 + n = d + (n + 1) by omega)))
        (((loopPowerPiShift n (d + 1)).app D).toEquiv
          (PointedCGWH.piNMap (d + 1) b
            ((nativeLoopPiShiftNatIso d).hom.app B (PointedCGWH.piNMap d a x)))) := by
    have hPoint := (congrArg ((nativeLoopPiShiftNatIso d).hom.app ((loopPower n).obj D))
      hComposite).trans hNative
    exact hPrefix.trans (congrArg (fun z =>
      (Equiv.cast (congrArg (fun j => PointedCGWH.piN j D)
        (show d + 1 + n = d + (n + 1) by omega)))
        (((loopPowerPiShift n (d + 1)).app D).toEquiv z)) hPoint)
  have hTarget := originalAllPowerShift_naturality (n + 1) d c
    (PointedCGWH.piNMap d (a ≫ PointedCGWH.loop.map b) x)
  have hCastMap : ∀ {i j : ℕ} (h : i = j) (z : PointedCGWH.piN i D),
      PointedCGWH.piNMap j c ((Equiv.cast (congrArg (fun k => PointedCGWH.piN k D) h)) z) =
      (Equiv.cast (congrArg (fun k => PointedCGWH.piN k E) h)) (PointedCGWH.piNMap i c z) := by
    intro i j h z
    cases h
    rfl
  have hFullMap := ConcreteCategory.congr_hom ((PointedCGWH.piNFunctor d).map_comp
    (a ≫ PointedCGWH.loop.map b) ((loopPower (n + 1)).map c)) x
  have hMapInner := congrArg (PointedCGWH.piNMap (d + (n + 1)) c) hInner
  exact (hCastMap (show d + 1 + n = d + (n + 1) by omega)
    (((loopPowerPiShift n (d + 1)).app D).toEquiv
      (PointedCGWH.piNMap (d + 1) b
        ((nativeLoopPiShiftNatIso d).hom.app B (PointedCGWH.piNMap d a x))))).symm.trans
    (hMapInner.symm.trans (hTarget.symm.trans
      (congrArg (((loopPowerPiShift (n + 1) d).app E).toEquiv) hFullMap.symm)))
/-- The complete original shift action composes the original successor adjunct and prior power map. -/
theorem originalNativeShiftComposite_whole (n d : ℕ)
    {A B D E : PointedCGWH.{u, v}}
    (a : A ⟶ PointedCGWH.loop.obj B) (b : B ⟶ (loopPower n).obj D) (c : D ⟶ E) :
    (PointedCGWH.piNFunctor d).map a ≫ (nativeLoopPiShiftNatIso d).hom.app B ≫
      (PointedCGWH.piNFunctor (d + 1)).map b ≫
      (loopPowerPiShift n (d + 1)).hom.app D ≫
      (PointedCGWH.piNFunctor (d + 1 + n)).map c ≫
      eqToHom (congrArg (fun j => PointedCGWH.piN j E)
        (show d + 1 + n = d + (n + 1) by omega)) =
    (PointedCGWH.piNFunctor d).map (a ≫ PointedCGWH.loop.map b ≫ (loopPower (n + 1)).map c) ≫
      (loopPowerPiShift (n + 1) d).hom.app E := by
  apply ConcreteCategory.hom_ext
  intro x
  have h := originalCompositeNativeShift n d a b c x
  have hCast := originalTypeEqToHom_apply
    (congrArg (fun j => PointedCGWH.piN j E)
      (show d + 1 + n = d + (n + 1) by omega))
    (PointedCGWH.piNMap (d + 1 + n) c
      (((loopPowerPiShift n (d + 1)).app D).toEquiv
        (PointedCGWH.piNMap (d + 1) b
          ((nativeLoopPiShiftNatIso d).hom.app B (PointedCGWH.piNMap d a x)))))
  exact hCast.trans h

/-- The complete original successor source keeps the prior action through all actual target maps. -/
theorem originalNativeShiftCastComposite (n d j : ℕ) (hd : d + 1 = j)
    {A B B' C C' T : PointedCGWH.{u, v}} (hB : B = B') (hC : C = C')
    (a : A ⟶ PointedCGWH.loop.obj B)
    (b : B ⟶ (loopPower n).obj C) (b' : B' ⟶ (loopPower n).obj C')
    (c : C' ⟶ T) (c' : C ⟶ T)
    (hSource : eqToHom hB ≫ b' = b ≫ (loopPower n).map (eqToHom hC))
    (hTarget : eqToHom hC ≫ c = c') :
    (PointedCGWH.piNFunctor d).map a ≫ (nativeLoopPiShiftNatIso d).hom.app B ≫
      (PointedCGWH.piNFunctor (d + 1)).map (eqToHom hB) ≫
      eqToHom (congrArg (fun i => (PointedCGWH.piNFunctor i).obj B') hd) ≫
      (PointedCGWH.piNFunctor j).map b' ≫ (loopPowerPiShift n j).hom.app C' ≫
      (PointedCGWH.piNFunctor (j + n)).map c ≫
      eqToHom (congrArg (fun i => (PointedCGWH.piNFunctor (i + n)).obj T) hd.symm) =
    (PointedCGWH.piNFunctor d).map a ≫ (nativeLoopPiShiftNatIso d).hom.app B ≫
      (PointedCGWH.piNFunctor (d + 1)).map b ≫ (loopPowerPiShift n (d + 1)).hom.app C ≫
      (PointedCGWH.piNFunctor (d + 1 + n)).map c' := by
  cases hd
  cases hB
  cases hC
  have hPointB : eqToHom (Eq.refl B) = 𝟙 B := rfl
  have hPointC : eqToHom (Eq.refl C) = 𝟙 C := rfl
  have hLoopMap := (loopPower n).map_id C
  have hb : b' = b :=
    (Category.id_comp b').symm.trans
      ((congrArg (fun z => z ≫ b') hPointB).symm.trans
        (hSource.trans ((congrArg (fun z => b ≫ (loopPower n).map z) hPointC).trans
          ((congrArg (fun z => b ≫ z) hLoopMap).trans (Category.comp_id b)))))
  have hc : c = c' := (Category.id_comp c).symm.trans
    ((congrArg (fun z => z ≫ c) hPointC).symm.trans hTarget)
  subst b'
  subst c'
  have hPiB := (PointedCGWH.piNFunctor (d + 1)).map_id B
  simp only [eqToHom_refl, hPiB, Category.id_comp, Category.comp_id]

/-- The whole original group/space target equality is its actual level map followed by its degree cast. -/
theorem originalMixedPiCast {a b : ℕ} (h : a = b)
    (K : ℕ → ℕ) (X : ℕ → PointedCGWH.{u, v}) :
    eqToHom (congrArg (fun i => PointedCGWH.piN (K i) (X i)) h) =
      (PointedCGWH.piNFunctor (K a)).map (eqToHom (congrArg X h)) ≫
        eqToHom (congrArg (fun i => PointedCGWH.piN (K i) (X b)) h) := by
  cases h
  have hMap : (PointedCGWH.piNFunctor (K a)).map (𝟙 (X a)) =
      𝟙 (PointedCGWH.piN (K a) (X a)) := (PointedCGWH.piNFunctor (K a)).map_id _
  change 𝟙 _ = (PointedCGWH.piNFunctor (K a)).map (𝟙 (X a)) ≫ 𝟙 _
  exact (Category.id_comp _).symm.trans (congrArg (fun f => f ≫ 𝟙 _) hMap.symm)

/-- Both original pointed equality paths induce the SAME actual homotopy equality arrow. -/
theorem originalPiLevelCastPath (d : ℕ) {A B D : PointedCGWH.{u, v}}
    (h₁ : A = B) (h₂ : B = D) (h₃ : A = D) :
    (PointedCGWH.piNFunctor d).map (eqToHom h₁) ≫
      (PointedCGWH.piNFunctor d).map (eqToHom h₂) =
      (PointedCGWH.piNFunctor d).map (eqToHom h₃) := by
  rw [← Functor.map_comp, eqToHom_trans]

/-- The complete original source recurrence retains its actual postcomposition map. -/
theorem originalPostSourceRecurrence {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ D) (h : d = a ≫ b) :
    a ≫ b ≫ c = d ≫ c :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ c) h.symm)

/-- The full two-coordinate target cast preserves its actual prior degree arrow and level map. -/
theorem originalPiTargetCastSquare {a b : ℕ} (h : a = b)
    (K : ℕ → ℕ) (X : ℕ → PointedCGWH.{u, v}) (d : ℕ)
    (hd : d = K a) {A : PointedCGWH.{u, v}} (l : A ⟶ X a)
    (c : A ⟶ X b) (hc : l ≫ eqToHom (congrArg X h) = c) (he : d = K b) :
    (PointedCGWH.piNFunctor d).map l ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X a)) hd) ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor (K q)).obj (X q)) h) =
    (PointedCGWH.piNFunctor d).map c ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X b)) he) := by
  cases h
  cases hd
  have hMap := (PointedCGWH.piNFunctor (K a)).congr_map hc
  have hId : l ≫ eqToHom (congrArg X (Eq.refl a)) = l := Category.comp_id l
  have hc' : l = c := hId.symm.trans hc
  have hResult := (PointedCGWH.piNFunctor (K a)).congr_map hc'
  have hTail : eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X a)) he) =
      𝟙 ((PointedCGWH.piNFunctor (K a)).obj (X a)) := by
    have hp : he = Eq.refl (K a) := Subsingleton.elim _ _
    exact congrArg (fun p => eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X a)) p)) hp
  have hLeft : (PointedCGWH.piNFunctor (K a)).map l ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X a)) (Eq.refl (K a))) ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor (K q)).obj (X q)) (Eq.refl a)) =
      (PointedCGWH.piNFunctor (K a)).map l :=
    (congrArg (fun z => (PointedCGWH.piNFunctor (K a)).map l ≫ z)
      (Category.id_comp (𝟙 ((PointedCGWH.piNFunctor (K a)).obj (X a))))).trans
      (Category.comp_id _)
  have hRight : (PointedCGWH.piNFunctor (K a)).map c ≫
      eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X a)) he) =
      (PointedCGWH.piNFunctor (K a)).map c :=
    (congrArg (fun z => (PointedCGWH.piNFunctor (K a)).map c ≫ z) hTail).trans (Category.comp_id _)
  exact hLeft.trans (hResult.trans hRight.symm)

/-- The whole actual diagonal n-step Type map retains both level and degree arithmetic arrows. -/
theorem originalDiagonalMap_power_whole (X : PointedCGWH.SequentialSpectrum.{u, v})
    (m k t n : ℕ) :
    (forget GrpCat).map
      ((PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry.diagonalDiagram X m k).map
        (homOfLE (Nat.le_add_right t n))) =
    (PointedCGWH.piNFunctor (k + t + 1)).map
        (originalEnrichedRepeatedSphereAdjunct X (m + t) n) ≫
      (loopPowerPiShift n (k + t + 1)).hom.app (X.level (m + t + n)) ≫
      (PointedCGWH.piNFunctor (k + t + 1 + n)).map
        (eqToHom (congrArg X.level (show m + t + n = m + (t + n) by omega))) ≫
      eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + n))))
        (show k + t + 1 + n = k + (t + n) + 1 by omega)) := by
  induction n generalizing m k t with
  | zero =>
    let D := PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry.diagonalDiagram X m k
    have hArrow : homOfLE (Nat.le_add_right t 0) = 𝟙 t := Subsingleton.elim _ _
    have hLeft : (forget GrpCat).map (D.map (homOfLE (Nat.le_add_right t 0))) =
        𝟙 ((PointedCGWH.piNFunctor (k + t + 1)).obj (X.level (m + t))) :=
      (congrArg (fun f => (forget GrpCat).map (D.map f)) hArrow).trans
        ((congrArg (forget GrpCat).map (D.map_id t)).trans ((forget GrpCat).map_id _))
    have hAdj := originalEnrichedRepeatedSphereAdjunctZero X (m + t)
    have hPi := (PointedCGWH.piNFunctor (k + t + 1)).map_id (X.level (m + t))
    have hLoop : (loopPowerPiShift 0 (k + t + 1)).hom.app (X.level (m + t + 0)) =
        𝟙 ((PointedCGWH.piNFunctor (k + t + 1)).obj (X.level (m + t))) := rfl
    have hPoint : eqToHom (congrArg X.level (show m + t + 0 = m + (t + 0) by omega)) =
        𝟙 (X.level (m + t)) := rfl
    have hDegree : eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + 0))))
        (show k + t + 1 + 0 = k + (t + 0) + 1 by omega)) =
      𝟙 ((PointedCGWH.piNFunctor (k + t + 1)).obj (X.level (m + t))) := rfl
    have hRight :
        (PointedCGWH.piNFunctor (k + t + 1)).map
            (originalEnrichedRepeatedSphereAdjunct X (m + t) 0) ≫
          (loopPowerPiShift 0 (k + t + 1)).hom.app (X.level (m + t + 0)) ≫
          (PointedCGWH.piNFunctor (k + t + 1 + 0)).map
            (eqToHom (congrArg X.level (show m + t + 0 = m + (t + 0) by omega))) ≫
          eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + 0))))
            (show k + t + 1 + 0 = k + (t + 0) + 1 by omega)) =
        𝟙 ((PointedCGWH.piNFunctor (k + t + 1)).obj (X.level (m + t))) := by
      have hAdjMap := congrArg (PointedCGWH.piNFunctor (k + t + 1)).map hAdj
      have hPointMap := (congrArg (PointedCGWH.piNFunctor (k + t + 1)).map hPoint).trans hPi
      have hHead := congrArg₂ (fun a b => a ≫ b) (hAdjMap.trans hPi) hLoop
      have hTail := congrArg₂ (fun c d => c ≫ d) hPointMap hDegree
      have hAll := congrArg₂ (fun a b => a ≫ b) hHead hTail
      exact hAll.trans (originalTypeFourIdentities _)
    exact hLeft.trans hRight.symm
  | succ n ih =>
    let D := PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry.diagonalDiagram X m k
    let a := homOfLE (Nat.le_succ t)
    let b := homOfLE (show t + 1 ≤ t + (n + 1) by omega)
    let c := homOfLE (Nat.le_add_right t (n + 1))
    have hArrow : a ≫ b = c := Subsingleton.elim _ _
    have hMap : (forget GrpCat).map (D.map c) =
        (forget GrpCat).map (D.map a) ≫ (forget GrpCat).map (D.map b) :=
      (congrArg (fun f => (forget GrpCat).map (D.map f)) hArrow).symm.trans
        ((congrArg (forget GrpCat).map (D.map_comp a b)).trans ((forget GrpCat).map_comp _ _))
    have hPrior := ih m k (t + 1)
    have hSource := originalEnrichedRepeatedSphereAdjunctSucc X (m + t) n
    have hSuccessor :
        (forget GrpCat).map (D.map a) =
        (PointedCGWH.piNFunctor (k + t + 1)).map
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) ≫
        (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso (k + t + 1)).hom.app
          (X.level (m + t + 1)) ≫
        (PointedCGWH.piNFunctor (k + t + 1 + 1)).map
          (eqToHom (congrArg X.level (show m + t + 1 = m + (t + 1) by omega))) ≫
        eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + 1))))
          (show k + t + 1 + 1 = k + (t + 1) + 1 by omega)) := by
      apply ConcreteCategory.hom_ext
      intro x
      exact originalDiagonalSuccessor_apply X m k t x
    let b0 : t + 1 ⟶ t + 1 + n := homOfLE (Nat.le_add_right (t + 1) n)
    let bCast : t + 1 + n ⟶ t + (n + 1) := eqToHom (show t + 1 + n = t + (n + 1) by omega)
    have hB : b = b0 ≫ bCast := Subsingleton.elim _ _
    have hBMap : (forget GrpCat).map (D.map b) =
        (forget GrpCat).map (D.map b0) ≫ (forget GrpCat).map (D.map bCast) :=
      (congrArg (fun f => (forget GrpCat).map (D.map f)) hB).trans
        ((congrArg (forget GrpCat).map (D.map_comp b0 bCast)).trans ((forget GrpCat).map_comp _ _))
    have hPriorActual := hBMap.trans (congrArg (fun f => f ≫ (forget GrpCat).map (D.map bCast)) hPrior)
    have hBCast : (forget GrpCat).map (D.map bCast) =
        eqToHom (congrArg (fun j => PointedCGWH.piN (k + j + 1) (X.level (m + j)))
          (show t + 1 + n = t + (n + 1) by omega)) := by
      have h := eqToHom_map D (show t + 1 + n = t + (n + 1) by omega)
      exact (congrArg (forget GrpCat).map h).trans
        (eqToHom_map (forget GrpCat) _)
    have hApplied := hMap.trans (congrArg₂ (fun f g => f ≫ g) hSuccessor hPriorActual)
    let r := m + t
    let d := k + t + 1
    let l1 := eqToHom (congrArg X.level (show r + 1 = m + (t + 1) by omega))
    let l2 := eqToHom (congrArg X.level (show m + (t + 1) + n = m + ((t + 1) + n) by omega))
    let l3 := eqToHom (congrArg X.level (show r + 1 + n = r + (n + 1) by omega))
    have hDegree : d + 1 = k + (t + 1) + 1 := by dsimp [d]; omega
    have hSourceCast := originalPowerSourceDegreeCast hDegree
      (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n)
    have hShiftCast := originalPowerShiftDegreeCast n hDegree (X.level (m + (t + 1) + n))
    have hNatural := (loopPowerPiShift n (d + 1)).hom.naturality l2
    have hIndex := originalRepeatedSphereAdjunctIndexCast X n
      (show r + 1 = m + (t + 1) by dsimp [r]; omega)
    have hWholeIndex := originalShiftedLevelSourceWord n (d + 1)
      (show X.level (r + 1) = X.level (m + (t + 1)) by dsimp [r]; congr 1)
      (show X.level (r + 1 + n) = X.level (m + (t + 1) + n) by dsimp [r]; congr 1)
      (originalEnrichedRepeatedSphereAdjunct X (r + 1) n)
      (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n) hIndex
    have hComposite := originalNativeShiftComposite_whole n d
      (PointedCGWH.SequentialSpectrum.adjointStructureMap X r)
      (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) l3
    have hDegreeTail :
        eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + ((t + 1) + n))))
          (show k + (t + 1) + 1 + n = k + ((t + 1) + n) + 1 by omega)) ≫
        eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + ((t + 1) + n))))
          (show k + ((t + 1) + n) + 1 = k + (t + (n + 1)) + 1 by omega)) =
      eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + ((t + 1) + n))))
        (show k + (t + 1) + 1 + n = k + (t + (n + 1)) + 1 by omega)) := by
      rw [eqToHom_trans]
    have hLevelTail : l1 ≫
        eqToHom (congrArg X.level (show m + (t + 1) = r + 1 by dsimp [r]; omega)) =
      𝟙 (X.level (r + 1)) := by
      dsimp only [l1]
      rw [eqToHom_trans]
      rfl
    have hFinalSource := congrArg (PointedCGWH.piNFunctor d).map hSource
    have hPointShift := (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso d).hom.naturality
      (originalEnrichedRepeatedSphereAdjunct X (r + 1) n)
    have hSourceWord := originalEnrichedRepeatedSphereAdjunctSucc X r n
    let wholeCast := eqToHom (congrArg X.level
      (show r + (n + 1) = m + (t + (n + 1)) by dsimp [r]; omega))
    let degreeCast := eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + (n + 1)))))
      (show d + (n + 1) = k + (t + (n + 1)) + 1 by dsimp [d]; omega))
    have hShiftTarget := (loopPowerPiShift (n + 1) d).hom.naturality wholeCast
    have hCompositePost := congrArg (fun z => z ≫
      (PointedCGWH.piNFunctor (d + (n + 1))).map wholeCast ≫ degreeCast) hComposite
    have hLevelPath : l3 ≫ wholeCast =
        eqToHom (congrArg X.level
          (show r + 1 + n = m + (t + (n + 1)) by dsimp [r]; omega)) := by
      dsimp only [l3, wholeCast]
      rw [eqToHom_trans]
    have hFinal :
        ((PointedCGWH.piNFunctor (k + t + 1)).map
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X (m + t)) ≫
          (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso (k + t + 1)).hom.app
            (X.level (m + t + 1)) ≫
          (PointedCGWH.piNFunctor (k + t + 1 + 1)).map
            (eqToHom (congrArg X.level (show m + t + 1 = m + (t + 1) by omega))) ≫
          eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + 1))))
            (show k + t + 1 + 1 = k + (t + 1) + 1 by omega))) ≫
        ((PointedCGWH.piNFunctor (k + (t + 1) + 1)).map
          (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n) ≫
          (loopPowerPiShift n (k + (t + 1) + 1)).hom.app (X.level (m + (t + 1) + n)) ≫
          (PointedCGWH.piNFunctor (k + (t + 1) + 1 + n)).map
            (eqToHom (congrArg X.level (show m + (t + 1) + n = m + ((t + 1) + n) by omega))) ≫
          eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + ((t + 1) + n))))
            (show k + (t + 1) + 1 + n = k + ((t + 1) + n) + 1 by omega))) ≫
        (forget GrpCat).map (D.map bCast) =
        (PointedCGWH.piNFunctor (k + t + 1)).map
          (originalEnrichedRepeatedSphereAdjunct X (m + t) (n + 1)) ≫
          (loopPowerPiShift (n + 1) (k + t + 1)).hom.app (X.level (m + t + (n + 1))) ≫
          (PointedCGWH.piNFunctor (k + t + 1 + (n + 1))).map
            (eqToHom (congrArg X.level (show m + t + (n + 1) = m + (t + (n + 1)) by omega))) ≫
          eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj (X.level (m + (t + (n + 1)))))
            (show k + t + 1 + (n + 1) = k + (t + (n + 1)) + 1 by omega)) := by
      let j := k + (t + 1) + 1
      let B := X.level (r + 1)
      let B' := X.level (m + (t + 1))
      let C := X.level (r + 1 + n)
      let C' := X.level (m + (t + 1) + n)
      let T := X.level (m + (t + (n + 1)))
      let c' : C' ⟶ T := eqToHom (congrArg X.level
        (show m + (t + 1) + n = m + (t + (n + 1)) by omega))
      let c : C ⟶ T := l3 ≫ wholeCast
      have hTargetEq : eqToHom (congrArg X.level
          (show r + 1 + n = m + (t + 1) + n by dsimp [r]; omega)) ≫ c' = c := by
        dsimp only [c', c, l3, wholeCast]
        rw [eqToHom_trans, eqToHom_trans]
      have hCastComposite := originalNativeShiftCastComposite n d j hDegree
        (congrArg X.level (show r + 1 = m + (t + 1) by dsimp [r]; omega))
        (congrArg X.level (show r + 1 + n = m + (t + 1) + n by dsimp [r]; omega))
        (PointedCGWH.SequentialSpectrum.adjointStructureMap X r)
        (originalEnrichedRepeatedSphereAdjunct X (r + 1) n)
        (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n) c' c hIndex hTargetEq
      have hCastTail :
          (PointedCGWH.piNFunctor (j + n)).map l2 ≫
            eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X.level (m + ((t + 1) + n))))
              (show j + n = k + ((t + 1) + n) + 1 by dsimp [j]; omega)) ≫
            (forget GrpCat).map (D.map bCast) =
          (PointedCGWH.piNFunctor (j + n)).map c' ≫
            eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj T)
              (show j + n = k + (t + (n + 1)) + 1 by dsimp [j]; omega)) := by
        have hPath : l2 ≫ eqToHom (congrArg X.level
            (show m + ((t + 1) + n) = m + (t + (n + 1)) by omega)) = c' := by
          dsimp only [l2, c']
          rw [eqToHom_trans]
        have hActual := originalPiTargetCastSquare
          (show t + 1 + n = t + (n + 1) by omega)
          (fun q => k + q + 1) (fun q => X.level (m + q)) (j + n)
          (show j + n = k + ((t + 1) + n) + 1 by dsimp [j]; omega)
          l2 c' hPath
          (show j + n = k + (t + (n + 1)) + 1 by dsimp [j]; omega)
        have hBCastPost := congrArg (fun z => (PointedCGWH.piNFunctor (j + n)).map l2 ≫
          eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj (X.level (m + ((t + 1) + n))))
            (show j + n = k + ((t + 1) + n) + 1 by dsimp [j]; omega)) ≫ z) hBCast
        exact hBCastPost.trans hActual




      have hNative := originalNativeShiftComposite_whole n d
        (PointedCGWH.SequentialSpectrum.adjointStructureMap X r)
        (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) c
      have hSourceFull :
          PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫
            PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
            (loopPower (n + 1)).map c =
          originalEnrichedRepeatedSphereAdjunct X r (n + 1) ≫
            (loopPower (n + 1)).map wholeCast := by
        have hMap := (loopPower (n + 1)).map_comp l3 wholeCast
        have hPost :
            PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫
              PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
              ((loopPower (n + 1)).map l3 ≫ (loopPower (n + 1)).map wholeCast) =
            (PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫
              (PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
              (loopPower (n + 1)).map l3)) ≫ (loopPower (n + 1)).map wholeCast := by
          exact (congrArg (fun z => PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫ z)
            (Category.assoc
              (PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n))
              ((loopPower (n + 1)).map l3) ((loopPower (n + 1)).map wholeCast)).symm).trans
            (Category.assoc
              (PointedCGWH.SequentialSpectrum.adjointStructureMap X r)
              (PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
                (loopPower (n + 1)).map l3)
              ((loopPower (n + 1)).map wholeCast)).symm
        have hSourcePost := originalPostSourceRecurrence
          (PointedCGWH.SequentialSpectrum.adjointStructureMap X r)
          (PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫
            (loopPower (n + 1)).map l3)
          ((loopPower (n + 1)).map wholeCast)
          (originalEnrichedRepeatedSphereAdjunct X r (n + 1)) hSourceWord
        exact (congrArg (fun z => PointedCGWH.SequentialSpectrum.adjointStructureMap X r ≫
          PointedCGWH.loop.map (originalEnrichedRepeatedSphereAdjunct X (r + 1) n) ≫ z) hMap).trans
          (hPost.trans (by simpa only [Category.assoc] using hSourcePost))
      have hMapSource := (PointedCGWH.piNFunctor d).congr_map hSourceFull
      have hTarget := (loopPowerPiShift (n + 1) d).hom.naturality wholeCast
      have hTailPost := congrArg (fun z =>
        (PointedCGWH.piNFunctor d).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X r) ≫
        (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso d).hom.app B ≫
        (PointedCGWH.piNFunctor (d + 1)).map l1 ≫
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj B') hDegree) ≫
        (PointedCGWH.piNFunctor j).map (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n) ≫
        (loopPowerPiShift n j).hom.app C' ≫ z) hCastTail
      have hDegreeEnd :
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj T)
          (show j + n = k + (t + (n + 1)) + 1 by dsimp [j]; omega)) =
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor (q + n)).obj T) hDegree.symm) ≫
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj T)
          (show d + 1 + n = d + (n + 1) by omega)) ≫ degreeCast := by
        dsimp only [degreeCast]
        rw [eqToHom_trans, eqToHom_trans]
      have hCastCompositePost := congrArg (fun z => z ≫
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj T)
          (show d + 1 + n = d + (n + 1) by omega)) ≫ degreeCast) hCastComposite
      have hNativePost := congrArg (fun z => z ≫ degreeCast) hNative
      have hSourcePost := congrArg (fun z => (PointedCGWH.piNFunctor d).map z ≫
        (loopPowerPiShift (n + 1) d).hom.app T ≫ degreeCast) hSourceFull
      have hTargetPost := congrArg (fun z => (PointedCGWH.piNFunctor d).map
        (originalEnrichedRepeatedSphereAdjunct X r (n + 1)) ≫ z ≫ degreeCast) hTarget
      have hLeftNormalized := hTailPost
      have hAfterDegree := congrArg (fun z =>
        (PointedCGWH.piNFunctor d).map (PointedCGWH.SequentialSpectrum.adjointStructureMap X r) ≫
        (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso d).hom.app B ≫
        (PointedCGWH.piNFunctor (d + 1)).map l1 ≫
        eqToHom (congrArg (fun q => (PointedCGWH.piNFunctor q).obj B') hDegree) ≫
        (PointedCGWH.piNFunctor j).map (originalEnrichedRepeatedSphereAdjunct X (m + (t + 1)) n) ≫
        (loopPowerPiShift n j).hom.app C' ≫
        (PointedCGWH.piNFunctor (j + n)).map c' ≫ z) hDegreeEnd
      have hMapSourceComp := (PointedCGWH.piNFunctor d).map_comp
        (originalEnrichedRepeatedSphereAdjunct X r (n + 1)) ((loopPower (n + 1)).map wholeCast)
      have hSourceCompPost := congrArg (fun z => z ≫
        (loopPowerPiShift (n + 1) d).hom.app T ≫ degreeCast) hMapSourceComp
      have hTargetNormalized :
          ((PointedCGWH.piNFunctor d).map (originalEnrichedRepeatedSphereAdjunct X r (n + 1)) ≫
            (PointedCGWH.piNFunctor d).map ((loopPower (n + 1)).map wholeCast)) ≫
            (loopPowerPiShift (n + 1) d).hom.app T ≫ degreeCast =
          (PointedCGWH.piNFunctor d).map (originalEnrichedRepeatedSphereAdjunct X r (n + 1)) ≫
            (loopPowerPiShift (n + 1) d).hom.app (X.level (r + (n + 1))) ≫
            (PointedCGWH.piNFunctor (d + (n + 1))).map wholeCast ≫ degreeCast := by
        simpa only [Functor.comp_map, Category.assoc] using hTargetPost
      have hRight := hNativePost.trans
        (hSourcePost.trans (hSourceCompPost.trans hTargetNormalized))
      exact hLeftNormalized.trans (hAfterDegree.trans (hCastCompositePost.trans hRight))





    exact hApplied.trans hFinal


end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaDiagonalPower

section NativeGammaSphereSource


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory
open CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open PointedCGWH.SphereHom
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

theorem originalIsoSourceHomWord {C : Type*} [Category C] [MonoidalCategory C]
    {A U P T : C} (v : A ≅ P ⊗ U) (u : U ≅ 𝟙_ C) (c : P ≅ T) :
    ((v ≪≫ tensorIso (Iso.refl P) u ≪≫ ρ_ P) ≪≫ c).hom =
      v.hom ≫ (P ◁ u.hom) ≫ (ρ_ P).hom ≫ c.hom := by
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, Category.assoc]

/-- The complete free-point unit and original coefficient multiplication retain the original tensor source. -/
theorem originalCanonicalTensorSourceWord {C : Type*} [Category C] [MonoidalCategory C]
    {P Q R P' Q' R' U V A B : C}
    (eU : U ≅ 𝟙_ C) (p : P ≅ P') (q : Q ≅ Q') (r : R ≅ R')
    (v : V ≅ Q ⊗ U) (d : R ≅ P ⊗ Q)
    (m : P' ⊗ Q' ⟶ R') (s : A ⟶ B) (e : B ⟶ P ⊗ V) (w : A ⟶ R ⊗ U)
    (hSplit : s ≫ e ≫ (P ◁ v.hom) ≫ (α_ P Q U).inv = w ≫ (d.hom ▷ U))
    (hCoeff : d.inv ≫ r.hom = (p.hom ⊗ₘ q.hom) ≫ m) :
    s ≫ e ≫ (P ◁ (v.hom ≫ (Q ◁ eU.hom) ≫ (ρ_ Q).hom ≫ q.hom)) ≫
        (p.hom ▷ Q') ≫ m =
      w ≫ (R ◁ eU.hom) ≫ (ρ_ R).hom ≫ r.hom := by
  have hNat :
      (P ◁ (Q ◁ eU.hom)) ≫ (P ◁ (ρ_ Q).hom) =
        (α_ P Q U).inv ≫ ((P ⊗ Q) ◁ eU.hom) ≫ (ρ_ (P ⊗ Q)).hom := by
    monoidal
  have hCoeff' : (p.hom ⊗ₘ q.hom) ≫ m = d.inv ≫ r.hom := hCoeff.symm
  have hTarget :
      (d.hom ▷ U) ≫ ((P ⊗ Q) ◁ eU.hom) ≫ (ρ_ (P ⊗ Q)).hom ≫ d.inv ≫ r.hom =
        (R ◁ eU.hom) ≫ (ρ_ R).hom ≫ r.hom := by
    have hExchange : (d.hom ▷ U) ≫ ((P ⊗ Q) ◁ eU.hom) =
        (R ◁ eU.hom) ≫ (d.hom ▷ (𝟙_ C)) :=
      (whisker_exchange d.hom eU.hom).symm
    have hUnitor : (d.hom ▷ (𝟙_ C)) ≫ (ρ_ (P ⊗ Q)).hom = (ρ_ R).hom ≫ d.hom :=
      rightUnitor_naturality d.hom
    rw [← Category.assoc (d.hom ▷ U) ((P ⊗ Q) ◁ eU.hom), hExchange]
    simp only [Category.assoc]
    rw [← Category.assoc (d.hom ▷ (𝟙_ C)) (ρ_ (P ⊗ Q)).hom, hUnitor]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← Category.assoc (P ◁ q.hom) (p.hom ▷ Q') m,
    ← tensorHom_def', hCoeff']
  rw [← Category.assoc (P ◁ (Q ◁ eU.hom)) (P ◁ (ρ_ Q).hom), hNat]
  have h := congrArg (fun z => z ≫ ((P ⊗ Q) ◁ eU.hom) ≫
    (ρ_ (P ⊗ Q)).hom ≫ d.inv ≫ r.hom) hSplit
  have hFinal :
      (w ≫ (d.hom ▷ U)) ≫ ((P ⊗ Q) ◁ eU.hom) ≫ (ρ_ (P ⊗ Q)).hom ≫ d.inv ≫ r.hom =
        w ≫ (R ◁ eU.hom) ≫ (ρ_ R).hom ≫ r.hom := by
    simpa only [Category.assoc] using congrArg (fun z => w ≫ z) hTarget
  simpa only [Category.assoc] using h.trans hFinal


attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

theorem originalOrderedCoefficientTensor (a b : ℕ) :
    (MonoidalCategory.TensorPower.tensorPowObj_add PointedCGWH.sphereOne.{u, v} a b).inv ≫
        (orderedCoefficientIso (a + b)).hom =
      ((orderedCoefficientIso a).hom ⊗ₘ (orderedCoefficientIso b).hom) ≫
        orthogonalSphereMonoidalData.{u, v}.mu a b := by
  have h := originalSymmetricOrthogonalCoefficientNatIso_tensor.{u, v}
    (Sequential.finiteIndex a) (Sequential.finiteIndex b)
  rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component,
    originalSymmetricOrthogonalCoefficientNatIso_hom_component,
    originalSymmetricOrthogonalCoefficientNatIso_hom_component] at h
  exact h

theorem originalNativeSphereSourceIso_add (b a : ℕ) :
    eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd b a) freePoint) ≫
      (spherePowerValueIso b (sphere a)).hom ≫
      (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne b ◁
        (nativeSphereSourceIso a).hom) ≫
      ((orderedCoefficientIso b).hom ▷ PointedCGWH.orthogonalSphere a) ≫
      orthogonalSphereMonoidalData.{u, v}.mu b a =
    (nativeSphereSourceIso (b + a)).hom := by
  have h := originalCanonicalTensorSourceWord freePointUnitIso
    (orderedCoefficientIso b) (orderedCoefficientIso a)
    (orderedCoefficientIso (b + a)) (spherePowerValueIso a freePoint)
    (MonoidalCategory.TensorPower.tensorPowObj_add PointedCGWH.sphereOne b a)
    (orthogonalSphereMonoidalData.{u, v}.mu b a)
    (eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd b a) freePoint))
    (spherePowerValueIso b (sphere a)).hom (spherePowerValueIso (b + a) freePoint).hom
    (originalSpherePowerValueIso_ordered_add b a freePoint)
    (originalOrderedCoefficientTensor b a)
  have hNative (k : ℕ) : (nativeSphereSourceIso.{u, v} k).hom =
      (spherePowerValueIso k freePoint).hom ≫
        (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne k ◁ freePointUnitIso.hom) ≫
        (ρ_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne k)).hom ≫
        (orderedCoefficientIso k).hom := by
    exact originalIsoSourceHomWord (spherePowerValueIso k freePoint) freePointUnitIso
      (orderedCoefficientIso k)
  rw [hNative a, hNative (b + a)]
  exact h


end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaSphereSource

section NativeGammaIntegerPowerFormula


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- Every actual integer-stage advance is the original power adjunct and complete degree/level transport. -/
theorem integerStageAdvance_power_formula (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (x : ((integerDiagonalFunctor q).obj X).obj t) :
    (integerStageAdvance q X t n).hom x =
      (eqToHom (congrArg (fun j => (PointedCGWH.piNFunctor j).obj
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))))
        (show integerTailPositiveIndex q + t + 1 + n = integerTailPositiveIndex q + (t + n) + 1 by omega)))
      (PointedCGWH.piNMap (integerTailPositiveIndex q + t + 1 + n)
        (eqToHom (congrArg (fun j => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex j))
          (show integerTailLevel q + t + n = integerTailLevel q + (t + n) by omega)))
        ((loopPowerPiShift n (integerTailPositiveIndex q + t + 1)).hom.app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)))
          (PointedCGWH.piNMap (integerTailPositiveIndex q + t + 1)
            (originalEnrichedRepeatedSphereAdjunct (underlyingSequential.obj X) (integerTailLevel q + t) n) x))) := by
  exact ConcreteCategory.congr_hom
    (originalDiagonalMap_power_whole (underlyingSequential.obj X)
      (integerTailLevel q) (integerTailPositiveIndex q) t n) x

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaIntegerPowerFormula

section NativeGammaIntegerPointedClass


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant

theorem originalNativePowerSourceClass (d n : ℕ) (A D : PointedCGWH.{u, v})
    (f : sphere d ⟶ A) (h : A ⟶ (loopPower n).obj D) :
    (spherePiHomEquiv (d + n) D).symm
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
        (eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
          ((powerAdjunction n).homEquiv (sphere d) D).symm (f ≫ h))) =
      ((loopPowerPiShift n d).app D).toEquiv
        (PointedCGWH.piNMap d h
          ((spherePiHomEquiv d A).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f))) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  let _ : IsCofibrant (sphere.{u, v} d) := FreeSphereHom.sphere_isCofibrant d
  have hClass := originalSpherePiHomEquiv_power_adjunct n d D
    (((powerAdjunction n).homEquiv (sphere d) D).symm (f ≫ h))
  have hAdj := QuillenOrdinaryHoHom.homEquiv_map (powerAdjunction n) (sphere d) D
    (((powerAdjunction n).homEquiv (sphere d) D).symm (f ≫ h))
  have hActual := ((powerAdjunction n).homEquiv (sphere d) D).apply_symm_apply (f ≫ h)
  have hNat := spherePiHomEquiv_naturality d h
    ((spherePiHomEquiv d A).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f))
  have hMap :
      QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) (sphere d) D
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
          (((powerAdjunction n).homEquiv (sphere d) D).symm (f ≫ h))) =
      (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f ≫ (HomotopicalAlgebra.toHomotopyCategory
        PointedCGWH).map h :=
    hAdj.trans (((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).congr_map hActual).trans
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map_comp f h))
  have hInverse :
      (spherePiHomEquiv d ((loopPower n).obj D)).symm
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f ≫ (HomotopicalAlgebra.toHomotopyCategory
          PointedCGWH).map h) =
      PointedCGWH.piNMap d h
        ((spherePiHomEquiv d A).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) := by
    apply (spherePiHomEquiv d ((loopPower n).obj D)).injective
    exact ((spherePiHomEquiv d ((loopPower n).obj D)).apply_symm_apply _).trans
      (hNat.trans (congrArg (fun z => z ≫ (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map h)
        ((spherePiHomEquiv d A).apply_symm_apply _))).symm
  exact hClass.trans (congrArg (((loopPowerPiShift n d).app D).toEquiv)
    ((congrArg (spherePiHomEquiv d ((loopPower n).obj D)).symm hMap).trans hInverse))

theorem originalSphereClassDegreeCast {a b : ℕ} (h : a = b) (X : PointedCGWH.{u, v})
    (f : sphere a ⟶ X) :
    (Equiv.cast (congrArg (fun n => PointedCGWH.piN n X) h))
      ((spherePiHomEquiv a X).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map f)) =
    (spherePiHomEquiv b X).symm
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
        (eqToHom (congrArg sphere h.symm) ≫ f)) := by
  cases h
  have hSource : eqToHom (congrArg sphere (Eq.refl a).symm) ≫ f = f :=
    Category.id_comp f
  exact (congrArg (fun g => (spherePiHomEquiv a X).symm
    ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map g)) hSource).symm


/-- Both original scalar-sphere correspondence functions retain every pointed target arrow. -/
theorem scalarSphereClass_postcompose (d : ℕ) {A D : PointedCGWH.{u, v}}
    (p : sphere d ⟶ A) (g : A ⟶ D) :
    (spherePiHomEquiv d D).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map (p ≫ g)) =
      PointedCGWH.piNMap d g
        ((spherePiHomEquiv d A).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map p)) := by
  apply (spherePiHomEquiv d D).injective
  rw [Equiv.apply_symm_apply, spherePiHomEquiv_naturality, Equiv.apply_symm_apply, Functor.map_comp]

/-- The original n-fold pointed representative source at its exact later integer level and degree. -/
def integerPointedPowerSource (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X) :
    sphere (integerTailPositiveIndex q + (t + n) + 1) ⟶
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))) :=
  let d := integerTailPositiveIndex q + t + 1
  let r := integerTailLevel q + t
  let D := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n))
  let p := (nativeSphereSourceIso d).hom ≫ Free.evaluate (OrthogonalOperatorIndex.ofIndex r)
    (PointedCGWH.orthogonalSphere d) X f
  let h := originalEnrichedRepeatedSphereAdjunct (underlyingSequential.obj X) r n
  let z := eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
    ((powerAdjunction n).homEquiv (sphere d) D).symm (p ≫ h)
  let target := eqToHom (congrArg
    (fun j => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex j))
    (show r + n = integerTailLevel q + (t + n) by dsimp only [r]; omega))
  let degree : d + n = integerTailPositiveIndex q + (t + n) + 1 := by dsimp only [d]; omega
  eqToHom (congrArg sphere degree.symm) ≫ (z ≫ target)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

/-- The original native free representative has its exact original stage class. -/
def integerNativeFreeClass (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X) :
    PointedCGWH.piN (integerTailPositiveIndex q + t + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))) :=
  (nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
    (integerTailPositiveIndex q + t + 1) X).symm
    ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier).map f)

/-- The original pointed power source has its actual later-stage class. -/
def integerPointedPowerClass (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X) :
    PointedCGWH.piN (integerTailPositiveIndex q + (t + n) + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))) :=
    (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))))).symm
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map (integerPointedPowerSource q X t n f))

set_option maxRecDepth 1024 in
/-- Every exact original pointed source represents the same actual n-step integer diagram action. -/
theorem integerPointedPowerSource_class (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶ X) :
    integerPointedPowerClass q X t n f = (integerStageAdvance q X t n).hom (integerNativeFreeClass q X t f) := by
  let d := integerTailPositiveIndex q + t + 1
  let r := integerTailLevel q + t
  let A := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)
  let D := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n))
  let E := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
  let p := (nativeSphereSourceIso d).hom ≫ Free.evaluate (OrthogonalOperatorIndex.ofIndex r)
    (PointedCGWH.orthogonalSphere d) X f
  let h := originalEnrichedRepeatedSphereAdjunct (underlyingSequential.obj X) r n
  let z := eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
    ((powerAdjunction n).homEquiv (sphere d) D).symm (p ≫ h)
  let target : D ⟶ E := eqToHom (congrArg
    (fun j => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex j))
    (show r + n = integerTailLevel q + (t + n) by dsimp only [r]; omega))
  let degree : d + n = integerTailPositiveIndex q + (t + n) + 1 := by dsimp only [d]; omega
  have hDegree := originalSphereClassDegreeCast degree E (z ≫ target)
  have hPost := scalarSphereClass_postcompose (d + n) z target
  have hPower := originalNativePowerSourceClass d n A D p h
  have hNative := nativeSphereClass_evaluate (OrthogonalOperatorIndex.ofIndex r) d X f
  have hOriginal := integerStageAdvance_power_formula q X t n
    ((nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex r) d X).symm
      ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier).map f))
  let move := Equiv.cast (congrArg (fun j => PointedCGWH.piN j E) degree)
  have hNativeMoved := congrArg (fun x => (loopPowerPiShift n d).hom.app D
    (PointedCGWH.piNMap d h x)) hNative.symm
  have hBase := hPower.trans hNativeMoved
  have hMapped := congrArg (PointedCGWH.piNMap (d + n) target) hBase
  have hPointed := hPost.trans hMapped
  have hNormal := hDegree.symm.trans (congrArg move hPointed)
  have hCast := originalTypeEqToHom_apply
    (congrArg (fun j => (PointedCGWH.piNFunctor j).obj E) degree)
    (PointedCGWH.piNMap (d + n) target
      ((loopPowerPiShift n d).hom.app D
        (PointedCGWH.piNMap d h ((nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex r) d X).symm
          ((HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier).map f)))))
  have hAdvance := hCast.symm.trans hOriginal.symm
  have hFinal := hNormal.trans hAdvance
  simpa only [integerPointedPowerClass, integerPointedPowerSource, integerNativeFreeClass,
    d, r, D, E, p, h, z, target, move, Category.assoc] using hFinal

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaIntegerPointedClass

section NativeGammaSourceReadbackBridge


set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.SphereHom
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- The full original scalar sphere, integer source cast and native free evaluation read the same mixed map. -/
def mixedPointedReadback (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    sphere (integerTailPositiveIndex q + (t + n) + 1) ⟶
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))) :=
  (nativeSphereSourceIso (integerTailPositiveIndex q + (t + n) + 1)).hom ≫
    Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + (t + n) + 1)) X
      ((integerMixedSourceIso q t n).hom ≫ g)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The original mixed integer class retains its entire original pointed source readback. -/
theorem mixedIntegerClass_eq_scalarReadback (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    mixedIntegerClass q t n X g =
      (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1)
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))))).symm
        ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map (mixedPointedReadback q X t n g)) :=
  nativeSphereClass_evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
    (integerTailPositiveIndex q + (t + n) + 1) X ((integerMixedSourceIso q t n).hom ≫ g)

/-- A proved equality of the complete original pointed source maps identifies the actual n-step integer class. -/
theorem mixedIntegerClass_eq_advance_of_pointedSource (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X)
    (h : mixedPointedReadback q X t n g = integerPointedPowerSource q X t n f) :
    mixedIntegerClass q t n X g = (integerStageAdvance q X t n).hom (integerNativeFreeClass q X t f) := by
  have he := mixedIntegerClass_eq_scalarReadback q X t n g
  have hm := (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).congr_map h
  have hc := congrArg
    (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))))).symm hm
  exact he.trans (hc.trans (integerPointedPowerSource_class q X t n f))

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaSourceReadbackBridge

section NativeGammaFinalUnitLift


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Spectra
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily

section Ordinary
universe uV vV uD vD
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {D : Type uD} [Category.{vD} D]

/-- The actual arbitrary unit map is retained throughout the whole lift family. -/
def LiftType (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V) : Type _ :=
  letI := M
  ∀ (n r : ℕ) (K : V), (P r K ⟶ 𝟙_ D) → (P (n + r) (S n ⊗ K) ⟶ P n (S n))

/-- The original pair inverse and right unitor construct every original unit lift. -/
def liftFamily (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (pair : Independent.PairFormula M P (fun n r => n + r)) : LiftType M P S := by
  letI := M
  intro n r K f
  exact (pair n r (S n) K).inv ≫ P n (S n) ◁ f ≫ (ρ_ (P n (S n))).hom

/-- Both original unit words preserve the complete Gamma and arbitrary second-factor map. -/
theorem unitGammaFactor (M : MonoidalCategory D) :
    letI := M
    ∀ {A K : D} (g : A ⟶ 𝟙_ D) (f : K ⟶ 𝟙_ D),
      A ◁ f ≫ (ρ_ A).hom ≫ g = (g ⊗ₘ 𝟙 K) ≫ (λ_ K).hom ≫ f := by
  let := M
  intro A K g f
  simp only [tensorHom_id]
  rw [← rightUnitor_naturality g, ← unitors_equal, whisker_exchange_assoc,
    leftUnitor_naturality]

/-- Composing a unit lift with `gamma n` equals the left Gamma face followed by the original
unit-target map. -/
def LiftGammaFormula (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : Independent.GammaType M P S) (lifts : LiftType M P S)
    (faces : Independent.LeftFaceType P S) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K : V) (f : P r K ⟶ 𝟙_ D),
    lifts n r K f ≫ gamma n = faces n r K ≫ f

/-- The whole right-unit lift family has precisely the original left Gamma composite. -/
theorem liftFamily_gamma (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : Independent.GammaType M P S)
    (pair : Independent.PairFormula M P (fun n r => n + r)) :
    LiftGammaFormula M P S gamma (liftFamily M P S pair)
      (Independent.leftFaceFamily M P S gamma pair) := by
  let := M
  intro n r K f
  simp only [liftFamily, Independent.leftFaceFamily, Category.assoc]
  rw [unitGammaFactor M]

end Ordinary

/-- Every actual unit representative is lifted on the original native monoidal pointer. -/
def nativeUnitLift : LiftType CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} :=
  liftFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v}

/-- The actual whole native lift retains the literal original Gamma-left map on every unit map. -/
theorem nativeUnitLift_gamma : LiftGammaFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v}
    nativeUnitLift.{u, v} nativeLeftFaces.{u, v} :=
  liftFamily_gamma CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v}

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily

end

end NativeGammaFinalUnitLift

section NativeGammaFinalUnitInteger


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The arbitrary original free unit map is lifted at its exact original later integer stage. -/
def unitLiftIntegerClass (n : ℕ) (q : ℤ) (t : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶
        𝟙_ CanonicalSourceSmash.Carrier.{u, v}) : (integerPiFunctor q).obj (sphereFree.{u, v} n) :=
  (integerPiLeg q (sphereFree n) (t + n)).hom
    (mixedIntegerClass q t n (sphereFree n)
      (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) f))

/-- The lift has precisely the literal original Gamma-left representative at the same later stage. -/
theorem unitLiftIntegerClass_gamma (n : ℕ) (q : ℤ) (t : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere.{u, v} (integerTailPositiveIndex q + t + 1)) ⟶
        𝟙_ CanonicalSourceSmash.Carrier.{u, v}) :
    ((integerPiFunctor q).map (gamma n)).hom (unitLiftIntegerClass n q t f) =
      (integerPiLeg q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) (t + n)).hom
        (mixedIntegerClass q t n (𝟙_ CanonicalSourceSmash.Carrier.{u, v})
          (nativeLeftFaces n (integerTailLevel q + t)
            (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f)) := by
  have h := mixedIntegerLeg_postcompose q t n (gamma n)
    (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) f)
  have hLift := UnitLiftFamily.nativeUnitLift_gamma.{u, v}
    n (integerTailLevel q + t)
    (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) f
  rw [hLift] at h
  exact h

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end NativeGammaFinalUnitInteger

section NativeGammaFinalScalarNativeSource


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.SphereHom
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory

/-- The original degree equality retains both scalar and native sphere comparison maps. -/
theorem nativeSphereSourceIso_cast {a b : ℕ} (h : a = b) :
    eqToHom (congrArg sphere.{u, v} h) ≫ (nativeSphereSourceIso b).hom =
      (nativeSphereSourceIso a).hom ≫ eqToHom (congrArg PointedCGWH.orthogonalSphere h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The ordered and original sphere-power source equalities retain the same actual source map. -/
theorem orderedSphereSourceCast (d n : ℕ) :
    eqToHom (congrArg sphere.{u, v} (Nat.add_comm d n)) ≫
      eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd n d) freePoint) =
    eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) := by
  rw [eqToHom_trans]

/-- The original mixed coefficient is the complete original pointed power source split. -/
theorem mixedCoefficientScalarSource (n d : ℕ) :
    (nativeSphereSourceIso.{u, v} (d + n)).hom ≫ (mixedCoefficientIso n d).hom =
      eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
        (spherePowerValueIso n (sphere d)).hom ≫
        (TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ (nativeSphereSourceIso d).hom) ≫
        ((orderedCoefficientIso n).hom ▷ PointedCGWH.orthogonalSphere d) := by
  let e := PointedCGWH.orthogonalSphereTensorIso.{u, v} n d
  have h := originalNativeSphereSourceIso_add n d
  have hMu : orthogonalSphereMonoidalData.{u, v}.mu n d = e.inv := rfl
  rw [hMu] at h
  have hSplit := congrArg (fun z => z ≫ e.hom) h
  have hSource :
      eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd n d) freePoint) ≫
        (spherePowerValueIso n (sphere d)).hom ≫
        (TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ (nativeSphereSourceIso d).hom) ≫
        ((orderedCoefficientIso n).hom ▷ PointedCGWH.orthogonalSphere d) =
      (nativeSphereSourceIso (n + d)).hom ≫ e.hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hSplit
  have hCast := nativeSphereSourceIso_cast.{u, v} (Nat.add_comm d n)
  calc
    _ = (nativeSphereSourceIso (d + n)).hom ≫
        eqToHom (congrArg PointedCGWH.orthogonalSphere (Nat.add_comm d n)) ≫ e.hom := rfl
    _ = eqToHom (congrArg sphere (Nat.add_comm d n)) ≫
        (nativeSphereSourceIso (n + d)).hom ≫ e.hom := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ e.hom) hCast.symm
    _ = eqToHom (congrArg sphere (Nat.add_comm d n)) ≫
        (eqToHom (Functor.congr_obj (originalSphereTensorPowerOrderedAdd n d) freePoint) ≫
          (spherePowerValueIso n (sphere d)).hom ≫
          (TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ (nativeSphereSourceIso d).hom) ≫
          ((orderedCoefficientIso n).hom ▷ PointedCGWH.orthogonalSphere d)) :=
      congrArg (fun z => eqToHom (congrArg sphere (Nat.add_comm d n)) ≫ z) hSource.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (spherePowerValueIso n (sphere d)).hom ≫
          (TensorPower.tensorPowObj PointedCGWH.sphereOne n ◁ (nativeSphereSourceIso d).hom) ≫
          ((orderedCoefficientIso n).hom ▷ PointedCGWH.orthogonalSphere d))
        (orderedSphereSourceCast d n)

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalScalarNativeSource

section NativeGammaFinalPointedPowerSource


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SphereHom
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The complete original pointed n-fold source, before the later integer casts. -/
def pointedPowerSource (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) ⟶ X) :
    sphere (d + n) ⟶ X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n)) :=
  eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
    ((powerAdjunction n).homEquiv (sphere d)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n)))).symm
      ((nativeSphereSourceIso d).hom ≫
        Free.evaluate (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) X f ≫
          originalEnrichedRepeatedSphereAdjunct (underlyingSequential.obj X) r n)

/-- The same pointed power source retains the complete native evaluation, coefficient and target word. -/
theorem pointedPowerSource_formula (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) ⟶ X) :
    pointedPowerSource X r d n f =
      (nativeSphereSourceIso (d + n)).hom ≫ (mixedCoefficientIso n d).hom ≫
        (PointedCGWH.orthogonalSphere n ◁
          Free.evaluate (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) X f) ≫
        (β_ (PointedCGWH.orthogonalSphere n)
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r))).hom ≫
        sphereAction X r n ≫ Sequential.indexMap X (orderedTargetIso r n).hom := by
  let S : PointedCGWH.SequentialSpectrum.{u, v} := underlyingSequential.obj X
  let A := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)
  let D := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n))
  let P := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} n
  let Sn := PointedCGWH.orthogonalSphere.{u, v} n
  let Sd := PointedCGWH.orthogonalSphere.{u, v} d
  let ev := Free.evaluate (OrthogonalOperatorIndex.ofIndex r) Sd X f
  let p : sphere d ⟶ A := (nativeSphereSourceIso d).hom ≫ ev
  let src := eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint)
  let j := CategoryTheory.SequentialSpectrum.iteratedStructureMap
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor PointedCGWH.sphereOne S) n r ≫
      eqToHom (congrArg S.level (Nat.add_comm n r))
  let native := (β_ Sn A).hom ≫ sphereAction X r n ≫
    Sequential.indexMap X (orderedTargetIso r n).hom
  have hAdj :
      ((powerAdjunction n).homEquiv (sphere d) D).symm
        (p ≫ originalEnrichedRepeatedSphereAdjunct S r n) =
      (sphereTensorPower n).map p ≫ originalEnrichedRepeatedSphereStructure S r n := by
    change ((powerAdjunction n).homEquiv (sphere d) D).symm
      (p ≫ ((powerAdjunction n).homEquiv A D) (originalEnrichedRepeatedSphereStructure S r n)) = _
    rw [(powerAdjunction n).homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hStructure : originalEnrichedRepeatedSphereStructure S r n =
      (spherePowerValueIso n A).hom ≫ j := rfl
  have hValue := originalSpherePowerValueIso_naturality n p
  have hFinite : j = ((orderedCoefficientIso n).hom ▷ A) ≫ native :=
    finiteNativeAction X r n
  have hExchange : (P ◁ ev) ≫ ((orderedCoefficientIso n).hom ▷ A) =
      ((orderedCoefficientIso n).hom ▷ Sd) ≫ (Sn ◁ ev) :=
    whisker_exchange (orderedCoefficientIso n).hom ev
  have hMixed :
      src ≫ (spherePowerValueIso n (sphere d)).hom ≫ (P ◁ p) ≫
        ((orderedCoefficientIso n).hom ▷ A) =
      (nativeSphereSourceIso (d + n)).hom ≫ (mixedCoefficientIso n d).hom ≫ (Sn ◁ ev) := by
    calc
      _ = (src ≫ (spherePowerValueIso n (sphere d)).hom ≫
          (P ◁ (nativeSphereSourceIso d).hom)) ≫
            ((P ◁ ev) ≫ ((orderedCoefficientIso n).hom ▷ A)) := by
        simp only [p, whiskerLeft_comp, Category.assoc]
      _ = (src ≫ (spherePowerValueIso n (sphere d)).hom ≫
          (P ◁ (nativeSphereSourceIso d).hom)) ≫
            (((orderedCoefficientIso n).hom ▷ Sd) ≫ (Sn ◁ ev)) :=
        congrArg (fun z => (src ≫ (spherePowerValueIso n (sphere d)).hom ≫
          (P ◁ (nativeSphereSourceIso d).hom)) ≫ z) hExchange
      _ = _ := by
        simpa only [src, P, Sd, Category.assoc] using congrArg
          (fun z => z ≫ (Sn ◁ ev)) (mixedCoefficientScalarSource.{u, v} n d).symm
  calc
    _ = src ≫ ((sphereTensorPower n).map p ≫ originalEnrichedRepeatedSphereStructure S r n) :=
      congrArg (fun z => src ≫ z) hAdj
    _ = src ≫ ((sphereTensorPower n).map p ≫ (spherePowerValueIso n A).hom) ≫ j := by
      rw [hStructure]
      simp only [Category.assoc]
    _ = src ≫ ((spherePowerValueIso n (sphere d)).hom ≫ (P ◁ p)) ≫ j :=
      congrArg (fun z => src ≫ z ≫ j) hValue
    _ = (src ≫ (spherePowerValueIso n (sphere d)).hom ≫ (P ◁ p) ≫
        ((orderedCoefficientIso n).hom ▷ A)) ≫ native := by
      rw [hFinite]
      simp only [Category.assoc]
    _ = ((nativeSphereSourceIso (d + n)).hom ≫ (mixedCoefficientIso n d).hom ≫ (Sn ◁ ev)) ≫ native :=
      congrArg (fun z => z ≫ native) hMixed
    _ = _ := by simp only [Sn, A, ev, Sd, native, Category.assoc]

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalPointedPowerSource

section NativeGammaFinalCastReadback


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SphereHom
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The complete original source label equality on the original mixed coefficient. -/
def mixedLabelCast (n r d : ℕ) :
    Free.object (OrthogonalOperatorIndex.ofIndex (r + n))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ PointedCGWH.orthogonalSphere d) ⟶
    mixedFree.{u, v} n r d :=
  eqToHom (congrArg (fun a => Free.object (OrthogonalOperatorIndex.ofIndex a)
    (PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d)) (Nat.add_comm r n))

/-- Evaluation after the same original n+r/r+n source label cast. -/
def rawMixedEvaluate (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (g : mixedFree.{u, v} n r d ⟶ X) :
    PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d ⟶
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n)) :=
  Free.evaluate (OrthogonalOperatorIndex.ofIndex (r + n))
    (PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d) X
    (mixedLabelCast n r d ≫ g)

/-- The full original mixed source keeps its coefficient map and its original source label equality. -/
theorem mixedSourceIso_evaluate (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (g : mixedFree.{u, v} n r d ⟶ X) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex (r + n))
      (PointedCGWH.orthogonalSphere (d + n)) X ((mixedSourceIso n r d).hom ≫ g) =
    (mixedCoefficientIso n d).hom ≫ rawMixedEvaluate X r d n g := by
  change Free.evaluate (OrthogonalOperatorIndex.ofIndex (r + n))
    (PointedCGWH.orthogonalSphere (d + n)) X
      (((Free.functor (OrthogonalOperatorIndex.ofIndex (r + n))).map
        (mixedCoefficientIso n d).hom ≫ mixedLabelCast n r d) ≫ g) =
    (mixedCoefficientIso n d).hom ≫
      Free.evaluate (OrthogonalOperatorIndex.ofIndex (r + n))
        (PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d) X (mixedLabelCast n r d ≫ g)
  rw [Category.assoc]
  exact evaluate_coefficient (OrthogonalOperatorIndex.ofIndex (r + n))
    (mixedCoefficientIso.{u, v} n d).hom X (mixedLabelCast n r d ≫ g)

/-- Every original free source cast retains its two sphere maps and original target cast. -/
theorem freeSourceCast_readback {a b c d : ℕ} (ha : a = b) (hc : c = d)
    (X : Actual.OrthogonalCarrier.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex b) (PointedCGWH.orthogonalSphere d) ⟶ X) :
    (nativeSphereSourceIso c).hom ≫
      Free.evaluate (OrthogonalOperatorIndex.ofIndex a) (PointedCGWH.orthogonalSphere c) X
        ((freeSourceCast ha hc).hom ≫ g) =
      eqToHom (congrArg sphere hc) ≫ (nativeSphereSourceIso d).hom ≫
        Free.evaluate (OrthogonalOperatorIndex.ofIndex b) (PointedCGWH.orthogonalSphere d) X g ≫
          eqToHom (congrArg (fun j => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex j)) ha.symm) := by
  cases ha
  cases hc
  simp only [freeSourceCast, Iso.refl_hom, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The original later signed-degree source cast into its d+n scalar sphere. -/
def integerSphereCast (q : ℤ) (t n : ℕ) :
    sphere.{u, v} (integerTailPositiveIndex q + (t + n) + 1) ⟶
      sphere (integerTailPositiveIndex q + t + 1 + n) :=
  eqToHom (congrArg sphere (show integerTailPositiveIndex q + (t + n) + 1 =
    integerTailPositiveIndex q + t + 1 + n by omega))

/-- The original r+n/later-stage target equality acts on the full original native level. -/
def integerTargetCast (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ) :
    X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)) ⟶
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n))) :=
  eqToHom (congrArg (fun j => X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex j))
    (show integerTailLevel q + t + n = integerTailLevel q + (t + n) by omega))

/-- The entire original raw finite action word, with actual evaluation and target permutation. -/
def rawPowerAction (X : Actual.OrthogonalCarrier.{u, v}) (r d n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) ⟶ X) :
    PointedCGWH.orthogonalSphere n ⊗ PointedCGWH.orthogonalSphere d ⟶
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (r + n)) :=
  (PointedCGWH.orthogonalSphere n ◁
    Free.evaluate (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) X f) ≫
    (β_ (PointedCGWH.orthogonalSphere n)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r))).hom ≫
    sphereAction X r n ≫ Sequential.indexMap X (orderedTargetIso r n).hom

/-- Every signed integer pointed power source keeps its full original degree/level casts and native action word. -/
theorem integerPointedPowerSource_formula (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X) :
    integerPointedPowerSource q X t n f =
      integerSphereCast q t n ≫ (nativeSphereSourceIso (integerTailPositiveIndex q + t + 1 + n)).hom ≫
        (mixedCoefficientIso n (integerTailPositiveIndex q + t + 1)).hom ≫
        rawPowerAction X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f ≫
        integerTargetCast q X t n := by
  have h := pointedPowerSource_formula X (integerTailLevel q + t)
    (integerTailPositiveIndex q + t + 1) n f
  have hCast := congrArg (fun z => integerSphereCast q t n ≫ z ≫ integerTargetCast q X t n) h
  simpa only [integerPointedPowerSource, pointedPowerSource, integerSphereCast, integerTargetCast,
    rawPowerAction, Category.assoc] using hCast

/-- Every original mixed readback has precisely the same original degree/level casts and raw evaluation. -/
theorem mixedPointedReadback_formula (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X) :
    mixedPointedReadback q X t n g =
      integerSphereCast q t n ≫ (nativeSphereSourceIso (integerTailPositiveIndex q + t + 1 + n)).hom ≫
        (mixedCoefficientIso n (integerTailPositiveIndex q + t + 1)).hom ≫
        rawMixedEvaluate X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n g ≫
        integerTargetCast q X t n := by
  have h := freeSourceCast_readback
    (show integerTailLevel q + (t + n) = integerTailLevel q + t + n by omega)
    (show integerTailPositiveIndex q + (t + n) + 1 = integerTailPositiveIndex q + t + 1 + n by omega)
    X ((mixedSourceIso n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1)).hom ≫ g)
  rw [mixedSourceIso_evaluate] at h
  simpa only [mixedPointedReadback, integerMixedSourceIso, Iso.trans_hom,
    integerSphereCast, integerTargetCast, Category.assoc] using h

/-- A proved full raw evaluated-map equality joins the original mixed and n-fold pointed sources. -/
theorem mixedPointedReadback_eq_power_of_rawEvaluate (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X)
    (h : rawMixedEvaluate X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n g =
      rawPowerAction X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f) :
    mixedPointedReadback q X t n g = integerPointedPowerSource q X t n f := by
  have hCast := congrArg (fun z => integerSphereCast q t n ≫
    (nativeSphereSourceIso (integerTailPositiveIndex q + t + 1 + n)).hom ≫
      (mixedCoefficientIso n (integerTailPositiveIndex q + t + 1)).hom ≫ z ≫
        integerTargetCast q X t n) h
  exact (mixedPointedReadback_formula q X t n g).trans
    (hCast.trans (integerPointedPowerSource_formula q X t n f).symm)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- A proved complete raw map equality identifies the actual all-signed-degree n-step integer action. -/
theorem mixedIntegerClass_eq_advance_of_rawEvaluate (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X)
    (h : rawMixedEvaluate X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n g =
      rawPowerAction X (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f) :
    mixedIntegerClass q t n X g = (integerStageAdvance q X t n).hom (integerNativeFreeClass q X t f) :=
  mixedIntegerClass_eq_advance_of_pointedSource q X t n f g
    (mixedPointedReadback_eq_power_of_rawEvaluate q X t n f g h)

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalCastReadback

section NativeGammaFinalTensorNullity


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SphereHom PointedCGWH.NativeLoopShiftGeometry
open PointedCGWH.SequentialSpectrum.OrderedLoop.HomotopyEvaluationGeometry
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

/-- Two complete original degree casts preserve the original positive-degree identity class. -/
theorem positiveClass_cast_composite_one (a b c : ℕ) (h : a + 1 = b) (j : b = c + 1)
    (D : PointedCGWH.{u, v}) :
    Equiv.cast (congrArg (fun d => PointedCGWH.piN d D) j)
      (Equiv.cast (congrArg (fun d => PointedCGWH.piN d D) h)
        (1 : PointedCGWH.piN (a + 1) D)) =
      (1 : PointedCGWH.piN (c + 1) D) := by
  cases h
  have hac : a = c := Nat.succ.inj j
  cases hac
  rfl

/-- The actual all-degree sphere-Hom shift preserves the original positive identity after its full degree cast. -/
theorem positivePowerShift_cast_one (n k c : ℕ) (h : k + 1 + n = c + 1)
    (D : PointedCGWH.{u, v}) :
    Equiv.cast (congrArg (fun d => PointedCGWH.piN d D) h)
      (((loopPowerPiShift n (k + 1)).app D).toEquiv
        (1 : PointedCGWH.piN (k + 1) ((loopPower n).obj D))) =
      (1 : PointedCGWH.piN (c + 1) D) := by
  let castFinal := Equiv.cast (congrArg (fun d => PointedCGWH.piN d D) h)
  let castShift := Equiv.cast (congrArg (fun d => PointedCGWH.piN d D)
    (show k + n + 1 = k + 1 + n by omega))
  have hType := loopPowerGroupShift_hom_eq_allDegree n k D
    (1 : PointedCGWH.piN (k + 1) ((loopPower n).obj D))
  have hActual := positiveOrderedShiftEquiv_apply n k D
    (1 : PointedCGWH.piN (k + 1) ((loopPower n).obj D))
  have hGroup := ((loopPowerGroupShiftNatIso n k).hom.app D).hom.map_one
  calc
    _ = castFinal (positiveOrderedShiftEquiv n k D 1) :=
      congrArg castFinal hType.symm
    _ = castFinal (castShift (((loopPowerGroupShiftNatIso n k).hom.app D).hom 1)) :=
      congrArg castFinal hActual
    _ = castFinal (castShift (1 : PointedCGWH.piN (k + n + 1) D)) :=
      congrArg (fun z => castFinal (castShift z)) hGroup
    _ = 1 := positiveClass_cast_composite_one (k + n) (k + 1 + n) c (by omega) h D

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- Every actual native null source stays null under the complete original pointed n-fold Hom source and signed degree
cast. -/
theorem integerNativeSuspendedSource_null (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (D : PointedCGWH.{u, v})
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (l : X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t)) ⟶
      (loopPower n).obj D)
    (hNull : (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeNullMap _ X)) :
    (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1) D).symm
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map
        (integerSphereCast q t n ≫
          eqToHom (Functor.congr_obj
            (originalSphereTensorPowerAdd (integerTailPositiveIndex q + t + 1) n) freePoint) ≫
          ((powerAdjunction n).homEquiv (sphere (integerTailPositiveIndex q + t + 1)) D).symm
            ((nativeSphereSourceIso (integerTailPositiveIndex q + t + 1)).hom ≫
              Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
                (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) X f ≫ l))) =
      (1 : PointedCGWH.piN (integerTailPositiveIndex q + (t + n) + 1) D) := by
  let k := integerTailPositiveIndex q + t
  let r := integerTailLevel q + t
  let d := k + 1
  let A := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)
  let p : sphere d ⟶ A := (nativeSphereSourceIso d).hom ≫
    Free.evaluate (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) X f
  let z := eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
    ((powerAdjunction n).homEquiv (sphere d) D).symm (p ≫ l)
  have hNative := (nativeSpherePiHomEquiv_null_iff
    (OrthogonalOperatorIndex.ofIndex r) k X f).mpr hNull
  have hScalar := (nativeSphereClass_evaluate (OrthogonalOperatorIndex.ofIndex r) d X f).symm.trans hNative
  have hMapOne : PointedCGWH.piNMap d l
      ((spherePiHomEquiv d A).symm ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map p)) = 1 :=
    (congrArg (PointedCGWH.piNMap d l) hScalar).trans
      ((PointedCGWH.piNPositiveMap_apply k l 1).symm.trans (PointedCGWH.piNPositiveMap k l).hom.map_one)
  have hPower := originalNativePowerSourceClass d n A D p l
  have hPowerOne := hPower.trans
    (congrArg (((loopPowerPiShift n d).app D).toEquiv) hMapOne)
  have hd : d + n = integerTailPositiveIndex q + (t + n) + 1 := by
    dsimp only [d, k]
    omega
  have hDegree := originalSphereClassDegreeCast hd D z
  have hFinal := hDegree.symm.trans
    ((congrArg (Equiv.cast (congrArg (fun j => PointedCGWH.piN j D) hd)) hPowerOne).trans
      (positivePowerShift_cast_one n k (integerTailPositiveIndex q + (t + n)) hd D))
  simpa only [integerSphereCast, z, p, d, r, k, Category.assoc] using hFinal

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalTensorNullity

section NativeGammaFinalKernelFunctorFaces


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.KernelFaces

section Ordinary
universe uV vV uC vC
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C]

/-- Families sending a map into the free sphere at `n` to a map from the free object at `n + r`
into the doubled free sphere. -/
def PrecomposeType (F : ℕ → V ⥤ C) (S : ℕ → V) : Type _ :=
  ∀ (n r : ℕ) (K : V), ((F r).obj K ⟶ (F n).obj (S n)) →
    ((F (n + r)).obj (S n ⊗ K) ⟶ (F (n + n)).obj (S (n + n)))

/-- The whole family is constructed on the exact original sphere-pair interface and original free functors. -/
def precomposeFamily (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (spheres : Independent.SpherePairType M F S) : PrecomposeType F S := by
  letI := M
  intro n r K f
  exact (pair n r (S n) K).inv ≫ ((F n).obj (S n) ◁ f) ≫ (spheres n).hom

/-- Precomposition followed by a sphere face agrees with the raw left face followed by the
original map. -/
def LeftFormula (F : ℕ → V ⥤ C) (S : ℕ → V) (pres : PrecomposeType F S)
    (sphereFaces : Independent.SphereFaceType F S)
    (faces : Independent.LeftFaceType (fun n K => (F n).obj K) S) : Prop :=
  ∀ (n r : ℕ) (K : V) (f : (F r).obj K ⟶ (F n).obj (S n)),
    pres n r K f ≫ sphereFaces n = faces n r K ≫ f

/-- Precomposition followed by a sphere face agrees with the unit lift of the original map
followed by `gamma n`. -/
def RightFormula (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S) (pres : PrecomposeType F S)
    (lifts : UnitLiftFamily.LiftType M (fun n K => (F n).obj K) S)
    (sphereFaces : Independent.SphereFaceType F S) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K : V) (f : (F r).obj K ⟶ (F n).obj (S n)),
    pres n r K f ≫ sphereFaces n = lifts n r K (f ≫ gamma n)

/-- The original left sphere face postcomposes every source map into its literal raw left face. -/
theorem precomposeFamily_left (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (spheres : Independent.SpherePairType M F S)
    (sphereFaces : Independent.SphereFaceType F S)
    (faces : Independent.LeftFaceType (fun n K => (F n).obj K) S)
    (hRaw : Independent.LeftFaceFormula M (fun n K => (F n).obj K) S gamma pair faces)
    (hSphere : Independent.LeftSphereFormula M F S gamma spheres sphereFaces) :
    LeftFormula F S (precomposeFamily M F S pair spheres) sphereFaces faces := by
  let := M
  intro n r K f
  simp only [precomposeFamily, Category.assoc]
  rw [hSphere n, hRaw n r K]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, tensorHom_id]
  rw [whisker_exchange_assoc, leftUnitor_naturality]

/-- The original right sphere face postcomposes every source map into the actual lift of its Gamma composite. -/
theorem precomposeFamily_right (M : MonoidalCategory C) (F : ℕ → V ⥤ C) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (spheres : Independent.SpherePairType M F S)
    (sphereFaces : Independent.SphereFaceType F S)
    (hSphere : Independent.RightSphereFormula M F S gamma spheres sphereFaces) :
    RightFormula M F S gamma (precomposeFamily M F S pair spheres)
      (UnitLiftFamily.liftFamily M (fun n K => (F n).obj K) S pair) sphereFaces := by
  let := M
  intro n r K f
  simp only [precomposeFamily, UnitLiftFamily.liftFamily, Category.assoc]
  rw [hSphere n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, id_tensorHom, whiskerLeft_comp]

end Ordinary

/-- The original native kernel precomposition family retains its exact native free-functor and sphere-pair types. -/
def nativeKernelPrecompose : PrecomposeType nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v} :=
  precomposeFamily CanonicalSourceSmash.monoidalCategory.{u, v} nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v} nativeSpherePairFamily.{u, v}

/-- Every original native map postcomposes the same literal native left sphere face. -/
theorem nativeKernelPrecompose_left : LeftFormula nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativeKernelPrecompose.{u, v}
    nativeLeftSphereFaces.{u, v} nativeLeftFaces.{u, v} :=
  precomposeFamily_left CanonicalSourceSmash.monoidalCategory.{u, v} nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v} nativeSpherePairFamily.{u, v}
    nativeLeftSphereFaces.{u, v} nativeLeftFaces.{u, v}
    nativeLeftFaces_original.{u, v} nativeLeftSphereFaces_original.{u, v}

/-- Every original native map postcomposes the same literal right sphere face into its original unit lift. -/
theorem nativeKernelPrecompose_right : RightFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v}
    nativeKernelPrecompose.{u, v} UnitLiftFamily.nativeUnitLift.{u, v} nativeRightSphereFaces.{u, v} :=
  precomposeFamily_right CanonicalSourceSmash.monoidalCategory.{u, v} nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} gamma.{u, v} nativePairFamily.{u, v} nativeSpherePairFamily.{u, v}
    nativeRightSphereFaces.{u, v} nativeRightSphereFaces_original.{u, v}

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.KernelFaces

end

end NativeGammaFinalKernelFunctorFaces

section NativeGammaFinalTensorReadback


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SphereHom
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

/-- The actual original pointed n-fold target map on an arbitrary tensor action. -/
def tensorTargetPower (n : ℕ) (A D : PointedCGWH.{u, v})
    (w : PointedCGWH.orthogonalSphere n ⊗ A ⟶ D) : (sphereTensorPower n).obj A ⟶ D :=
  (spherePowerValueIso n A).hom ≫ ((orderedCoefficientIso n).hom ▷ A) ≫ w

/-- The same actual target map through both original n-fold Hom functions. -/
def tensorTargetAdjunct (n : ℕ) (A D : PointedCGWH.{u, v})
    (w : PointedCGWH.orthogonalSphere n ⊗ A ⟶ D) : A ⟶ (loopPower n).obj D :=
  (powerAdjunction n).homEquiv A D (tensorTargetPower n A D w)

/-- The original native tensor coefficient source is exactly the original pointed n-fold Hom source. -/
theorem tensorScalarSource_formula (n d : ℕ) (A D : PointedCGWH.{u, v})
    (ev : PointedCGWH.orthogonalSphere d ⟶ A)
    (w : PointedCGWH.orthogonalSphere n ⊗ A ⟶ D) :
    (nativeSphereSourceIso (d + n)).hom ≫ (mixedCoefficientIso n d).hom ≫
      (PointedCGWH.orthogonalSphere n ◁ ev) ≫ w =
    eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
      ((powerAdjunction n).homEquiv (sphere d) D).symm
        (((nativeSphereSourceIso d).hom ≫ ev) ≫ tensorTargetAdjunct n A D w) := by
  let P := TensorPower.tensorPowObj PointedCGWH.sphereOne.{u, v} n
  let Sn := PointedCGWH.orthogonalSphere.{u, v} n
  let Sd := PointedCGWH.orthogonalSphere.{u, v} d
  let p : sphere d ⟶ A := (nativeSphereSourceIso d).hom ≫ ev
  let src := eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint)
  have hAdj : ((powerAdjunction n).homEquiv (sphere d) D).symm
      (p ≫ tensorTargetAdjunct n A D w) =
    (sphereTensorPower n).map p ≫ tensorTargetPower n A D w := by
    simp only [tensorTargetAdjunct]
    rw [(powerAdjunction n).homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hExchange : (P ◁ ev) ≫ ((orderedCoefficientIso n).hom ▷ A) =
      ((orderedCoefficientIso n).hom ▷ Sd) ≫ (Sn ◁ ev) :=
    whisker_exchange (orderedCoefficientIso n).hom ev
  have hSplit : (P ◁ p) ≫ ((orderedCoefficientIso n).hom ▷ A) =
      (P ◁ (nativeSphereSourceIso d).hom) ≫
        ((orderedCoefficientIso n).hom ▷ Sd) ≫ (Sn ◁ ev) := by
    simpa only [p, whiskerLeft_comp, Category.assoc] using
      congrArg (fun z => (P ◁ (nativeSphereSourceIso d).hom) ≫ z) hExchange
  have hValue := originalSpherePowerValueIso_naturality n p
  calc
    _ = (src ≫ (spherePowerValueIso n (sphere d)).hom ≫
        (P ◁ (nativeSphereSourceIso d).hom) ≫ ((orderedCoefficientIso n).hom ▷ Sd)) ≫ (Sn ◁ ev) ≫ w :=
      congrArg (fun z => z ≫ (Sn ◁ ev) ≫ w) (mixedCoefficientScalarSource.{u, v} n d)
    _ = src ≫ (spherePowerValueIso n (sphere d)).hom ≫
        ((P ◁ p) ≫ ((orderedCoefficientIso n).hom ▷ A)) ≫ w := by
      simpa only [Category.assoc] using congrArg
        (fun z => src ≫ (spherePowerValueIso n (sphere d)).hom ≫ z ≫ w) hSplit.symm
    _ = src ≫ ((spherePowerValueIso n (sphere d)).hom ≫ (P ◁ p)) ≫
        ((orderedCoefficientIso n).hom ▷ A) ≫ w := by simp only [Category.assoc]
    _ = src ≫ ((sphereTensorPower n).map p ≫ (spherePowerValueIso n A).hom) ≫
        ((orderedCoefficientIso n).hom ▷ A) ≫ w :=
      congrArg (fun z => src ≫ z ≫ ((orderedCoefficientIso n).hom ▷ A) ≫ w) hValue.symm
    _ = src ≫ ((sphereTensorPower n).map p ≫ tensorTargetPower n A D w) := by
      simp only [tensorTargetPower, Category.assoc]
    _ = _ := congrArg (fun z => src ≫ z) hAdj.symm

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- A complete original tensor readback of an actual native null source has the original identity class at its exact
later integer stage. -/
theorem mixedIntegerClass_one_of_tensorReadback (q : ℤ)
    (X Y : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (g : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ Y)
    (w : PointedCGWH.orthogonalSphere n ⊗
      X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t)) ⟶
        Y.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)))
    (hRaw : rawMixedEvaluate Y (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n g =
      (PointedCGWH.orthogonalSphere n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) X f) ≫ w)
    (hNull : (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (nativeNullMap _ X)) :
    mixedIntegerClass q t n Y g = 1 := by
  let r := integerTailLevel q + t
  let d := integerTailPositiveIndex q + t + 1
  let A := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex r)
  let D := Y.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
  let ev := Free.evaluate (OrthogonalOperatorIndex.ofIndex r) (PointedCGWH.orthogonalSphere d) X f
  let target := integerTargetCast q Y t n
  let l := tensorTargetAdjunct n A D (w ≫ target)
  let z := integerSphereCast q t n ≫
    eqToHom (Functor.congr_obj (originalSphereTensorPowerAdd d n) freePoint) ≫
      ((powerAdjunction n).homEquiv (sphere d) D).symm
        (((nativeSphereSourceIso d).hom ≫ ev) ≫ l)
  have hRead := mixedPointedReadback_formula q Y t n g
  have hRawCast := congrArg (fun u => integerSphereCast q t n ≫
    (nativeSphereSourceIso (d + n)).hom ≫ (mixedCoefficientIso n d).hom ≫ u ≫ target) hRaw
  have hTensor := congrArg (fun u => integerSphereCast q t n ≫ u)
    (tensorScalarSource_formula n d A D ev (w ≫ target))
  have hPoint : mixedPointedReadback q Y t n g = z := by
    calc
      _ = integerSphereCast q t n ≫ (nativeSphereSourceIso (d + n)).hom ≫
          (mixedCoefficientIso n d).hom ≫ rawMixedEvaluate Y r d n g ≫ target := hRead
      _ = integerSphereCast q t n ≫ (nativeSphereSourceIso (d + n)).hom ≫
          (mixedCoefficientIso n d).hom ≫ (PointedCGWH.orthogonalSphere n ◁ ev) ≫ w ≫ target := by
        simpa only [r, d, ev, Category.assoc] using hRawCast
      _ = integerSphereCast q t n ≫ ((nativeSphereSourceIso (d + n)).hom ≫
          (mixedCoefficientIso n d).hom ≫ (PointedCGWH.orthogonalSphere n ◁ ev) ≫ (w ≫ target)) := rfl
      _ = z := hTensor
  have hClass := mixedIntegerClass_eq_scalarReadback q Y t n g
  have hMap := (HomotopicalAlgebra.toHomotopyCategory PointedCGWH).congr_map hPoint
  have hClassPoint := congrArg
    (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1) D).symm hMap
  have hOne : (spherePiHomEquiv (integerTailPositiveIndex q + (t + n) + 1) D).symm
      ((HomotopicalAlgebra.toHomotopyCategory PointedCGWH).map z) = 1 := by
    simpa only [z, ev, r, d, Category.assoc] using
      integerNativeSuspendedSource_null q X t n D f l hNull
  exact hClass.trans (hClassPoint.trans hOne)

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalTensorReadback

section NativeGammaFinalKernelHoTransfer


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.KernelFaces

/-- Every complete original source map preserves a proved equality of mapped target arrows. -/
theorem map_composite_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} (g : A ⟶ B) (l r : B ⟶ T) (h : F.map l = F.map r) :
    F.map (g ≫ l) = F.map (g ≫ r) :=
  (F.map_comp g l).trans
    ((congrArg (fun a => F.map g ≫ a) h).trans (F.map_comp g r).symm)

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- A proved equality of the literal original sphere faces transfers through every actual native free source map. -/
theorem nativeKernelComparison_of_sphereFaceEquality (n r : ℕ) (K : PointedCGWH.{u, v})
    (f : (nativeFreeFunctor r).obj K ⟶ (nativeFreeFunctor n).obj (PointedCGWH.orthogonalSphere n))
    (h : (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map (nativeLeftSphereFaces n) =
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map (nativeRightSphereFaces n)) :
    (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map (nativeLeftFaces n r K ≫ f) =
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
        (UnitLiftFamily.nativeUnitLift n r K (f ≫ gamma n)) := by
  let H := HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}
  let pre := nativeKernelPrecompose n r K f
  have hLeft := H.congr_map (nativeKernelPrecompose_left n r K f)
  have hRight := H.congr_map (nativeKernelPrecompose_right n r K f)
  have hCompare := map_composite_eq H pre (nativeLeftSphereFaces n) (nativeRightSphereFaces n) h
  exact hLeft.symm.trans (hCompare.trans hRight)

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.KernelFaces

end

end NativeGammaFinalKernelHoTransfer

section NativeGammaFinalMixedHoCongruence


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- The complete original mixed integer source sends an actual native Ho equality to equality of its original stage
classes. -/
theorem mixedIntegerClass_eq_of_mapped_eq (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v}) (t n : ℕ)
    (g h : mixedFree n (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) ⟶ X)
    (e : (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map g =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map h) :
    mixedIntegerClass q t n X g = mixedIntegerClass q t n X h := by
  have ep := KernelFaces.map_composite_eq
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v})
    (integerMixedSourceIso q t n).hom g h e
  exact congrArg
    (nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + (t + n)))
      (integerTailPositiveIndex q + (t + n) + 1) X).symm ep

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin

end

end NativeGammaFinalMixedHoCongruence

section OriginalIntegerGammaAssembly


set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open Actual.OrthogonalIntegerHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeakness
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant

/-- An actual representative retains both functions of the original native sphere correspondence. -/
theorem integerNativeFreeClass_representative (q : ℤ) (X : Actual.OrthogonalCarrier.{u, v})
    (t : ℕ)
    (x : PointedCGWH.piN (integerTailPositiveIndex q + t + 1)
      (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))))
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X)
    (h : nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (integerTailPositiveIndex q + t + 1) X x =
        (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map f) :
    integerNativeFreeClass q X t f = x := by
  exact (congrArg
    (nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (integerTailPositiveIndex q + t + 1) X).symm h).symm.trans
        ((nativeSpherePiHomEquiv (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (integerTailPositiveIndex q + t + 1) X).symm_apply_apply x)

/-- The literal Gamma-left evaluator and original unit lift give every target integer class. -/
theorem integerGamma_surjective_of_raw_left (n : ℕ) (q : ℤ)
    (hLeft : ∀ (t : ℕ)
      (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶
          𝟙_ CanonicalSourceSmash.Carrier.{u, v}),
      SourceJoin.rawMixedEvaluate (𝟙_ CanonicalSourceSmash.Carrier.{u, v})
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (nativeLeftFaces n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) =
      SourceJoin.rawPowerAction (𝟙_ CanonicalSourceSmash.Carrier.{u, v})
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f) :
    Function.Surjective ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)).hom := by
  intro α
  obtain ⟨t, x, f, hf, hα⟩ := actualIntegerNativeSphereRepresentative
    q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) α
  refine ⟨unitLiftIntegerClass n q t f, ?_⟩
  have hRead := SourceJoin.mixedIntegerClass_eq_advance_of_rawEvaluate
    q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) t n f
    (nativeLeftFaces n (integerTailLevel q + t)
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) (hLeft t f)
  have hClass := integerNativeFreeClass_representative
    q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) t x f hf
  rw [hClass] at hRead
  exact (unitLiftIntegerClass_gamma n q t f).trans
    ((congrArg (integerPiLeg q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) (t + n)).hom hRead).trans
      ((integerStageAdvance_leg_apply q (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) t n x).trans hα))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The literal original sphere-face homotopy identifies the same actual mixed integer representatives. -/
theorem mixedIntegerClass_original_sphere_faces (n : ℕ) (q : ℤ) (t : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ sphereFree.{u, v} n)
    (hFaces :
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeLeftSphereFaces n) =
        (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeRightSphereFaces n)) :
    mixedIntegerClass q t n (sphereFree.{u, v} n)
        (nativeLeftFaces n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) =
      mixedIntegerClass q t n (sphereFree.{u, v} n)
        (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) (f ≫ gamma n)) := by
  have hCompare := KernelFaces.nativeKernelComparison_of_sphereFaceEquality
    n (integerTailLevel q + t)
    (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) f hFaces
  exact SourceJoin.mixedIntegerClass_eq_of_mapped_eq q (sphereFree.{u, v} n) t n
    (nativeLeftFaces n (integerTailLevel q + t)
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f)
    (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) (f ≫ gamma n)) hCompare

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A genuine native Gamma-null representative is killed by its exact original n-step integer action. -/
theorem integerGamma_null_stageAdvance_of_raw_faces (n : ℕ) (q : ℤ) (t : ℕ)
    (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
      (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ sphereFree.{u, v} n)
    (hNull : (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map (f ≫ gamma n) =
      (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
        (nativeNullMap _ (𝟙_ CanonicalSourceSmash.Carrier.{u, v})))
    (hFaces :
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeLeftSphereFaces n) =
        (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeRightSphereFaces n))
    (hLeft : SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (nativeLeftFaces n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) =
      SourceJoin.rawPowerAction (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f)
    (w : PointedCGWH.orthogonalSphere.{u, v} n ⊗
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}).toEnrichedFunctor.obj
            (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t)) ⟶
        (sphereFree.{u, v} n).toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)))
    (hLift : SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) (f ≫ gamma n)) =
      (PointedCGWH.orthogonalSphere n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1))
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) (f ≫ gamma n)) ≫ w) :
    (integerStageAdvance q (sphereFree.{u, v} n) t n).hom
      (integerNativeFreeClass q (sphereFree.{u, v} n) t f) = 1 := by
  let left := nativeLeftFaces n (integerTailLevel q + t)
    (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f
  let lift := UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
    (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) (f ≫ gamma n)
  have hLiftNull : mixedIntegerClass q t n (sphereFree.{u, v} n) lift = 1 :=
    SourceJoin.mixedIntegerClass_one_of_tensorReadback q
      (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) (sphereFree.{u, v} n) t n
      (f ≫ gamma n) lift w hLift hNull
  have hRead : mixedIntegerClass q t n (sphereFree.{u, v} n) left =
      (integerStageAdvance q (sphereFree.{u, v} n) t n).hom
        (integerNativeFreeClass q (sphereFree.{u, v} n) t f) :=
    SourceJoin.mixedIntegerClass_eq_advance_of_rawEvaluate q (sphereFree.{u, v} n)
      t n f left hLeft
  exact hRead.symm.trans ((mixedIntegerClass_original_sphere_faces n q t f hFaces).trans hLiftNull)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Original null representatives, literal sphere faces and actual tensor readbacks kill the full Gamma kernel. -/
theorem integerGamma_injective_of_raw_faces (n : ℕ) (q : ℤ)
    (hFaces :
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeLeftSphereFaces n) =
        (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeRightSphereFaces n))
    (hLeft : ∀ (t : ℕ)
      (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ sphereFree.{u, v} n),
      SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (nativeLeftFaces n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) =
      SourceJoin.rawPowerAction (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f)
    (w : ∀ t : ℕ,
      PointedCGWH.orthogonalSphere.{u, v} n ⊗
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}).toEnrichedFunctor.obj
            (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t)) ⟶
        (sphereFree.{u, v} n).toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)))
    (hLift : ∀ (t : ℕ)
      (g : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶
          𝟙_ CanonicalSourceSmash.Carrier.{u, v}),
      SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) g) =
      (PointedCGWH.orthogonalSphere n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1))
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) g) ≫ w t) :
    Function.Injective ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)).hom := by
  apply (injective_iff_map_eq_one ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)).hom).mpr
  intro α hα
  obtain ⟨t, x, f, hf, hx, hNull⟩ := integerKernelRepresentative q (gamma.{u, v} n) α hα
  have hAdvance := integerGamma_null_stageAdvance_of_raw_faces n q t f hNull hFaces
    (hLeft t f) (w t) (hLift t (f ≫ gamma n))
  have hClass := integerNativeFreeClass_representative q (sphereFree.{u, v} n) t x f hf
  rw [hClass] at hAdvance
  exact hx.symm.trans ((integerLeg_one_iff_advance q (sphereFree.{u, v} n) t x).mpr ⟨n, hAdvance⟩)

/-- The complete original raw left, unit-lift and sphere-face equations make Gamma an isomorphism in every original
integer degree. -/
theorem integerGamma_isIso_of_raw_faces (n : ℕ) (q : ℤ)
    (hFaces :
      (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeLeftSphereFaces n) =
        (HomotopicalAlgebra.toHomotopyCategory CanonicalSourceSmash.Carrier.{u, v}).map
          (nativeRightSphereFaces n))
    (hLeft : ∀ (X : Actual.OrthogonalCarrier.{u, v}) (t : ℕ)
      (f : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶ X),
      SourceJoin.rawMixedEvaluate X
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (nativeLeftFaces n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ≫ f) =
      SourceJoin.rawPowerAction X
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n f)
    (w : ∀ t : ℕ,
      PointedCGWH.orthogonalSphere.{u, v} n ⊗
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}).toEnrichedFunctor.obj
            (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t)) ⟶
        (sphereFree.{u, v} n).toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t + n)))
    (hLift : ∀ (t : ℕ)
      (g : Free.object (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
        (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) ⟶
          𝟙_ CanonicalSourceSmash.Carrier.{u, v}),
      SourceJoin.rawMixedEvaluate (sphereFree.{u, v} n)
        (integerTailLevel q + t) (integerTailPositiveIndex q + t + 1) n
        (UnitLiftFamily.nativeUnitLift n (integerTailLevel q + t)
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1)) g) =
      (PointedCGWH.orthogonalSphere n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex (integerTailLevel q + t))
          (PointedCGWH.orthogonalSphere (integerTailPositiveIndex q + t + 1))
          (𝟙_ CanonicalSourceSmash.Carrier.{u, v}) g) ≫ w t) :
    IsIso ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)) := by
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨integerGamma_injective_of_raw_faces n q hFaces (hLeft (sphereFree.{u, v} n)) w hLift,
      integerGamma_surjective_of_raw_left n q (hLeft (𝟙_ CanonicalSourceSmash.Carrier.{u, v}))⟩

omit B in
private theorem map_middle_isIso
    {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A L R Z : C} (eSource : A ≅ L) (f : L ⟶ R) (eTarget : Z ≅ R)
    (h : IsIso (F.map (eSource.hom ≫ f ≫ eTarget.inv))) : IsIso (F.map f) := by
  have hWord : F.map (eSource.hom ≫ f ≫ eTarget.inv) =
      F.map eSource.hom ≫ F.map f ≫ F.map eTarget.inv := by
    simp only [Functor.map_comp]
  let : IsIso (F.map eSource.hom ≫ F.map f ≫ F.map eTarget.inv) := hWord ▸ h
  let : IsIso (F.map f ≫ F.map eTarget.inv) :=
    IsIso.of_isIso_comp_left (F.map eSource.hom) (F.map f ≫ F.map eTarget.inv)
  exact IsIso.of_isIso_comp_right (F.map f) (F.map eTarget.inv)

omit B in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Both genuine original source and unit isomorphisms transfer Gamma to the unchanged stabilization arrow. -/
theorem integerStabilization_isIso_of_gamma (n : ℕ) (q : ℤ)
    [IsIso ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n))] :
    IsIso ((integerPiFunctor.{u, v} q).map (Actual.orthogonalStabilization.{u, v} 0 n)) := by
  exact map_middle_isIso (integerPiFunctor.{u, v} q) (gammaSourceIso.{u, v} n)
    (Actual.orthogonalStabilization.{u, v} 0 n) CanonicalSourceSmashUnit.unitIso.{u, v}
    (inferInstance : IsIso ((integerPiFunctor.{u, v} q).map (gamma.{u, v} n)))

end PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion

end

end OriginalIntegerGammaAssembly
