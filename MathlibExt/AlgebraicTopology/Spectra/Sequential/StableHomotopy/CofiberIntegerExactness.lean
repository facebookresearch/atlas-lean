/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberRotationIntegerPi
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.CofiberIntegerKernelPreimage
import Mathlib.Algebra.Exact.Basic

/-!
# The actual integer cofiber sequence on original sequential spectra

The original source map, Q-counit inclusion and chosen-boundary connecting
map are retained throughout. The actual sphere/kernel preimage supplies
the first image law. Actual weak cofiber rotation and its full suspension
reversal transport the following two image laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerExactnessGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberConnectingIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberRotationIntegerPiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberKernelRepresentatives

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}

/-- At the original target, every integer inclusion kernel is the actual original source image. -/
theorem exact_at_target (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj F.right) :
    (inclusionInteger q F).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj F.left,
        ((integerStablePiFunctor q).map F.hom).hom y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := original_inclusion_kernel_preimage q F x hx
    rw [integerStablePiHoFunctor_map] at hy
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact source_inclusion_null q F y

/-- The original connecting kernel is the exact original chosen-boundary kernel before inversion. -/
theorem connectingPlusOne_eq_one_iff (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    (connectingPlusOne q F).hom x = 1 ↔
      ((integerStablePiFunctor (q + 1)).map (boundary F)).hom x = 1 := by
  rw [connectingPlusOne_apply]
  let e := (integerISuspensionPiNatIso q).app F.left
  constructor
  · intro h
    apply e.groupIsoToMulEquiv.symm.injective
    change e.inv.hom (((integerStablePiFunctor (q + 1)).map (boundary F)).hom x) =
      e.inv.hom 1
    exact h.trans (map_one e.inv.hom).symm
  · intro h
    exact (congrArg ((integerISuspensionPiNatIso q).inv.app F.left).hom h).trans (map_one _)

/-- Actual weak rotation turns each original connecting kernel into a target-inclusion image. -/
theorem connecting_kernel_preimage_plusOne (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F))
    (hx : (connectingPlusOne q F).hom x = 1) :
    ∃ y : (integerStablePiFunctor (q + 1)).obj F.right,
      (inclusionInteger (q + 1) F).hom y = x := by
  let J := targetInclusionArrow F
  let e := rotationSourceDesuspensionIso q F
  have hJ : ((inclusionIntegerNatTrans (q + 1)).app J).hom x = 1 := by
    apply e.groupIsoToMulEquiv.injective
    change e.hom.hom (((inclusionIntegerNatTrans (q + 1)).app J).hom x) = e.hom.hom 1
    rw [rotationSourceDesuspensionIso_hom, rotationSourceDesuspension_inclusion_apply]
    exact hx.trans (map_one _).symm
  have hJ' : (inclusionInteger (q + 1) J).hom x = 1 := hJ
  obtain ⟨b, hb⟩ := (exact_at_target (q + 1) J x).mp hJ'
  let eY := (qCounitIntegerNatIso (q + 1)).app F.right
  refine ⟨eY.hom.hom b, ?_⟩
  rw [inclusionInteger_formula, qCounitHoIso_integer_inverse]
  change ((integerStablePiFunctor (q + 1)).map (inclusion F)).hom
    (eY.inv.hom (eY.hom.hom b)) = x
  have hTriangle := ConcreteCategory.congr_hom eY.hom_inv_id b
  change eY.inv.hom (eY.hom.hom b) = b at hTriangle
  rw [hTriangle]
  exact hb

/-- The exact original cofiber position is an image/kernel equality in every successor degree. -/
theorem exact_at_cofiber_plusOne (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F)) :
    (connectingPlusOne q F).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor (q + 1)).obj F.right,
        (inclusionInteger (q + 1) F).hom y = x := by
  constructor
  · exact connecting_kernel_preimage_plusOne q F x
  · rintro ⟨y, rfl⟩
    have h := inclusion_connectingPlusOne_null q F y
    rw [inclusionIntegerNatTrans_app] at h
    exact h

/-- Every canonical connecting kernel has an original inclusion preimage
in the same integer degree. -/
theorem connecting_kernel_preimage (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj (cofiber.obj F))
    (hx : (connecting q F).hom x = 1) :
    ∃ y : (integerStablePiFunctor q).obj F.right,
      (inclusionInteger q F).hom y = x := by
  let eC := (predecessorDegreeNatIso q).app (cofiber.obj F)
  let eY := (predecessorDegreeNatIso q).app F.right
  have hPlus : (connectingPlusOne (q - 1) F).hom (eC.hom.hom x) = 1 := hx
  obtain ⟨y, hy⟩ := connecting_kernel_preimage_plusOne (q - 1) F (eC.hom.hom x) hPlus
  refine ⟨eY.inv.hom y, ?_⟩
  apply eC.groupIsoToMulEquiv.injective
  have hn := ConcreteCategory.congr_hom (congr_app
    (integerDegree_inclusion_naturality q ((q - 1) + 1) (by omega)) F) (eY.inv.hom y)
  change eC.hom.hom ((inclusionInteger q F).hom (eY.inv.hom y)) =
    (inclusionInteger ((q - 1) + 1) F).hom (eY.hom.hom (eY.inv.hom y)) at hn
  have ht := ConcreteCategory.congr_hom eY.inv_hom_id y
  change eY.hom.hom (eY.inv.hom y) = y at ht
  exact hn.trans ((congrArg (inclusionInteger ((q - 1) + 1) F).hom ht).trans hy)

/-- At the actual original cofiber, every integer connecting kernel is
exactly the inclusion image. -/
theorem exact_at_cofiber (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj (cofiber.obj F)) :
    (connecting q F).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj F.right,
        (inclusionInteger q F).hom y = x := by
  constructor
  · exact connecting_kernel_preimage q F x
  · rintro ⟨y, rfl⟩
    have h := inclusion_connecting_null q F y
    rw [inclusionIntegerNatTrans_app] at h
    exact h

private theorem nextConnecting_kernel_of_source_kernel (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F)
    (ha : ((integerStablePiFunctor q).map F.hom).hom
      ((rotationSourceDesuspension q F).hom a) = 1) :
    (connectingPlusOne q (targetInclusionArrow F)).hom a = 1 := by
  have h := nextConnectingPlusOne_correction_apply q F a
  exact h.trans ((congrArg ((rotationTargetCorrectionNatIso q).hom.app F.right).hom ha).trans
    (map_one _))

private theorem rotation_inclusion_preimage (q : ℤ) (F : Arrow Carrier.{u, v})
    (a : (nextQCofiberFunctor ⋙ integerStablePiFunctor (q + 1)).obj F)
    (ha : (nextConnectingPlusOne q F).hom a = 1) :
    ∃ y : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F),
      (connectingPlusOne q F).hom y = (rotationSourceDesuspension q F).hom a := by
  obtain ⟨y, hy⟩ := connecting_kernel_preimage_plusOne.{u, v} (B := B) q
    (targetInclusionFunctor.obj F) a ha
  change (integerStablePiFunctor (q + 1)).obj (cofiber.obj F) at y
  change (inclusionInteger (q + 1) (targetInclusionArrow F)).hom y = a at hy
  refine ⟨y, ?_⟩
  have hLeg := rotationSourceDesuspension_inclusion_apply q F y
  rw [inclusionIntegerNatTrans_app] at hLeg
  exact hLeg.symm.trans (congrArg (rotationSourceDesuspension q F).hom hy)

/-- Actual signed rotation lifts each original source kernel through the
original connecting map. -/
theorem source_kernel_preimage_plusOne (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj F.left)
    (hx : ((integerStablePiFunctor q).map F.hom).hom x = 1) :
    ∃ y : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F),
      (connectingPlusOne q F).hom y = x := by
  let e := rotationSourceDesuspensionIso q F
  let a := e.inv.hom x
  have he := ConcreteCategory.congr_hom e.inv_hom_id x
  change e.hom.hom a = x at he
  rw [rotationSourceDesuspensionIso_hom] at he
  have hJ : (nextConnectingPlusOne q F).hom a = 1 := by
    have hSource : ((integerStablePiFunctor q).map F.hom).hom
        ((rotationSourceDesuspension q F).hom a) = 1 :=
      (congrArg ((integerStablePiFunctor q).map F.hom).hom he).trans hx
    exact nextConnecting_kernel_of_source_kernel q F a hSource
  obtain ⟨y, hy⟩ := rotation_inclusion_preimage q F a hJ
  exact ⟨y, hy.trans he⟩

/-- Every successor-degree original source kernel is exactly the same original connecting image. -/
theorem exact_at_source_plusOne (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj F.left) :
    ((integerStablePiFunctor q).map F.hom).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor (q + 1)).obj (cofiber.obj F),
        (connectingPlusOne q F).hom y = x := by
  constructor
  · exact source_kernel_preimage_plusOne q F x
  · rintro ⟨y, rfl⟩
    exact connectingPlusOne_source_null q F y

/-- All original predecessor-degree source kernels lift through the canonical connecting map. -/
theorem source_kernel_preimage (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q - 1)).obj F.left)
    (hx : ((integerStablePiFunctor (q - 1)).map F.hom).hom x = 1) :
    ∃ y : (integerStablePiFunctor q).obj (cofiber.obj F),
      (connecting q F).hom y = x := by
  obtain ⟨y, hy⟩ := source_kernel_preimage_plusOne (q - 1) F x hx
  let e := (predecessorDegreeNatIso q).app (cofiber.obj F)
  refine ⟨e.inv.hom y, ?_⟩
  change (connectingPlusOne (q - 1) F).hom (e.hom.hom (e.inv.hom y)) = x
  have h := ConcreteCategory.congr_hom e.inv_hom_id y
  change e.hom.hom (e.inv.hom y) = y at h
  rw [h]
  exact hy

/-- At the original source, every integer kernel is the exact original
predecessor connecting image. -/
theorem exact_at_source (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q - 1)).obj F.left) :
    ((integerStablePiFunctor (q - 1)).map F.hom).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj (cofiber.obj F),
        (connecting q F).hom y = x := by
  constructor
  · exact source_kernel_preimage q F x
  · rintro ⟨y, rfl⟩
    exact connecting_source_null q F y

/-- The exact original source/inclusion pair has Mathlib's multiplicative exactness contract. -/
theorem source_inclusion_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact ((integerStablePiFunctor q).map F.hom).hom
      (inclusionInteger q F).hom :=
  exact_at_target q F

/-- The exact original inclusion/connecting pair retains the canonical predecessor degree. -/
theorem inclusion_connecting_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact (inclusionInteger q F).hom (connecting q F).hom :=
  exact_at_cofiber q F

/-- The exact original connecting/source pair uses the unchanged raw predecessor source map. -/
theorem connecting_source_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact (connecting q F).hom
      ((integerStablePiFunctor (q - 1)).map F.hom).hom :=
  exact_at_source q F

/-- The successor-degree row keeps the same original connecting and source functions. -/
theorem connectingPlusOne_source_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact (connectingPlusOne q F).hom
      ((integerStablePiFunctor q).map F.hom).hom :=
  exact_at_source_plusOne q F

section CallerChoices

private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index)
private abbrev ι := OriginalICone.inclusion (B := B) (I := Index)

variable (cc : ∀ F : Arrow Carrier.{u, v},
    PushoutCocone (ι.app (Q.obj F.left)) (Q.map F.hom))
  (hcc : ∀ F, IsColimit (cc F))
  (s : ∀ X : Carrier.{u, v}, PushoutCocone (ι.app X) (Diagrams.toZero X))
  (hs : ∀ X, IsColimit (s X))

/-- Every caller's actual target kernel is the same complete original source image. -/
theorem caller_exact_at_target (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor q).obj F.right) :
    ((callerInclusionIntegerNatTrans cc hcc q).app F).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj F.left,
        ((integerStablePiFunctor q).map F.hom).hom y = x := by
  let e := (callerCofiberIntegerNatIso cc hcc q).app F
  constructor
  · intro h
    have hOriginal : (inclusionInteger q F).hom x = 1 := by
      apply e.groupIsoToMulEquiv.injective
      change e.hom.hom ((inclusionInteger q F).hom x) = e.hom.hom 1
      exact h.trans (map_one e.hom.hom).symm
    exact (exact_at_target q F x).mp hOriginal
  · intro h
    have hOriginal := (exact_at_target q F x).mpr h
    change e.hom.hom ((inclusionInteger q F).hom x) = 1
    rw [hOriginal]
    exact map_one _

/-- The full caller connecting kernel is its actual chosen target-inclusion image. -/
theorem caller_exact_at_cofiber (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).obj F) :
    (callerConnecting cc hcc s hs q F).hom x = 1 ↔
      ∃ y : (integerStablePiFunctor q).obj F.right,
        ((callerInclusionIntegerNatTrans cc hcc q).app F).hom y = x := by
  let e := (callerCofiberIntegerNatIso cc hcc q).app F
  constructor
  · intro hx
    have hOriginal : (connecting q F).hom (e.inv.hom x) = 1 := by
      have h := callerConnecting_inverse_original_apply cc hcc s hs q F x
      exact h.symm.trans hx
    obtain ⟨y, hy⟩ := (exact_at_cofiber q F (e.inv.hom x)).mp hOriginal
    refine ⟨y, ?_⟩
    change e.hom.hom ((inclusionInteger q F).hom y) = x
    rw [hy]
    exact ConcreteCategory.congr_hom e.inv_hom_id x
  · rintro ⟨y, rfl⟩
    exact caller_inclusion_connecting_null cc hcc s hs q F y

/-- Every original source kernel is the complete connecting image for
both independent caller choices. -/
theorem caller_exact_at_source (q : ℤ) (F : Arrow Carrier.{u, v})
    (x : (integerStablePiFunctor (q - 1)).obj F.left) :
    ((integerStablePiFunctor (q - 1)).map F.hom).hom x = 1 ↔
      ∃ y : (callerCofiberFunctor cc hcc ⋙ integerStablePiFunctor q).obj F,
        (callerConnecting cc hcc s hs q F).hom y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (exact_at_source q F x).mp hx
    refine ⟨((callerCofiberIntegerNatIso cc hcc q).hom.app F).hom y, ?_⟩
    rw [callerConnecting_original_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    exact caller_connecting_source_null cc hcc s hs q F y

/-- Every actual caller cofiber has the same exact original source/inclusion pair. -/
theorem caller_source_inclusion_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact ((integerStablePiFunctor q).map F.hom).hom
      ((callerInclusionIntegerNatTrans cc hcc q).app F).hom :=
  caller_exact_at_target cc hcc q F

/-- Two independently chosen actual colimits retain the exact caller inclusion/connecting pair. -/
theorem caller_inclusion_connecting_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact ((callerInclusionIntegerNatTrans cc hcc q).app F).hom
      (callerConnecting cc hcc s hs q F).hom :=
  caller_exact_at_cofiber cc hcc s hs q F

/-- The caller connecting image is the kernel of the same original predecessor source map. -/
theorem caller_connecting_source_mulExact (q : ℤ) (F : Arrow Carrier.{u, v}) :
    Function.MulExact (callerConnecting cc hcc s hs q F).hom
      ((integerStablePiFunctor (q - 1)).map F.hom).hom :=
  caller_exact_at_source cc hcc s hs q F

end CallerChoices

end PointedCGWH.SequentialSpectrum.StableHomotopy.CofiberIntegerExactnessGeometry
