/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerKernel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerRotation
import Mathlib.Algebra.Exact.Basic

/-!
# Integer stable homotopy exactness of cofibers

For a pointed CGWH enriched functor category and a sequential-index functor, the
integer stable homotopy groups of an arrow fit into a cofiber long exact sequence.
The maps use the chosen projective cofibrant replacement, cofiber inclusion, and
suspension boundary, with the connecting map lowering degree by one.
Exactness is expressed both by `Function.MulExact` and by equalities of kernels and ranges.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerMaps
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I}

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev C := (Carrier.{u, v} (I := I))
private abbrev Index := I
private abbrev H := toHomotopyCategory (Carrier.{u, v} (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev cone := OriginalICone.cone (B := B) (I := I)
private abbrev ι := OriginalICone.inclusion (B := B) (I := I)
private abbrev c := OriginalISuspension.cocone (B := B) (I := I)
private abbrev hc := OriginalISuspension.coconeIsColimit (B := B) (I := I)
private abbrev CQ := CofiberNullity.cofiberQ (B := B) (I := I)

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerExactness

open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerKernel
open HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerRotation

/-- At the original target, every integer inclusion kernel is the actual original source image. -/
theorem exact_at_target (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj F.right) :
    (inclusionInteger (j := j) q F).hom x = 1 ↔
      ∃ y : (integerPiFunctor j q).obj F.left,
        ((integerPiFunctor j q).map F.hom).hom y = x := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := original_inclusion_kernel_preimage (j := j) q F x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact source_inclusion_null (j := j) q F y

/-- The original connecting kernel is the exact original chosen-boundary kernel before inversion. -/
theorem connectingPlusOne_eq_one_iff (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F)) :
    (connectingPlusOne (j := j) q F).hom x = 1 ↔
      ((integerPiFunctor j (q + 1)).map (boundary F)).hom x = 1 := by
  rw [connectingPlusOne_apply (j := j)]
  let e := (integerISuspensionPiNatIso (j := j) q).app F.left
  constructor
  · intro h
    apply e.groupIsoToMulEquiv.symm.injective
    change e.inv.hom (((integerPiFunctor j (q + 1)).map (boundary F)).hom x) =
      e.inv.hom 1
    exact h.trans (map_one e.inv.hom).symm
  · intro h
    exact (congrArg ((integerISuspensionPiNatIso (j := j) q).inv.app F.left).hom h).trans (map_one
      _)

/-- Actual weak rotation turns each original connecting kernel into a target-inclusion image. -/
theorem connecting_kernel_preimage_plusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F))
    (hx : (connectingPlusOne (j := j) q F).hom x = 1) :
    ∃ y : (integerPiFunctor j (q + 1)).obj F.right,
      (inclusionInteger (j := j) (q + 1) F).hom y = x := by
  let J := targetInclusionArrow F
  let e := rotationSourceDesuspensionIso (j := j) q F
  have hJ : ((inclusionIntegerNatTrans (j := j) (q + 1)).app J).hom x = 1 := by
    apply e.groupIsoToMulEquiv.injective
    change e.hom.hom (((inclusionIntegerNatTrans (j := j) (q + 1)).app J).hom x) = e.hom.hom 1
    rw [rotationSourceDesuspensionIso_hom (j := j), rotationSourceDesuspension_inclusion_apply (j
      := j)]
    exact hx.trans (map_one _).symm
  have hJ' : (inclusionInteger (j := j) (q + 1) J).hom x = 1 := hJ
  obtain ⟨b, hb⟩ := (exact_at_target (j := j) (q + 1) J x).mp hJ'
  let eY := (qCounitIntegerNatIso (j := j) (q + 1)).app F.right
  refine ⟨eY.hom.hom b, ?_⟩
  rw [inclusionInteger_formula (j := j), qCounitHoIso_integer_inverse (j := j)]
  change ((integerPiFunctor j (q + 1)).map (inclusion F)).hom
    (eY.inv.hom (eY.hom.hom b)) = x
  have hTriangle := ConcreteCategory.congr_hom eY.hom_inv_id b
  change eY.inv.hom (eY.hom.hom b) = b at hTriangle
  rw [hTriangle]
  exact hb

/-- The exact original cofiber position is an image/kernel equality in every successor degree. -/
theorem exact_at_cofiber_plusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F)) :
    (connectingPlusOne (j := j) q F).hom x = 1 ↔
      ∃ y : (integerPiFunctor j (q + 1)).obj F.right,
        (inclusionInteger (j := j) (q + 1) F).hom y = x := by
  constructor
  · exact connecting_kernel_preimage_plusOne (j := j) q F x
  · rintro ⟨y, rfl⟩
    have h := inclusion_connectingPlusOne_null (j := j) q F y
    rw [inclusionIntegerNatTrans_app (j := j)] at h
    exact h

omit B in
private theorem transportGroupPreimage {A A' C C' : GrpCat.{v}}
    (eA : A ≅ A') (eC : C ≅ C') (f : A ⟶ C) (g : A' ⟶ C')
    (h : f ≫ eC.hom = eA.hom ≫ g) (x : C) (y : A')
    (hy : g.hom y = eC.hom.hom x) : f.hom (eA.inv.hom y) = x := by
  apply eC.groupIsoToMulEquiv.injective
  have hn := ConcreteCategory.congr_hom h (eA.inv.hom y)
  have he := ConcreteCategory.congr_hom eA.inv_hom_id y
  exact hn.trans ((congrArg g.hom he).trans hy)

/-- Every canonical connecting kernel has an original inclusion preimage
in the same integer degree. -/
theorem connecting_kernel_preimage (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F))
    (hx : (connecting (j := j) q F).hom x = 1) :
    ∃ y : (integerPiFunctor j q).obj F.right,
      (inclusionInteger (j := j) q F).hom y = x := by
  let eC := (predecessorDegreeNatIso (j := j) q).app ((cofiber (I := I)).obj F)
  let eY := (predecessorDegreeNatIso (j := j) q).app F.right
  have hPlus : (connectingPlusOne (j := j) (q - 1) F).hom (eC.hom.hom x) = 1 := hx
  obtain ⟨y, hy⟩ := connecting_kernel_preimage_plusOne (j := j) (q - 1) F (eC.hom.hom x) hPlus
  have h := congr_app (integerDegree_inclusion_naturality (j := j)
    q ((q - 1) + 1) (by omega)) F
  refine ⟨eY.inv.hom y, ?_⟩
  exact transportGroupPreimage eY eC (inclusionInteger (j := j) q F)
    (inclusionInteger (j := j) ((q - 1) + 1) F) h x y hy

/-- At the actual original cofiber, every integer connecting kernel is
exactly the inclusion image. -/
theorem exact_at_cofiber (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F)) :
    (connecting (j := j) q F).hom x = 1 ↔
      ∃ y : (integerPiFunctor j q).obj F.right,
        (inclusionInteger (j := j) q F).hom y = x := by
  constructor
  · exact connecting_kernel_preimage (j := j) q F x
  · rintro ⟨y, rfl⟩
    have h := inclusion_connecting_null (j := j) q F y
    rw [inclusionIntegerNatTrans_app (j := j)] at h
    exact h

private theorem nextConnecting_kernel_of_source_kernel (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F)
    (ha : ((integerPiFunctor j q).map F.hom).hom
      ((rotationSourceDesuspension (j := j) q F).hom a) = 1) :
    (connectingPlusOne (j := j) q (targetInclusionArrow F)).hom a = 1 := by
  have h := nextConnectingPlusOne_correction_apply (j := j) q F a
  exact h.trans ((congrArg ((rotationTargetCorrectionNatIso (j := j) q).hom.app F.right).hom
    ha).trans
    (map_one _))

private theorem rotation_inclusion_preimage (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (a : (nextQCofiberFunctor ⋙ integerPiFunctor j (q + 1)).obj F)
    (ha : (nextConnectingPlusOne (j := j) q F).hom a = 1) :
    ∃ y : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F),
      (connectingPlusOne (j := j) q F).hom y = (rotationSourceDesuspension (j := j) q F).hom a := by
  obtain ⟨y, hy⟩ := connecting_kernel_preimage_plusOne.{u, v} (j := j) (B := B) q
    (targetInclusionFunctor.obj F) a ha
  change (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F) at y
  change (inclusionInteger (j := j) (q + 1) (targetInclusionArrow F)).hom y = a at hy
  refine ⟨y, ?_⟩
  have hLeg := rotationSourceDesuspension_inclusion_apply (j := j) q F y
  rw [inclusionIntegerNatTrans_app (j := j)] at hLeg
  exact hLeg.symm.trans (congrArg (rotationSourceDesuspension (j := j) q F).hom hy)

/-- Actual signed rotation lifts each original source kernel through the
original connecting (j := j) map. -/
theorem source_kernel_preimage_plusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj F.left)
    (hx : ((integerPiFunctor j q).map F.hom).hom x = 1) :
    ∃ y : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F),
      (connectingPlusOne (j := j) q F).hom y = x := by
  let e := rotationSourceDesuspensionIso (j := j) q F
  let a := e.inv.hom x
  have he := ConcreteCategory.congr_hom e.inv_hom_id x
  change e.hom.hom a = x at he
  rw [rotationSourceDesuspensionIso_hom (j := j)] at he
  have hJ : (nextConnectingPlusOne (j := j) q F).hom a = 1 := by
    have hSource : ((integerPiFunctor j q).map F.hom).hom
        ((rotationSourceDesuspension (j := j) q F).hom a) = 1 :=
      (congrArg ((integerPiFunctor j q).map F.hom).hom he).trans hx
    exact nextConnecting_kernel_of_source_kernel (j := j) q F a hSource
  obtain ⟨y, hy⟩ := rotation_inclusion_preimage (j := j) q F a hJ
  exact ⟨y, hy.trans he⟩

/-- Every successor-degree original source kernel is exactly the same original connecting image. -/
theorem exact_at_source_plusOne (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j q).obj F.left) :
    ((integerPiFunctor j q).map F.hom).hom x = 1 ↔
      ∃ y : (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F),
        (connectingPlusOne (j := j) q F).hom y = x := by
  constructor
  · exact source_kernel_preimage_plusOne (j := j) q F x
  · rintro ⟨y, rfl⟩
    exact connectingPlusOne_source_null (j := j) q F y

/-- All original predecessor-degree source kernels lift through the canonical connecting map. -/
theorem source_kernel_preimage (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j (q - 1)).obj F.left)
    (hx : ((integerPiFunctor j (q - 1)).map F.hom).hom x = 1) :
    ∃ y : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F),
      (connecting (j := j) q F).hom y = x := by
  obtain ⟨y, hy⟩ := source_kernel_preimage_plusOne (j := j) (q - 1) F x hx
  let e := (predecessorDegreeNatIso (j := j) q).app ((cofiber (I := I)).obj F)
  refine ⟨e.inv.hom y, ?_⟩
  change (connectingPlusOne (j := j) (q - 1) F).hom (e.hom.hom (e.inv.hom y)) = x
  have h := ConcreteCategory.congr_hom e.inv_hom_id y
  change e.hom.hom (e.inv.hom y) = y at h
  rw [h]
  exact hy

/-- At the original source, every integer kernel is the exact original
predecessor connecting (j := j) image. -/
theorem exact_at_source (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I)))
    (x : (integerPiFunctor j (q - 1)).obj F.left) :
    ((integerPiFunctor j (q - 1)).map F.hom).hom x = 1 ↔
      ∃ y : (integerPiFunctor j q).obj ((cofiber (I := I)).obj F),
        (connecting (j := j) q F).hom y = x := by
  constructor
  · exact source_kernel_preimage (j := j) q F x
  · rintro ⟨y, rfl⟩
    exact connecting_source_null (j := j) q F y

/-- The exact original source/inclusion pair has Mathlib's multiplicative exactness contract. -/
theorem source_inclusion_mulExact (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    Function.MulExact ((integerPiFunctor j q).map F.hom).hom
      (inclusionInteger (j := j) q F).hom :=
  exact_at_target (j := j) q F

/-- The exact original inclusion/connecting pair retains the canonical predecessor degree. -/
theorem inclusion_connecting_mulExact (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    Function.MulExact (inclusionInteger (j := j) q F).hom (connecting (j := j) q F).hom :=
  exact_at_cofiber (j := j) q F

/-- The exact original connecting/source pair uses the unchanged raw predecessor source map. -/
theorem connecting_source_mulExact (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    Function.MulExact (connecting (j := j) q F).hom
      ((integerPiFunctor j (q - 1)).map F.hom).hom :=
  exact_at_source (j := j) q F

/-- The successor-degree row keeps the same original connecting and source functions. -/
theorem connectingPlusOne_source_mulExact (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    Function.MulExact (connectingPlusOne (j := j) q F).hom
      ((integerPiFunctor j q).map F.hom).hom :=
  exact_at_source_plusOne (j := j) q F

/-- For every original arrow and integer, the same three native homomorphism pairs are exact. -/
theorem integer_cofiber_long_exact (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    Function.MulExact ((integerPiFunctor j q).map F.hom).hom
        (inclusionInteger (j := j) q F).hom ∧
      Function.MulExact (inclusionInteger (j := j) q F).hom (connecting (j := j) q F).hom ∧
        Function.MulExact (connecting (j := j) q F).hom
          ((integerPiFunctor j (q - 1)).map F.hom).hom :=
  ⟨source_inclusion_mulExact (j := j) q F, inclusion_connecting_mulExact (j := j) q F,
    connecting_source_mulExact (j := j) q F⟩

/-- The original three exactness statements are literal kernel equals image subgroup equalities. -/
theorem integer_cofiber_kernel_equalities (q : ℤ) (F : Arrow (Carrier.{u, v} (I := I))) :
    (inclusionInteger (j := j) q F).hom.ker = ((integerPiFunctor j q).map F.hom).hom.range ∧
      (connecting (j := j) q F).hom.ker = (inclusionInteger (j := j) q F).hom.range ∧
        ((integerPiFunctor j (q - 1)).map F.hom).hom.ker = (connecting (j := j) q F).hom.range :=
  ⟨(source_inclusion_mulExact (j := j) q F).monoidHom_ker_eq,
    (inclusion_connecting_mulExact (j := j) q F).monoidHom_ker_eq,
    (connecting_source_mulExact (j := j) q F).monoidHom_ker_eq⟩


end HomotopicalAlgebra.EnrichedProjective.Native.NativeStableCofiberIntegerExactness
