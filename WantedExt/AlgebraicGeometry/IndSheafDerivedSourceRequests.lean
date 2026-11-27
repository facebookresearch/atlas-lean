/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
public import MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels

/-!
# Source constructions for actual derived and enhanced Ind primitives

Every request concerns a fixed native sheaf/Ind operator, its actual
compact generators, or the original bounded Q. These structural
providers do not contain enhanced reconstruction or a holonomic
Riemann--Hilbert conclusion.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2,3.2--3.3 and4.4;
Kashiwara--Schapira, Ind-sheaves and Categories and Sheaves.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndSheafDerivedSourceRequests

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
open MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
open MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels
open MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
open MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels

local instance sourceAbelianPreadditive (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- Restricted ordinary Yoneda has the actual Ind-object property on a locally compact Hausdorff space. -/
theorem_wanted actual_ordinary_ind_source (k : Type) [Field k] (X : TopCat.{0})
    [LocallyCompactSpace X] [T2Space X] : OrdinaryIndSource k X

/-- The sheafification of the actual coefficient tensor preserves compact support on generators. -/
theorem_wanted actual_compact_tensor_source (k : Type) [Field k] (X : TopCat.{0})
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)] : CompactTensorSource k X

/-- The native compact-Yoneda tensor extension exists in the original Ind category. -/
theorem_wanted actual_ind_tensor_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X]
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]
    (S : CompactTensorSource k X) : IndTensorSource k X S

/-- The prescribed Ind tensor is additive and has its native signed cochain totals. -/
theorem_wanted actual_tensor_cochain_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X]
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]
    (S : CompactTensorSource k X) (D : IndTensorSource k X S) : TensorCochainSource k X S D

/-- The original Q carries every literal bounded Ind complex into bounded cohomology. -/
theorem_wanted actual_bounded_cohomology_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] : BoundedCohomologySource k X

/-- The original bounded Q localizes the actual bounded cochain quasi-isomorphisms. -/
theorem_wanted actual_bounded_localization_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X] (R : BoundedCohomologySource k X) : BoundedLocalizationSource k X R

/-- Native totals of two bounded Ind complexes are literally bounded. -/
theorem_wanted actual_bounded_tensor_source (k : Type) [Field k] (X : TopCat.{0})
    [CompactSheafSource k X]
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]
    (S : CompactTensorSource k X) (D : IndTensorSource k X S) [TensorCochainSource k X S D] :
    BoundedTensorSource k X S D

/-- The actual field-coefficient bounded tensor inverts its source bounded quasi-isomorphisms. -/
theorem_wanted actual_derived_tensor_source (k : Type) [Field k] (X : TopCat.{0})
    [LocallyCompactSpace X] [T2Space X] [CompactSheafSource k X]
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]
    (S : CompactTensorSource k X) (D : IndTensorSource k X S) [TensorCochainSource k X S D]
    (R : BoundedCohomologySource k X) (T : BoundedTensorSource k X S D) :
    DerivedTensorSource k X S D R T

/-- Actual ordinary inverse-image generators extend by compact-Yoneda Kan extension. -/
theorem_wanted actual_ind_inverse_image_source (k : Type) [Field k] (X Y : TopCat.{0})
    (f : X ⟶ Y) (S : OrdinaryIndSource k X) : IndInverseImageSource k f S

/-- The same actual inverse-image extension is additive. -/
theorem_wanted actual_ind_inverse_image_additive (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (S : OrdinaryIndSource k X) (D : IndInverseImageSource k f S) :
    (indInverseImage k f S D).Additive

/-- The actual Ind inverse image has the exact native derived localization. -/
theorem_wanted actual_exact_ind_inverse_image_source (k : Type) [Field k] (X Y : TopCat.{0})
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (S : OrdinaryIndSource k X) (D : IndInverseImageSource k f S)
    [(indInverseImage k f S D).Additive] : ExactIndInverseImageSource k f S D

/-- Total right derivation refers to the prescribed compact-generator proper image. -/
theorem_wanted actual_derived_ind_proper_image_source (k : Type) [Field k] (X Y : TopCat.{0})
    [CompactSheafSource k X] [CompactSheafSource k Y]
    (f : X ⟶ Y) (P : CompactPushforwardSource k f) (D : IndPushforwardSource k f P)
    [(indProperImage k f P D).Additive] : DerivedIndPushforwardSource k f P D

/-- A genuine closed-boundary direct image preserves boundedness in the source quotient. -/
theorem_wanted actual_closed_boundary_bounded (k : Type) [Field k] (B : BorderedSpace)
    [B.HasLocallyCompactAmbient]
    [CompactSheafSource k (boundarySpace B)] [CompactSheafSource k B.ambient]
    (P : CompactPushforwardSource k (boundaryInclusion B))
    (D : IndPushforwardSource k (boundaryInclusion B) P)
    [(indProperImage k (boundaryInclusion B) P D).Additive]
    (H : DerivedIndPushforwardSource k (boundaryInclusion B) P D)
    (F : BoundedIndDerived k (boundarySpace B)) :
    IsBounded k B.ambient ((derivedIndProperImage k (boundaryInclusion B) P D H).obj F.obj)

end WantedExt.AlgebraicGeometry.IndSheafDerivedSourceRequests
