/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenScalarPointedRealization
import MathlibExt.AlgebraicTopology.ModelCategory.PointedFramingAction
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.CanonicalSphereHoGroup
import MathlibExt.Algebra.Group.EquivTransport

/-!
# The actual scalar circle Hom group

The original pointed realization unit and the earned pointed Quillen
adjunction identify the scalar circle Hom set with the native represented
one-sphere group. The original circle-realization and sphere-unit maps
are retained. Every target map acts by the complete original localized
postcomposition function. This supplies a scalar source for generic
framing Hom groups, without assuming a group on those Hom sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen CGWH.modelCategory

namespace HomotopicalAlgebra.ScalarCircleHomGroup

private abbrev P := Under (Δ[0] : SSet.{v})
private abbrev H := toHomotopyCategory P.{v}
private abbrev HC := toHomotopyCategory PointedCGWH.{u, v}
private abbrev F := SSet.pointedToCGWH.{u, v}
private abbrev G := CGWH.pointedToSSet.{u, v}
private abbrev circle := SSet.pointedCircle.{v}

local instance scalarQuillen : SSet.pointedToCGWHAdjunction.{u, v}.IsQuillenAdjunction :=
  QuillenScalarPointedRealization.isQuillen

local instance circleCofibrant : IsCofibrant circle := PointedFramingAction.pointedSSet_isCofibrant circle

local instance realizationFibrant (K : P) : IsFibrant ((F).obj K) :=
  PointedCGWH.modelCategory.allObjectsFibrant _

/-- The original pointed realization unit gives its actual isomorphism in the scalar ordinary Ho. -/
def unitHoIso (K : P) : (H).obj K ≅ (H).obj ((G).obj ((F).obj K)) := by
  let : IsIso ((H).map (SSet.pointedToCGWHAdjunction.{u, v}.unit.app K)) :=
    Localization.inverts (H) (weakEquivalences P) _ (QuillenScalarPointedRealization.unit_weak K)
  exact asIso ((H).map (SSet.pointedToCGWHAdjunction.{u, v}.unit.app K))

/-- The complete original unit square remains natural after scalar localization. -/
theorem unitHoIso_naturality {K L : P} (k : K ⟶ L) :
    (H).map k ≫ (unitHoIso.{u, v} L).hom =
      (unitHoIso.{u, v} K).hom ≫ (H).map ((G).map ((F).map k)) := by
  change (H).map k ≫ (H).map (SSet.pointedToCGWHAdjunction.{u, v}.unit.app L) =
    (H).map (SSet.pointedToCGWHAdjunction.{u, v}.unit.app K) ≫ (H).map ((G).map ((F).map k))
  rw [← (H).map_comp, ← (H).map_comp]
  exact (H).congr_map (SSet.pointedToCGWHAdjunction.{u, v}.unit.naturality k)

/-- Both original Ho adjunct functions retain the actual pointed unit and realization of the circle. -/
def realizationHomEquiv (K : P) : ((H).obj circle ⟶ (H).obj K) ≃
    ((HC).obj ((F).obj circle) ⟶ (HC).obj ((F).obj K)) :=
  (Iso.homCongr (Iso.refl _) (unitHoIso.{u, v} K)).trans
    (QuillenOrdinaryHoHom.homEquiv SSet.pointedToCGWHAdjunction circle ((F).obj K)).symm

/-- Every target arrow retains the full original realization map in the complete inverse Ho adjunct. -/
theorem realizationHomEquiv_naturality {K L : P} (k : K ⟶ L)
    (a : (H).obj circle ⟶ (H).obj K) :
    realizationHomEquiv.{u, v} L (a ≫ (H).map k) =
      realizationHomEquiv.{u, v} K a ≫ (HC).map ((F).map k) := by
  simp only [realizationHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp]
  rw [Category.assoc, unitHoIso_naturality, ← Category.assoc]
  exact QuillenOrdinaryHoHom.homEquiv_symm_naturality_right SSet.pointedToCGWHAdjunction circle
    (a ≫ (unitHoIso.{u, v} K).hom) ((F).map k)

/-- Both original sphere-source isomorphisms keep the full native circle realization. -/
def sphereSourceIso : PointedCGWH.SphereHom.canonicalSphere.{u, v} 1 ≅ (F).obj circle :=
  (λ_ PointedCGWH.sphereOne) ≪≫ PointedCGWH.pointedCircleRealizationIsoSphereOne.symm

/-- The actual sphere-source map follows the original pointed realization Hom functions. -/
def canonicalHomEquiv (K : P) : ((H).obj circle ⟶ (H).obj K) ≃
    ((HC).obj (PointedCGWH.SphereHom.canonicalSphere 1) ⟶ (HC).obj ((F).obj K)) :=
  (realizationHomEquiv.{u, v} K).trans
    (Iso.homCongr ((HC).mapIso sphereSourceIso).symm (Iso.refl _))

/-- The constant original source map commutes with the entire original target postcomposition. -/
theorem canonicalHomEquiv_naturality {K L : P} (k : K ⟶ L)
    (a : (H).obj circle ⟶ (H).obj K) :
    canonicalHomEquiv.{u, v} L (a ≫ (H).map k) =
      canonicalHomEquiv.{u, v} K a ≫ (HC).map ((F).map k) := by
  simp only [canonicalHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id]
  rw [realizationHomEquiv_naturality, Category.assoc]

/-- The original scalar circle Hom set is the actual native represented degree-one group. -/
def piEquiv (K : P) : ((H).obj circle ⟶ (H).obj K) ≃ PointedCGWH.piN 1 ((F).obj K) :=
  (canonicalHomEquiv.{u, v} K).trans
    (PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 ((F).obj K)).symm

/-- Every original pointed scalar map acts through the same actual positive homotopy-group map. -/
theorem piEquiv_naturality {K L : P} (k : K ⟶ L) (a : (H).obj circle ⟶ (H).obj K) :
    piEquiv.{u, v} L (a ≫ (H).map k) = PointedCGWH.piNMap 1 ((F).map k) (piEquiv.{u, v} K a) := by
  let eK : PointedCGWH.piN 1 ((F).obj K) ≃
      ((HC).obj (PointedCGWH.SphereHom.canonicalSphere 1) ⟶ (HC).obj ((F).obj K)) :=
    PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 ((F).obj K)
  let eL : PointedCGWH.piN 1 ((F).obj L) ≃
      ((HC).obj (PointedCGWH.SphereHom.canonicalSphere 1) ⟶ (HC).obj ((F).obj L)) :=
    PointedCGWH.SphereHom.canonicalSpherePiHomEquiv 1 ((F).obj L)
  have h : eL (PointedCGWH.piNMap 1 ((F).map k) (eK.symm (canonicalHomEquiv.{u, v} K a))) =
      eK (eK.symm (canonicalHomEquiv.{u, v} K a)) ≫ (HC).map ((F).map k) :=
    PointedCGWH.SphereHom.canonicalSpherePiHomEquiv_naturality 1 ((F).map k) _
  rw [eK.apply_symm_apply, ← canonicalHomEquiv_naturality] at h
  have ht := congrArg eL.symm h
  rw [eL.symm_apply_apply] at ht
  exact ht.symm

/-- The scalar circle Hom group is transported from the earned original native represented group. -/
@[instance_reducible]
def group (K : P) : Group ((H).obj circle ⟶ (H).obj K) :=
  letI := PointedCGWH.SphereHom.canonicalSphereHomGroup 0 ((F).obj K)
  EquivTransport.group (canonicalHomEquiv.{u, v} K)

/-- Every scalar target arrow gives a group homomorphism with the full original postcomposition function. -/
def postcompose {K L : P} (k : K ⟶ L) :
    letI := group.{u, v} K
    letI := group.{u, v} L
    ((H).obj circle ⟶ (H).obj K) →* ((H).obj circle ⟶ (H).obj L) := by
  letI := group.{u, v} K
  letI := group.{u, v} L
  letI := PointedCGWH.SphereHom.canonicalSphereHomGroup 0 ((F).obj K)
  letI := PointedCGWH.SphereHom.canonicalSphereHomGroup 0 ((F).obj L)
  exact EquivTransport.map (canonicalHomEquiv.{u, v} K) (canonicalHomEquiv.{u, v} L)
    (fun a => a ≫ (H).map k) (PointedCGWH.SphereHom.canonicalSphereHomPostcompose 0 ((F).map k))
    (fun a => by
      rw [PointedCGWH.SphereHom.canonicalSphereHomPostcompose_apply]
      exact canonicalHomEquiv_naturality k a)

/-- The complete group-map function is the unchanged localized scalar target postcomposition. -/
theorem postcompose_apply {K L : P} (k : K ⟶ L) (a : (H).obj circle ⟶ (H).obj K) :
    postcompose.{u, v} k a = a ≫ (H).map k := rfl

end HomotopicalAlgebra.ScalarCircleHomGroup
