/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricPointsCommonUniverse
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricClosureComparison
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The actual canonical residue closure over a field

The literal residue-field separable closure is given its base-field algebra
through the actual residue-field isomorphism. Closure uniqueness compares it
with the prescribed separable closure; its carrier is preserved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The exact residue-field separable closure used by the original canonical geometric point. -/
abbrev fieldCanonicalResidueClosure (k : Type u) [Field k] (x : Spec (.of k)) :=
  SeparableClosure ((Spec (.of k)).residueField x)

/-- Its actual base-field algebra comes through the inverse of the original residue-field
isomorphism. -/
@[instance_reducible]
def fieldCanonicalResidueClosureAlgebra (k : Type u) [Field k] (x : Spec (.of k)) :
    Algebra k (fieldCanonicalResidueClosure k x) :=
  ((algebraMap ((Spec (.of k)).residueField x) (fieldCanonicalResidueClosure k x)).comp
    (Spec.residueFieldIsoOfField x).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

attribute [local instance] fieldCanonicalResidueClosureAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- This actual canonical residue closure is a separable closure of the original field. -/
theorem fieldCanonicalResidueClosure_isSepClosure (k : Type u) [Field k] (x : Spec (.of k)) :
    IsSepClosure k (fieldCanonicalResidueClosure k x) := by
  let r := (Spec (.of k)).residueField x
  let S := fieldCanonicalResidueClosure k x
  let e := (Spec.residueFieldIsoOfField x).commRingCatIsoToRingEquiv
  have he : (algebraMap k S).comp e.toRingHom =
      (RingEquiv.refl S).toRingHom.comp (algebraMap r S) := by
    apply RingHom.ext
    intro a
    dsimp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      fieldCanonicalResidueClosureAlgebra, RingHom.algebraMap_toAlgebra]
    change algebraMap r S (e.symm (e a)) = algebraMap r S a
    rw [e.symm_apply_apply]
  have hsep : Algebra.IsSeparable k S :=
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl S) he
  exact ⟨inferInstance, hsep⟩

attribute [local instance] fieldCanonicalResidueClosure_isSepClosure

/-- The actual original residue closure is algebra-isomorphic to the prescribed separable
closure. -/
def fieldCanonicalResidueClosureEquiv (k : Type u) [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    fieldCanonicalResidueClosure k x ≃ₐ[k] Ω :=
  IsSepClosure.equiv k (fieldCanonicalResidueClosure k x) Ω

/-- The actual comparison sends the original base-field values to their prescribed Ω values. -/
theorem fieldCanonicalResidueClosureEquiv_algebraMap (k : Type u) [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (x : Spec (.of k)) (a : k) :
    fieldCanonicalResidueClosureEquiv k Ω x
      (algebraMap k (fieldCanonicalResidueClosure k x) a) = algebraMap k Ω a :=
  (fieldCanonicalResidueClosureEquiv k Ω x).commutes a

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual inverse residue-field isomorphism induces the original residue-field point over Spec
k. -/
theorem fieldSpecResidueIso_inv_map (k : Type u) [Field k] (x : Spec (.of k)) :
    Spec.map (Spec.residueFieldIsoOfField x).inv = (Spec (.of k)).fromSpecResidueField x := by
  rw [Spec.residueFieldIsoOfField_eq]
  rw [Iso.trans_inv, Spec.map_comp]
  change Spec.map (Spec.residueFieldIso (.of k) x).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField)) = _
  exact Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of k) x

set_option backward.isDefEq.respectTransparency.types false in
/-- The transported base-field algebra gives exactly the original canonical geometric morphism. -/
theorem fieldCanonicalResidueClosure_algebraMap_spec (k : Type u) [Field k] (x : Spec (.of k)) :
    Spec.algebraMap k (fieldCanonicalResidueClosure k x) =
      smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x := by
  change Spec.map (CommRingCat.ofHom (algebraMap k (fieldCanonicalResidueClosure k x))) =
    Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec (.of k)).residueField x) (fieldCanonicalResidueClosure k x))) ≫
      (Spec (.of k)).fromSpecResidueField x
  rw [← fieldSpecResidueIso_inv_map k x, ← Spec.map_comp]
  congr 1

attribute [local instance] IsSepClosure.sep_closed

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical common point is isomorphic to the prescribed Ω point through the genuine
closure isomorphism. -/
def fieldCanonicalCommonPointIso (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x) ≅
      smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) :=
  (eqToIso (congrArg (fun f => smallEtaleGeometricPointCommon.{u, w} f)
    (fieldCanonicalResidueClosure_algebraMap_spec k x).symm)) ≪≫
      (fieldClosureCommonPointIso.{u, w} k (fieldCanonicalResidueClosure k x) Ω
        (fieldCanonicalResidueClosureEquiv k Ω x).toAlgHom).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine point isomorphism gives an actual natural isomorphism from prescribed Ω stalks to
the original canonical stalks. -/
def fieldCanonicalCommonStalkIso (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).sheafFiber
        (A := AddCommGrpCat.{max u w}) where
  hom := (fieldCanonicalCommonPointIso.{u, w} k Ω x).hom.sheafFiber
  inv := (fieldCanonicalCommonPointIso.{u, w} k Ω x).inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldCanonicalCommonPointIso.{u, w} k Ω x).inv_hom_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp,
      (fieldCanonicalCommonPointIso.{u, w} k Ω x).hom_inv_id]
    exact GrothendieckTopology.Point.Hom.sheafFiber_id _

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original prescribed-point germ becomes the same original germ at its actual
canonical-point image. -/
theorem fieldCanonicalCommonStalkIso_germ (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k))
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U z Q.obj ≫
        (fieldCanonicalCommonStalkIso.{u, w} k Ω x).hom.app Q =
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).toPresheafFiber U
          ((fieldCanonicalCommonPointIso.{u, w} k Ω x).hom.hom.app U z) Q.obj := by
  let p := smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)
  let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let h := (fieldCanonicalCommonPointIso.{u, w} k Ω x).hom
  change q.toPresheafFiber U z Q.obj ≫ h.presheafFiber.app Q.obj =
    p.toPresheafFiber U (h.hom.app U z) Q.obj
  exact q.toPresheafFiber_presheafFiberDesc (A := AddCommGrpCat.{max u w}) (P := Q.obj) _ _ U z

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual common stalk isomorphism transports the canonical skyscraper adjunction to prescribed
Ω stalks. -/
def fieldCanonicalSkyscraperAdjunction (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).sheafFiber
        (A := AddCommGrpCat.{max u w}) ⊣
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) :=
  ((smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w})).ofNatIsoLeft
        (fieldCanonicalCommonStalkIso.{u, w} k Ω x).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical and prescribed point skyscrapers are identified by the actual stalk adjunctions. -/
def fieldCanonicalSkyscraperIso (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) ≅
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
        (A := AddCommGrpCat.{max u w}) :=
  Adjunction.rightAdjointUniq (fieldCanonicalSkyscraperAdjunction.{u, w} k Ω x)
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
      (A := AddCommGrpCat.{max u w}))

set_option backward.isDefEq.respectTransparency.types false in
/-- The original canonical point unit becomes the prescribed point unit through the actual
skyscraper and stalk comparisons. -/
theorem fieldCanonicalSkyscraperIso_unit (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k))
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let s := fieldCanonicalSkyscraperIso.{u, w} k Ω x
    let adj := fieldCanonicalSkyscraperAdjunction.{u, w} k Ω x
    let adj' := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    adj.unit.app Q ≫ s.hom.app (q.sheafFiber.obj Q) = adj'.unit.app Q := by
  intro q s adj adj'
  exact Adjunction.unit_rightAdjointUniq_hom_app adj adj' Q

set_option backward.isDefEq.respectTransparency.types false in
/-- The same skyscraper comparison intertwines the original canonical and prescribed evaluation
counits. -/
theorem fieldCanonicalSkyscraperIso_counit (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k))
    (M : AddCommGrpCat.{max u w}) :
    let q := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let s := fieldCanonicalSkyscraperIso.{u, w} k Ω x
    let adj := fieldCanonicalSkyscraperAdjunction.{u, w} k Ω x
    let adj' := q.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w})
    q.sheafFiber.map (s.hom.app M) ≫ adj'.counit.app M = adj.counit.app M := by
  intro q s adj adj'
  exact Adjunction.rightAdjointUniq_hom_app_counit adj adj' M

end AlgebraicGeometry.Scheme.DerivedSections
