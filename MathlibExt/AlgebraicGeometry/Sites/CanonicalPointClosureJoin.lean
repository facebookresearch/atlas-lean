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
# Residue separable closures and prescribed field points

For a point of `Spec k`, its residue field identifies with `k`. Transporting the algebra
structure makes the separable closure of that residue field a separable closure of `k`,
comparable with any prescribed separable closure.

When both fields lie in the scheme universe, this gives an isomorphism from the canonical
residue-field geometric point to the prescribed point. Its stalk comparison preserves germs,
and the associated skyscraper comparison respects adjunction units and counits.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Separable closure of a field spectrum residue field.

At a point of `Spec k`, take the separable closure of its residue field. -/
abbrev fieldCanonicalResidueClosure (k : Type u) [Field k] (x : Spec (.of k)) :=
  SeparableClosure ((Spec (.of k)).residueField x)

/-- Base field action on the residue separable closure.

Use the inverse residue-field isomorphism and the closure inclusion to give the canonical
residue closure a `k`-algebra structure. -/
@[instance_reducible]
def fieldCanonicalResidueClosureAlgebra (k : Type u) [Field k] (x : Spec (.of k)) :
    Algebra k (fieldCanonicalResidueClosure k x) :=
  ((algebraMap ((Spec (.of k)).residueField x) (fieldCanonicalResidueClosure k x)).comp
    (Spec.residueFieldIsoOfField x).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

attribute [local instance] fieldCanonicalResidueClosureAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical residue closure is a separable closure of the base field.

With the transported `k`-algebra structure, the residue-field separable closure satisfies
`IsSepClosure k`. -/
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

/-- Canonical residue closure compares with any prescribed separable closure.

The canonical residue closure is `k`-algebra equivalent to a prescribed separable closure `Ω`,
allowing an independent universe for `Ω`. -/
def fieldCanonicalResidueClosureEquiv (k : Type u) [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    fieldCanonicalResidueClosure k x ≃ₐ[k] Ω :=
  IsSepClosure.equiv k (fieldCanonicalResidueClosure k x) Ω

/-- Residue closure equivalence preserves base field elements.

The equivalence sends the image of any `a : k` under the canonical closure algebra map to its
image in `Ω`. -/
theorem fieldCanonicalResidueClosureEquiv_algebraMap (k : Type u) [Field k]
    (Ω : Type v) [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (x : Spec (.of k)) (a : k) :
    fieldCanonicalResidueClosureEquiv k Ω x
      (algebraMap k (fieldCanonicalResidueClosure k x) a) = algebraMap k Ω a :=
  (fieldCanonicalResidueClosureEquiv k Ω x).commutes a

set_option backward.isDefEq.respectTransparency.types false in
/-- Inverse residue isomorphism gives the residue point morphism.

Taking spectra of the inverse field-spectrum residue isomorphism gives the canonical map from
the residue-field spectrum to `Spec k`. -/
theorem fieldSpecResidueIso_inv_map (k : Type u) [Field k] (x : Spec (.of k)) :
    Spec.map (Spec.residueFieldIsoOfField x).inv = (Spec (.of k)).fromSpecResidueField x := by
  rw [Spec.residueFieldIsoOfField_eq]
  rw [Iso.trans_inv, Spec.map_comp]
  change Spec.map (Spec.residueFieldIso (.of k) x).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField)) = _
  exact Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of k) x

set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical closure algebra map gives the canonical geometric morphism.

The spectrum map of the base-field inclusion in the residue closure is the canonical geometric
morphism at the point. -/
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
/-- Canonical and prescribed field geometric points are isomorphic.

For a prescribed separable closure in the scheme universe, the canonical common geometric
point is isomorphic to the prescribed common point. -/
def fieldCanonicalCommonPointIso (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (x : Spec (.of k)) :
    smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism (Spec (.of k)) x) ≅
      smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω) :=
  (eqToIso (congrArg (fun f => smallEtaleGeometricPointCommon.{u, w} f)
    (fieldCanonicalResidueClosure_algebraMap_spec k x).symm)) ≪≫
      (fieldClosureCommonPointIso.{u, w} k (fieldCanonicalResidueClosure k x) Ω
        (fieldCanonicalResidueClosureEquiv k Ω x).toAlgHom).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Prescribed field stalk compares with the canonical residue stalk.

The point isomorphism induces a natural isomorphism from the prescribed stalk functor to the
canonical residue-point stalk functor. -/
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
/-- Field stalk comparison preserves geometric germ coordinates.

The prescribed-point germ followed by the stalk comparison equals the canonical-point germ at
the image fiber element. -/
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
/-- Prescribed field stalk is left adjoint to the canonical skyscraper.

Transport the canonical point adjunction through the stalk comparison to obtain this
adjunction. -/
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
/-- Canonical and prescribed field skyscraper functors are isomorphic.

Uniqueness of right adjoints gives a natural isomorphism from the canonical skyscraper functor
to the prescribed one. -/
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
/-- Field skyscraper comparison respects the adjunction unit.

The transported canonical unit followed by the skyscraper comparison equals the prescribed-
point unit. -/
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
/-- Field skyscraper comparison respects the adjunction counit.

Apply the prescribed stalk to the skyscraper comparison and then its counit; the result is the
transported canonical counit. -/
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
