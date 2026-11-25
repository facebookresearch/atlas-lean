/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/AlgebraicGeometry/AffineGroupScheme/CartierDuality/FiniteLocallyFree.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import MathlibExt.Algebra.HopfAlgebra.FiniteDual.CartierDuality.Basic
public import MathlibExt.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import MathlibExt.CategoryTheory.Monoidal.Mon

/-!
# Cartier duality over an affine base

This file transports finite locally free Cartier duality from coordinate Hopf algebras to
commutative affine group schemes over an arbitrary commutative ring. A morphism to an affine base
is finite locally free when it is finite, flat, and locally of finite presentation. For a Hopf
spectrum these three conditions say exactly that its coordinate algebra is finite projective over
the base (`MathlibExt.moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec`).
Commutativity of the group object is cocommutativity of the coordinate Hopf algebra
(`MathlibExt.isCocomm_iff_isCommMonObj_hopfSpec`).

The resulting anti-equivalence is Cartier duality over an arbitrary affine base. Its objects
explicitly include flatness and finite presentation; these hypotheses cannot be omitted over a
general ring. Because the Hopf-algebra equivalence being transported already knows its own
inverse, so does this one: the inverse is Cartier dualization again, and the counit is the
inverse of the double-dual isomorphism `cartierDualDualIso`.

## Main declarations

* `MathlibExt.finiteLocallyFreeCommAffineGroupSchemeProperty`: the object property selecting finite
  locally free commutative affine group schemes over an affine base.
* `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat`: the category selected by that property.
* `finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat`:
  the restricted anti-equivalence over a commutative ring.
  Its `functorCompFullSubcategoryιIso`, `functorCompιIso`, `inverseCompιIso`, and
  `rightOpInverseCompιIso` describe the two functors after forgetting the property proofs.
* `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDuality`: Cartier duality over an
  arbitrary affine base, with `cartierDuality_functor` and `cartierDuality_inverse` computing
  both of its directions as transported finite dualization.
* `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDual` and
  `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.coordinateHopfAlgebra`: the Cartier dual of
  a
  group scheme and its coordinate Hopf algebra, related by `cartierDual_eq` and
  `coordinateHopfAlgebraCartierDualIso`.
* `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso`:
  the comparison with the Hopf spectrum of the coordinate algebra in the ambient affine category.
* `MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat.cartierDualDualIso`: the double-dual
  isomorphism `G ≅ D(D(G))`, natural by `cartierDualDualIso_hom_naturality`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 11.c, with Aside 11.17 for a base ring.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace MathlibExt

universe u

/-- The object property selecting finite locally free commutative affine group schemes over an
affine base. Finite local freeness is expressed by the standard scheme-theoretic conjunction of
finiteness, flatness, and local finite presentation. -/
def finiteLocallyFreeCommAffineGroupSchemeProperty (S : CommRingCat.{u}) :
    ObjectProperty (AffineGroupSchemeCat S) :=
  fun G => IsFinite G.obj.X.hom ∧ Flat G.obj.X.hom ∧
    LocallyOfFinitePresentation G.obj.X.hom ∧ IsCommMonObj G.obj.X

/-- Membership in the finite-locally-free commutative affine-group-scheme property. -/
@[simp]
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_iff
    (S : CommRingCat.{u}) (G : AffineGroupSchemeCat S) :
    finiteLocallyFreeCommAffineGroupSchemeProperty S G ↔
      IsFinite G.obj.X.hom ∧ Flat G.obj.X.hom ∧
        LocallyOfFinitePresentation G.obj.X.hom ∧ IsCommMonObj G.obj.X :=
  Iff.rfl

instance (S : CommRingCat.{u}) :
    (finiteLocallyFreeCommAffineGroupSchemeProperty S).IsClosedUnderIsomorphisms where
  of_iso e hG := by
    let e' := (affineGroupSchemeProperty S).ι.mapIso e
    exact ⟨(MorphismProperty.over_iso_iff (@IsFinite) ((Grp.forget _).mapIso e')).mp hG.1,
      (MorphismProperty.over_iso_iff (@Flat) ((Grp.forget _).mapIso e')).mp hG.2.1,
      (MorphismProperty.over_iso_iff (@LocallyOfFinitePresentation)
        ((Grp.forget _).mapIso e')).mp hG.2.2.1,
      isCommMonObj_of_grp_iso e' hG.2.2.2⟩

/-- Under the affine Hopf/group-scheme anti-equivalence over a commutative ring, finite
projectivity and cocommutativity of the coordinate Hopf algebra correspond to finite local
freeness and commutativity of the affine group scheme. -/
theorem finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage
    (R : Type u) [CommRing R] :
    (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor =
      (finiteLocallyFreeBicommutativeHopfAlgProperty R).op := by
  apply objectProperty_inverseImage_commHopfAlgCatOpEquiv R
  intro H
  rw [finiteLocallyFreeCommAffineGroupSchemeProperty_iff,
    finiteLocallyFreeBicommutativeHopfAlgProperty_iff]
  constructor
  · intro h
    have hfinite : Module.Finite R H :=
      (moduleFinite_iff_isFinite_hopfSpec R H).mpr h.1
    let _ : Module.Finite R H := hfinite
    exact ⟨hfinite,
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H).mpr
        ⟨h.2.1, h.2.2.1⟩,
      (isCocomm_iff_isCommMonObj_hopfSpec R H).mpr h.2.2.2⟩
  · intro h
    let _ : Module.Finite R H := h.1
    have hprojective :=
      (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec R H).mp h.2.1
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H).mp h.1,
      hprojective.1, hprojective.2,
      (isCocomm_iff_isCommMonObj_hopfSpec R H).mp h.2.2⟩

/-- The category of finite locally free commutative affine group schemes over an affine base. -/
abbrev FiniteLocallyFreeCommAffineGroupSchemeCat (S : CommRingCat.{u}) : Type _ :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty S).FullSubcategory

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    IsFinite G.obj.obj.X.hom := G.property.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    Flat G.obj.obj.X.hom := G.property.2.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    LocallyOfFinitePresentation G.obj.obj.X.hom := G.property.2.2.1

instance {S : CommRingCat.{u}} (G : FiniteLocallyFreeCommAffineGroupSchemeCat S) :
    IsCommMonObj G.obj.obj.X := G.property.2.2.2

/-- `Spec` as an anti-equivalence from finite locally free bicommutative Hopf algebras to finite
locally free commutative affine group schemes over an arbitrary commutative ring. -/
noncomputable def
    finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    (R : Type u) [CommRing R] :
    (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)ᵒᵖ ≌
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (ObjectProperty.opEquivalence
    (finiteLocallyFreeBicommutativeHopfAlgProperty R)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).congrFullSubcategory
        (finiteLocallyFreeCommAffineGroupSchemeProperty_inverseImage R)

namespace finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

/-- The restricted equivalence followed by the finite-locally-free inclusion is the unrestricted
equivalence applied after forgetting the property proofs. This isomorphism isolates the
implementation of the object-property restrictions, so that downstream files never have to unfold
them. -/
noncomputable def functorCompFullSubcategoryιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor ⋙
        (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor :=
  Iso.refl _

/-- Over a commutative ring $R$, the anti-equivalence from finite locally free bicommutative Hopf
algebras to finite locally free commutative affine group schemes, followed by the inclusions into
affine group schemes and into all group schemes over $\operatorname{Spec} R$, is isomorphic to the
forgetful functor to commutative Hopf algebras followed by the Hopf spectrum functor `hopfSpec`. -/
noncomputable def functorCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor ⋙
        (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of R)).ι ≅
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ⋙ hopfSpec (CommRingCat.of R) :=
  Functor.isoWhiskerRight
      (functorCompFullSubcategoryιIso R)
      (affineGroupSchemeProperty (CommRingCat.of R)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
        (CommHopfAlgCat.{u} R)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (CommRingCat.of R))

/-- The object produced by the finite-locally-free Hopf/group-scheme anti-equivalence is
its bundled Hopf spectrum. -/
noncomputable def functorObjIso (R : Type u) [CommRing R]
    (H : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)ᵒᵖ) :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj H ≅
      ⟨⟨(hopfSpec (CommRingCat.of R)).obj (op H.unop.obj), by
          rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
          infer_instance⟩, by
        have hH := (finiteLocallyFreeBicommutativeHopfAlgProperty_iff R H.unop.obj).mp
          H.unop.property
        let _ : Module.Finite R H.unop.obj := hH.1
        have hp := (moduleProjective_iff_flat_and_locallyOfFinitePresentation_hopfSpec
          R H.unop.obj).mp hH.2.1
        exact ⟨(moduleFinite_iff_isFinite_hopfSpec R H.unop.obj).mp
          hH.1, hp.1, hp.2,
          (isCocomm_iff_isCommMonObj_hopfSpec R H.unop.obj).mp hH.2.2⟩⟩ :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
    ((affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((functorCompιIso R).app H))

/-- After forgetting the property proofs, the object comparison is the Hopf--spectrum
functor comparison. -/
theorem functorObjIso_hom_hom_hom (R : Type u) [CommRing R]
    (H : (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)ᵒᵖ) :
    (functorObjIso R H).hom.hom.hom = (functorCompιIso R).hom.app H := by
  calc
    _ = (affineGroupSchemeProperty (CommRingCat.of R)).ι.map
        ((finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.map
          (functorObjIso R H).hom) := rfl
    _ = _ := by
      rw [functorObjIso, Functor.preimageIso_hom, Functor.map_preimage,
        Functor.preimageIso_hom, Functor.map_preimage]
      rfl

/-- The inverse restricted anti-equivalence computes as the unrestricted coordinate-Hopf-algebra
functor after forgetting finite local freeness and commutativity. -/
noncomputable def inverseCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).inverse ⋙
        (forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R)
          (CommHopfAlgCat.{u} R)).op ≅
      (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse :=
  Iso.refl _

/-- The `rightOp` inverse used in scheme-level Cartier duality computes, after forgetting
finiteness, projectivity and cocommutativity, as the opposite of the unrestricted coordinate
Hopf-algebra functor. -/
noncomputable def rightOpInverseCompιIso (R : Type u) [CommRing R] :
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).rightOp.inverse ⋙
        forget₂ (FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) (CommHopfAlgCat.{u} R) ≅
      ((finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse).leftOp := by
  let e := inverseCompιIso R
  exact
    { hom := e.inv.leftOp
      inv := e.hom.leftOp }

end finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

namespace FiniteLocallyFreeCommAffineGroupSchemeCat

open finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat

/-- **Cartier duality for finite locally free commutative affine group schemes over an arbitrary
commutative base ring.**

Transporting `FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality` rather than the bare
dualization functor keeps the inverse computable: it is again Cartier dualization, and the counit
is the inverse of the double-dual evaluation isomorphism `cartierDualDualIso`.

The body is exposed so that `cartierDuality_inverse` holds definitionally, without which
`cartierDualDualNatIso` does not typecheck. -/
@[expose]
noncomputable def cartierDuality
    (R : Type u) [CommRing R] :
    (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))ᵒᵖ ≌
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp).symm.trans <|
    (FiniteLocallyFreeBicommutativeHopfAlgCat.cartierDuality (k := R)).rightOp.trans
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat R)

/-- The forward functor of Cartier duality over an arbitrary affine base is finite dualization
transported through the finite-locally-free Hopf--spectrum anti-equivalence. -/
@[simp]
theorem cartierDuality_functor (R : Type u) [CommRing R] :
    (cartierDuality R).functor =
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse ⋙
        (FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor (k := R)).rightOp ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor :=
  (rfl)

/-- Cartier dualization as a contravariant endofunctor on finite locally free commutative affine
group schemes. -/
noncomputable abbrev cartierDualFunctor (R : Type u) [CommRing R] :
    (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R))ᵒᵖ ⥤
      FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (cartierDuality R).functor

/-- The inverse of Cartier duality is Cartier dualization again. This is the identification that
`CategoryTheory.Functor.asEquivalence` cannot provide. -/
@[simp]
theorem cartierDuality_inverse (R : Type u) [CommRing R] :
    (cartierDuality R).inverse = (cartierDualFunctor R).rightOp :=
  (rfl)

/-- The coordinate Hopf algebra of a finite locally free commutative affine group scheme. -/
noncomputable abbrev coordinateHopfAlgebra (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R :=
  (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp.inverse.obj (op G)

/-- The Hopf spectrum of the coordinate Hopf algebra recovers the original affine group scheme,
after forgetting finite local freeness and commutativity. -/
noncomputable def hopfSpecCoordinateHopfAlgebraIso (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor.obj
        (op (coordinateHopfAlgebra R G).obj) ≅
      (finiteLocallyFreeCommAffineGroupSchemeProperty (CommRingCat.of R)).ι.obj G := by
  -- `coordinateHopfAlgebra` uses `rightOp.inverse`; after taking `op` and forgetting the
  -- property proofs it is the source of `inverseCompιIso.app G`.
  let e := (inverseCompιIso R).app G
  exact (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (CommRingCat.of R)).app
        (op (coordinateHopfAlgebra R G).obj) ≪≫
      (hopfSpec (CommRingCat.of R)).mapIso e ≪≫
      AffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso R G.obj)

/-- The Cartier dual of a finite locally free commutative affine group scheme. -/
noncomputable abbrev cartierDual (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R) :=
  (cartierDualFunctor R).obj (op G)

/-- The Cartier dual is represented by the finite dual of the coordinate Hopf algebra. -/
@[simp]
theorem cartierDual_eq (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    cartierDual R G =
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj
          (op (FiniteLocallyFreeBicommutativeHopfAlgCat.dual (coordinateHopfAlgebra R G))) :=
  (rfl)

/-- Cartier dualization of a Hopf spectrum is the Hopf spectrum of the finite dual. -/
noncomputable def cartierDualHopfSpecIso (R : Type u) [CommRing R]
    (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    cartierDual R
        ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).functor.obj (op H)) ≅
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).functor.obj (op (FiniteLocallyFreeBicommutativeHopfAlgCat.dual H)) := by
  rw [cartierDual_eq]
  exact
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).functor.mapIso
        ((FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor.mapIso
          ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
            R).unitIso.app (op H))).op)

/-- On morphisms, the Hopf--spectrum duality comparison is induced by the equivalence unit
and finite dualization. -/
theorem cartierDualHopfSpecIso_hom (R : Type u) [CommRing R]
    (H : FiniteLocallyFreeBicommutativeHopfAlgCat.{u} R) :
    let E :=
      finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat R
    (cartierDualHopfSpecIso R H).hom =
      eqToHom (cartierDual_eq R _) ≫ E.functor.map
        ((FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor.mapIso
          (E.unitIso.app (op H))).op.hom) := by
  rfl

/-- **The coordinate Hopf algebra of a Cartier dual is the finite dual of the coordinate Hopf
algebra**, naturally in the group scheme. -/
noncomputable def coordinateHopfAlgebraCartierDualNatIso (R : Type u) [CommRing R] :
    (cartierDualFunctor R).rightOp ⋙
        (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.inverse ≅
      (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
          R).rightOp.inverse.rightOp ⋙ FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor :=
  Functor.isoWhiskerLeft
    ((finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
        R).rightOp.inverse.rightOp ⋙ FiniteLocallyFreeBicommutativeHopfAlgCat.dualFunctor)
    (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
      R).rightOp.unitIso.symm

/-- The coordinate Hopf algebra of the Cartier dual of a single group scheme. -/
noncomputable abbrev coordinateHopfAlgebraCartierDualIso (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    coordinateHopfAlgebra R (cartierDual R G) ≅
      FiniteLocallyFreeBicommutativeHopfAlgCat.dual (coordinateHopfAlgebra R G) :=
  (coordinateHopfAlgebraCartierDualNatIso R).app G

/-- **Cartier duality is involutive.** Every finite locally free commutative affine group scheme
is naturally isomorphic to its Cartier double dual. -/
noncomputable def cartierDualDualNatIso (R : Type u) [CommRing R] :
    𝟭 (FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) ≅
      (cartierDualFunctor R).rightOp ⋙ cartierDualFunctor R :=
  (cartierDuality R).counitIso.symm

/-- The double-dual isomorphism of a single finite locally free commutative affine group
scheme. -/
noncomputable abbrev cartierDualDualIso (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    G ≅ cartierDual R (cartierDual R G) :=
  (cartierDualDualNatIso R).app G

/-- The double-dual isomorphism is the inverse counit of `cartierDuality`. -/
@[simp]
theorem cartierDualDualNatIso_hom_app (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    (cartierDualDualNatIso R).hom.app G = (cartierDuality R).counitIso.inv.app G :=
  (rfl)

/-- The inverse double-dual isomorphism is the counit of `cartierDuality`. -/
@[simp]
theorem cartierDualDualNatIso_inv_app (R : Type u) [CommRing R]
    (G : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)) :
    (cartierDualDualNatIso R).inv.app G = (cartierDuality R).counitIso.hom.app G :=
  (rfl)

/-- The double-dual isomorphism is natural in the group scheme. -/
@[reassoc]
theorem cartierDualDualIso_hom_naturality (R : Type u) [CommRing R]
    {G H : FiniteLocallyFreeCommAffineGroupSchemeCat (CommRingCat.of R)} (f : G ⟶ H) :
    f ≫ (cartierDualDualIso R H).hom =
      (cartierDualDualIso R G).hom ≫
        (cartierDualFunctor R).map ((cartierDualFunctor R).map f.op).op :=
  (cartierDualDualNatIso R).hom.naturality f

end FiniteLocallyFreeCommAffineGroupSchemeCat

end MathlibExt
