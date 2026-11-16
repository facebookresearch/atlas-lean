/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/AlgebraicGeometry/AffineGroupScheme/Equivalence.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import MathlibExt.AlgebraicGeometry.AffineGroupScheme.Basic
public import MathlibExt.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Affine group schemes are anti-equivalent to commutative Hopf algebras

Over a commutative ring `S`, the contravariant functor `Spec` is an equivalence from the opposite of
the category of commutative `S`-Hopf algebras onto the category of affine group schemes over
`Spec S`.

Mathlib's `AlgebraicGeometry/Group/Affine.lean` provides the functor
(`AlgebraicGeometry.hopfSpec`), its full faithfulness, and the characterization of its
essential image as the affine group schemes (`AlgebraicGeometry.essImage_hopfSpec`);
this file composes them into the equivalence with the category
`MathlibExt.AffineGroupSchemeCat` of the parent file.

`MathlibExt.AffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso` identifies an affine group
scheme with the Hopf spectrum of its coordinate algebra, using the counit of this equivalence.
-/

public section

namespace MathlibExt

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- `Spec` as an anti-equivalence from commutative `S`-Hopf algebras onto affine group
schemes over `Spec S`. The underlying functor is Mathlib's `AlgebraicGeometry.hopfSpec`,
which is fully faithful with essential image the affine group schemes; the isomorphism
`commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso` records this on the level
of functors, and is the intended interface for computing with the equivalence. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat (S : CommRingCat.{u}) :
    (CommHopfAlgCat S)ᵒᵖ ≌ AffineGroupSchemeCat S :=
  (hopfSpec S).toEssImage.asEquivalence.trans (ObjectProperty.fullSubcategoryCongr
      (funext fun G => propext (essImage_hopfSpec.trans (affineGroupSchemeProperty_iff G).symm)))

/-- The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat`, followed by the
inclusion of the full subcategory, is `hopfSpec`: the anti-equivalence really does act
by `Spec`. Consumers should transport along this isomorphism (and its `app` components
and naturality squares) rather than unfold the equivalence. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (S : CommRingCat.{u}) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat S).functor ⋙
      (affineGroupSchemeProperty S).ι ≅ hopfSpec S := by
  -- The equivalence is built as `toEssImage.asEquivalence.trans (fullSubcategoryCongr _)`,
  -- so its forward functor is, by definition of `Equivalence.trans`, `asEquivalence`, and
  -- `fullSubcategoryCongr`, the composite `toEssImage ⋙ ιOfLE _`. This `change` performs
  -- that unavoidable reduction once, explicitly; the isomorphism is then assembled from
  -- the public whiskering API.
  change ((hopfSpec S).toEssImage ⋙
      ObjectProperty.ιOfLE fun G hG => (affineGroupSchemeProperty_iff G).mpr
        (essImage_hopfSpec.mp hG)) ⋙
      (affineGroupSchemeProperty S).ι ≅ hopfSpec S
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (hopfSpec S).toEssImage (ObjectProperty.ιOfLECompιIso _) ≪≫
    (hopfSpec S).toEssImageCompι

/-- The object produced by the affine Hopf/group-scheme anti-equivalence is the bundled Hopf
spectrum. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat.functorObjIso
    (R : Type u) [CommRing R] (H : (CommHopfAlgCat.{u} R)ᵒᵖ) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
        (CommRingCat.of R)).functor.obj H ≅
      ⟨(hopfSpec (CommRingCat.of R)).obj H, by
        rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
        infer_instance⟩ :=
  (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
    ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
      (CommRingCat.of R)).app H)

/-- The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat` sends a Hopf algebra to the
bundled Hopf spectrum, as an equality of objects. Unlike `functorObjIso`, this equality lets one
transport an arbitrary object property, with no isomorphism invariance needed, so it can be used to
rewrite `P ((commHopfAlgCatOpEquivAffineGroupSchemeCat _).functor.obj H)`. -/
theorem commHopfAlgCatOpEquivAffineGroupSchemeCat.functor_obj
    (R : Type u) [CommRing R] (H : (CommHopfAlgCat.{u} R)ᵒᵖ) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor.obj H =
      ⟨(hopfSpec (CommRingCat.of R)).obj H, by
        rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
        infer_instance⟩ := by
  -- The equivalence is `toEssImage.asEquivalence` composed with `fullSubcategoryCongr`, whose
  -- forward functor acts on objects as `toEssImage` followed by the inclusion of the full
  -- subcategory; neither step changes the underlying scheme.
  rfl

/-- An affine group scheme is the Hopf spectrum of its coordinate Hopf algebra. -/
noncomputable def AffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso
    (R : Type u) [CommRing R] (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    (hopfSpec (CommRingCat.of R)).obj
        ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse.obj G) ≅ G.obj :=
  ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (CommRingCat.of R)).app
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).inverse.obj G)).symm ≪≫
    (affineGroupSchemeProperty (CommRingCat.of R)).ι.mapIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).counitIso.app G)

/-- To identify the inverse image of a property of affine group schemes
under the Hopf-algebra/group-scheme anti-equivalence, it suffices to identify that property on
Hopf spectra. -/
theorem objectProperty_inverseImage_commHopfAlgCatOpEquiv
    (R : Type u) [CommRing R]
    (P : ObjectProperty (AffineGroupSchemeCat (CommRingCat.of R)))
    (Q : ObjectProperty (CommHopfAlgCat.{u} R))
    (h : ∀ H, P ⟨(hopfSpec (CommRingCat.of R)).obj (op H), by
      rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
      infer_instance⟩ ↔ Q H) :
    P.inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor = Q.op := by
  ext H
  rw [ObjectProperty.prop_inverseImage_iff, ObjectProperty.op_iff,
    commHopfAlgCatOpEquivAffineGroupSchemeCat.functor_obj]
  exact h H.unop

end MathlibExt
