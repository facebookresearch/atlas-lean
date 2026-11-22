/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordShapeBoundaries
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeSimplicialLayerPushout
import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedSums

/-!
# Actual free-word layer inclusions are anodyne

The entire raw attaching boundary is the original indexed sum of its
finite shape corners. Both source and target comparisons retain the
same original words and finite labels. Native coproduct and pushout
closure therefore prove actual layer inclusions anodyne, rather than
assuming a model-transfer acyclicity condition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The actual indexed sum of all original positive finite shape boundaries. -/
abbrev boundaryShapes (T : Data C) (a b : O) (n : ℕ) : SSet.{u} :=
  SSet.IndexedSums.object (fun s : Shape O (n + 1) => (shapeBoundary T s a b).toSSet)

/-- Include the same actual finite factors in their entire original shape sum. -/
def boundaryShapesMap (T : Data C) (a b : O) (n : ℕ) : boundaryShapes T a b n ⟶ shapeSum T a b (n + 1) :=
  SSet.IndexedSums.map (fun s : Shape O (n + 1) => (shapeBoundary T s a b).toSSet)
    (fun s => (shapeBoundary T s a b).ι)

/-- Decode the same original boundary factors into the actual whole raw attaching boundary. -/
def boundaryShapesHom (T : Data C) (a b : O) (n : ℕ) :
    boundaryShapes T a b n ⟶ (boundaryLayer T a b n).toSSet where
  app q := ↾fun p => ⟨shapeDecode T q p.1 p.2.val,
    length_shapeDecode T q p.1 p.2.val,
    Nat.lt_succ_iff.mp ((mem_shapeBoundary_iff T q p.1 p.2.val).mp p.2.property)⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact (rawOperator_shapeDecode T f p.1 p.2.val).symm

/-- The whole decoded boundary comparison commutes with the same actual raw-stratum inclusion. -/
theorem boundaryShapes_square (T : Data C) (a b : O) (n : ℕ) :
    boundaryShapesHom T a b n ≫ boundaryInclusion T a b n =
      boundaryShapesMap T a b n ≫ (shapeSumIso T a b n).hom := by
  ext q p
  rfl

/-- The original boundary factor comparison is bijective in every degree on the same finite labels. -/
theorem boundaryShapesHom_bijective (T : Data C) (a b : O) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    Function.Bijective ((boundaryShapesHom T a b n).app q) := by
  constructor
  · intro p p' h
    change (Σ s : Shape O (n + 1), {p : (shapeSpace T s a b).obj q //
      p ∈ (shapeBoundary T s a b).obj q}) at p p'
    have hv := congrArg (fun t : (boundaryLayer T a b n).toSSet.obj q => t.val) h
    have hd : (shapeSumEquiv T a b n q ⟨p.1, p.2.val⟩).val =
        (shapeSumEquiv T a b n q ⟨p'.1, p'.2.val⟩).val :=
      (shapeSumEquiv_apply T a b n q ⟨p.1, p.2.val⟩).trans
        (hv.trans (shapeSumEquiv_apply T a b n q ⟨p'.1, p'.2.val⟩).symm)
    have hs := (shapeSumEquiv T a b n q).injective (Subtype.ext hd)
    rcases p with ⟨s, p⟩
    rcases p' with ⟨s', p'⟩
    rcases Sigma.mk.inj hs with ⟨hh, hp⟩
    cases hh
    have hp' : p = p' := Subtype.ext (eq_of_heq hp)
    cases hp'
    rfl
  · intro p
    let t := (shapeSumEquiv T a b n q).symm ⟨p.val, p.property.1⟩
    have ht : (shapeSumEquiv T a b n q t).val = p.val :=
      congrArg Subtype.val ((shapeSumEquiv T a b n q).apply_symm_apply ⟨p.val, p.property.1⟩)
    have hb : t.2 ∈ (shapeBoundary T t.1 a b).obj q := by
      apply (mem_shapeBoundary_iff T q t.1 t.2).mpr
      rw [← shapeSumEquiv_apply T a b n q t, ht]
      exact Nat.lt_succ_of_le p.property.2
    refine ⟨⟨t.1, ⟨t.2, hb⟩⟩, ?_⟩
    exact Subtype.ext ht

/-- The same original whole boundary comparison is a genuine simplicial isomorphism. -/
instance boundaryShapesHom_isIso (T : Data C) (a b : O) (n : ℕ) :
    IsIso (boundaryShapesHom T a b n) := by
  let _ (q : SimplexCategoryᵒᵖ) : IsIso ((boundaryShapesHom T a b n).app q) :=
    (isIso_iff_bijective _).mpr (boundaryShapesHom_bijective T a b n q)
  exact NatIso.isIso_of_isIso_app _

/-- The whole original indexed corner map and the actual raw boundary inclusion are isomorphic arrows. -/
def boundaryShapesArrowIso (T : Data C) (a b : O) (n : ℕ) :
    Arrow.mk (boundaryShapesMap T a b n) ≅ Arrow.mk (boundaryInclusion T a b n) :=
  Arrow.isoMk' _ _ (asIso (boundaryShapesHom T a b n)) (shapeSumIso T a b n)
    (boundaryShapes_square T a b n)

/-- The actual whole raw attaching-boundary inclusion is anodyne for original anodyne attaching maps. -/
theorem boundaryInclusion_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) (n : ℕ) :
    SSet.anodyneExtensions (boundaryInclusion T a b n) := by
  have h : SSet.anodyneExtensions (boundaryShapesMap T a b n) :=
    SSet.IndexedSums.map_property
      (fun s : Shape O (n + 1) => (shapeBoundary T s a b).toSSet)
      SSet.anodyneExtensions (fun s => (shapeBoundary T s a b).ι)
      (fun s => shapeBoundary_anodyne T hi s a b)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (boundaryShapesArrowIso T a b n)).mp h

/-- Every actual original relative-word length layer inclusion is anodyne by its genuine pushout square. -/
theorem layerInclusion_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) (n : ℕ) :
    SSet.anodyneExtensions (layerInclusion T a b n) :=
  SSet.anodyneExtensions.of_isPushout (simplicialLayerIsPushout T a b n)
    (boundaryInclusion_anodyne T hi a b n)

/-- The same actual layer inclusions are trivial cofibrations in the native scalar model. -/
theorem layerInclusion_trivialCofibration (T : Data C)
    (hi : ∀ x y, trivialCofibrations SSet.{u} (T.inclusion x y)) (a b : O) (n : ℕ) :
    trivialCofibrations SSet.{u} (layerInclusion T a b n) := by
  rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
  apply layerInclusion_anodyne T _ a b n
  intro x y
  rw [SSet.anodyneExtensions_eq_trivialCofibrations]
  exact hi x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
