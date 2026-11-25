/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositiveCoverFullFaithful
import Mathlib.CategoryTheory.Equivalence

/-!
# The SAME original positive-cover path and native StructuredArrow equivalence

The actual original comma object is its individual target and SAME full
completed source path. The inverse functor uses those exact original
objects and the proved full native positive-path preimage. Both whole
functor identities and every original projected arrow are retained.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in both full native inverse functors. -/
private local instance coverQuiverForEquivalence : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The full native inverse comma functor retains its SAME individual original targets and paths. -/
def commaToCoverPaths : PositiveCoverComma V z ⥤ Paths (CoverVertex V z) where
  obj a := (commaToCoverVertex V z a : Paths (CoverVertex V z))
  map {a b} h := (coverPathsToComma V z).preimage
    (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ h ≫
      eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm)
  map_id a := by
    apply (coverPathsToComma V z).map_injective
    have hp := (coverPathsToComma V z).map_preimage
      (X := (commaToCoverVertex V z a : Paths (CoverVertex V z)))
      (Y := (commaToCoverVertex V z a : Paths (CoverVertex V z)))
      (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ 𝟙 a ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z a).symm)
    have hid : eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ 𝟙 a ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z a).symm =
          𝟙 (coverVertexToComma V z (commaToCoverVertex V z a)) := by
      rw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact hp.trans (hid.trans ((coverPathsToComma V z).map_id _).symm)
  map_comp {a b c} f g := by
    apply (coverPathsToComma V z).map_injective
    have hp := (coverPathsToComma V z).map_preimage
      (X := (commaToCoverVertex V z a : Paths (CoverVertex V z)))
      (Y := (commaToCoverVertex V z c : Paths (CoverVertex V z)))
      (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ (f ≫ g) ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z c).symm)
    have hf := (coverPathsToComma V z).map_preimage
      (X := (commaToCoverVertex V z a : Paths (CoverVertex V z)))
      (Y := (commaToCoverVertex V z b : Paths (CoverVertex V z)))
      (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ f ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm)
    have hg := (coverPathsToComma V z).map_preimage
      (X := (commaToCoverVertex V z b : Paths (CoverVertex V z)))
      (Y := (commaToCoverVertex V z c : Paths (CoverVertex V z)))
      (eqToHom (coverVertexToComma_commaToCoverVertex V z b) ≫ g ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z c).symm)
    have hc : (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ f ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm) ≫
      (eqToHom (coverVertexToComma_commaToCoverVertex V z b) ≫ g ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z c).symm) =
      eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ (f ≫ g) ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z c).symm := by
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact hp.trans (hc.symm.trans
      ((congrArg₂ (fun f g => f ≫ g) hf hg).symm.trans
        ((coverPathsToComma V z).map_comp _ _).symm))

/-- Every original native inverse comma object is the SAME complete original target/path vertex. -/
lemma commaToCoverPaths_obj (a : PositiveCoverComma V z) :
    (commaToCoverPaths V z).obj a = (⟨a.right, a.hom⟩ : CoverVertex V z) := rfl

/-- The actual full native forward/inverse functors recover EVERY original cover path. -/
theorem coverPathsToComma_comp_inverse : coverPathsToComma V z ⋙ commaToCoverPaths V z =
  𝟭 (Paths (CoverVertex V z))
  := by
  have ho : ∀ a : Paths (CoverVertex V z),
      (coverPathsToComma V z ⋙ commaToCoverPaths V z).obj a = a :=
    fun a => commaToCoverVertex_coverVertexToComma V z a
  refine Functor.hext ho ?_
  intro a b p
  have hc : ∀ a : CoverVertex V z,
      coverVertexToComma_commaToCoverVertex V z (coverVertexToComma V z a) =
        congrArg (coverVertexToComma V z) (commaToCoverVertex_coverVertexToComma V z a) :=
    fun a => Subsingleton.elim _ _
  have hp := (coverPathsToComma V z).map_preimage
    (X := ((coverPathsToComma V z ⋙ commaToCoverPaths V z).obj a))
    (Y := ((coverPathsToComma V z ⋙ commaToCoverPaths V z).obj b))
    (eqToHom (coverVertexToComma_commaToCoverVertex V z ((coverPathsToComma V z).obj a)) ≫
      (coverPathsToComma V z).map p ≫
      eqToHom (coverVertexToComma_commaToCoverVertex V z ((coverPathsToComma V z).obj b)).symm)
  apply (conj_eqToHom_iff_heq (C := Paths (CoverVertex V z)) _ _ (ho a) (ho b)).mp
  apply (coverPathsToComma V z).map_injective
  have ht := (coverPathsToComma V z).map_comp (eqToHom (ho a)) (p ≫ eqToHom (ho b).symm)
  have ht' := (coverPathsToComma V z).map_comp p (eqToHom (ho b).symm)
  have hmap : (coverPathsToComma V z).map (eqToHom (ho a) ≫ p ≫ eqToHom (ho b).symm) =
      eqToHom (coverVertexToComma_commaToCoverVertex V z ((coverPathsToComma V z).obj a)) ≫
        (coverPathsToComma V z).map p ≫
        eqToHom (coverVertexToComma_commaToCoverVertex V z ((coverPathsToComma V z).obj
          b)).symm := by
    exact ht.trans (congrArg₂ (fun f g => f ≫ g) (CategoryTheory.eqToHom_map
      (coverPathsToComma V z) (ho a))
      (ht'.trans (congrArg (fun g => (coverPathsToComma V z).map p ≫ g)
        (CategoryTheory.eqToHom_map (coverPathsToComma V z) (ho b).symm))))
  exact hp.trans hmap.symm

/-- The actual full native inverse/forward functors recover EVERY original structured-arrow map. -/
theorem commaToCoverPaths_comp_forward : commaToCoverPaths V z ⋙ coverPathsToComma V z =
  𝟭 (PositiveCoverComma V z)
  := by
  have ho : ∀ a : PositiveCoverComma V z,
      (commaToCoverPaths V z ⋙ coverPathsToComma V z).obj a = a :=
    fun a => coverVertexToComma_commaToCoverVertex V z a
  refine CategoryTheory.Functor.hext ho ?_
  intro a b h
  apply (conj_eqToHom_iff_heq (C := PositiveCoverComma V z) _ _ (ho a) (ho b)).mp
  exact (coverPathsToComma V z).map_preimage
    (X := (commaToCoverVertex V z a : Paths (CoverVertex V z)))
    (Y := (commaToCoverVertex V z b : Paths (CoverVertex V z))) _

/-- The SAME complete original positive path category is equivalent to its actual native
completion comma. -/
def positiveCoverEquivalence : Paths (CoverVertex V z) ≌ PositiveCoverComma V z :=
  CategoryTheory.Equivalence.mk (coverPathsToComma V z) (commaToCoverPaths V z)
    (eqToIso (coverPathsToComma_comp_inverse V z).symm)
    (eqToIso (commaToCoverPaths_comp_forward V z))

/-- The equivalence keeps the SAME original full forward native comma functor. -/
lemma positiveCoverEquivalence_functor : (positiveCoverEquivalence V z).functor =
  coverPathsToComma V z := rfl

/-- The equivalence keeps the SAME actual inverse native object and full-path decoder. -/
lemma positiveCoverEquivalence_inverse : (positiveCoverEquivalence V z).inverse =
  commaToCoverPaths V z := rfl

/-- EVERY original forward path reads back its SAME full original projected path. -/
lemma positiveCoverEquivalence_forward_path {a b : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b) :
    ((positiveCoverEquivalence V z).functor.map p).right = (coverProjection V z).mapPath p :=
  coverPathsToComma_map_right V z p

/-- EVERY inverse original native comma arrow retains the SAME whole original positive path. -/
lemma positiveCoverEquivalence_inverse_path {a b : PositiveCoverComma V z} (h : a ⟶ b) :
    (coverProjection V z).mapPath ((commaToCoverPaths V z).map h) = h.right := by
  have hm := (coverPathsToComma_map_right V z ((commaToCoverPaths V z).map h)).symm
  have he := (coverPathsToComma V z).map_preimage
    (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ h ≫
      eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm)
  have hp := congrArg (fun h => h.right) he
  have ht : (eqToHom (coverVertexToComma_commaToCoverVertex V z a) ≫ h ≫
      eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm).right = h.right := by
    have hproj : ∀ {a b : PositiveCoverComma V z} (e : a = b),
        (eqToHom e).right = eqToHom (congrArg StructuredArrow.right e) := by
      intro a b e
      subst b
      rfl
    have hs : (eqToHom (coverVertexToComma_commaToCoverVertex V z a)).right = 𝟙 a.right := by
      exact (hproj _).trans (congrArg eqToHom (Subsingleton.elim _ rfl))
    have hb : (eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm).right = 𝟙 b.right := by
      exact (hproj _).trans (congrArg eqToHom (Subsingleton.elim _ rfl))
    change (eqToHom (coverVertexToComma_commaToCoverVertex V z a)).right ≫
      h.right ≫ (eqToHom (coverVertexToComma_commaToCoverVertex V z b).symm).right = h.right
    exact (congrArg₂ (fun f g => f ≫ g) hs
      (congrArg (fun g => h.right ≫ g) hb)).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  exact hm.trans (hp.trans ht)

end Quiver.FreeGroupoid.OriginalWords
