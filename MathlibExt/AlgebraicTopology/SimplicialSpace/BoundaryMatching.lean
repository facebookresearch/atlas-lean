/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSpace.EnrichedYoneda
import MathlibExt.AlgebraicTopology.SimplicialSpace.ZerothRow
import MathlibExt.AlgebraicTopology.SimplicialObject.Matching
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGeneratingFamilies
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Inner maps from the original outer boundary

For each fixed outer degree, the actual inner mapping functor out of the
original designated discrete boundary is naturally the matching functor.
The proof uses every scalar, the existing boundary descent, and the original
proper-face maps. Degree zero is handled as an empty boundary and index.

Naturality is in the target at fixed degree. No boundary functor on arbitrary
simplex operators and no model or generator assertion is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace

private abbrev D (A : SSet.{u}) : SimplicialSpace.{u} :=
  ofSimplicialObject.obj (SSet.simplicialSpaceDiscrete.obj A)

private abbrev B (m : ℕ) : SimplicialSpace.{u} := D (SSet.boundary.{u} m : SSet.{u})
private abbrev F (m : ℕ) : SimplicialSpace.{u} := D (Δ[m] : SSet.{u})

private abbrev repIso (m : ℕ) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.obj (op (F m))).obj Z ≅ Z.diagram.obj (op ⦋m⦌) :=
  SSet.Rezk.pointwiseYonedaIso m Z.diagram

private lemma repIso_target (m : ℕ) {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (innerHomFunctor.obj (op (F m))).map p ≫ (repIso m Y).hom =
      (repIso m X).hom ≫ p.hom.app (op ⦋m⦌) :=
  SSet.Rezk.pointwiseYonedaIso_naturality_target m p.hom

private lemma repIso_index {k l : ℕ} (g : ⦋k⦌ ⟶ ⦋l⦌) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map
      (ofSimplicialObject.map
          (SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map g))).op).app Z ≫
        (repIso k Z).hom = (repIso l Z).hom ≫ Z.diagram.map g.op :=
  SSet.Rezk.pointwiseYonedaIso_naturality_index g Z.diagram

private lemma proper_not_surjective {m : ℕ}
    (a : SimplicialObject.matchingIndex m) :
    ¬ Function.Surjective a.obj.hom.unop.toOrderHom := by
  intro h
  let _ : Epi a.obj.hom.unop := (SimplexCategory.epi_iff_surjective (f := a.obj.hom.unop)).2 h
  exact (Nat.not_le_of_lt a.property.2) (SimplexCategory.len_le_of_epi a.obj.hom.unop)

private def boundarySimplexι {m : ℕ} (a : SimplicialObject.matchingIndex m) :
    (Δ[a.obj.right.unop.len] : SSet.{u}) ⟶ (SSet.boundary.{u} m : SSet.{u}) :=
  SSet.Subcomplex.lift (SSet.stdSimplex.map a.obj.hom.unop) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff,
      SSet.yonedaEquiv_map]
    change ¬ Function.Surjective a.obj.hom.unop.toOrderHom
    exact proper_not_surjective a)

private lemma boundarySimplexι_ι {m : ℕ} (a : SimplicialObject.matchingIndex m) :
    boundarySimplexι.{u} a ≫ (SSet.boundary.{u} m).ι =
      SSet.stdSimplex.map a.obj.hom.unop :=
  SSet.Subcomplex.lift_ι _ _

/-- The canonical original proper-face map into the designated discrete boundary.
Its degree is fixed; no functor on arbitrary simplex operators is claimed. -/
abbrev boundaryFaceMap {m : ℕ} (a : SimplicialObject.matchingIndex m) :
    ofSimplicialObject.obj (SSet.Rezk.representable.{u} a.obj.right.unop.len) ⟶
      ofSimplicialObject.obj
        (SSet.simplicialSpaceDiscrete.obj (SSet.boundary.{u} m : SSet.{u})) :=
  ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map (boundarySimplexι.{u} a))

/-- The proper-face map retains its original standard-simplex composite. -/
@[reassoc]
lemma boundaryFaceMap_boundary {m : ℕ} (a : SimplicialObject.matchingIndex m) :
    boundaryFaceMap.{u} a ≫ ReedyGeneratingFamilies.outerBoundaryMap.{u} m =
      ofSimplicialObject.map
        (SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map a.obj.hom.unop)) := by
  rw [← ofSimplicialObject.map_comp, ← SSet.simplicialSpaceDiscrete.map_comp,
    boundarySimplexι_ι]

private lemma boundarySimplexι_naturality {m : ℕ}
    {a b : SimplicialObject.matchingIndex m} (g : a ⟶ b) :
    SSet.stdSimplex.map g.hom.right.unop ≫ boundarySimplexι.{u} a =
      boundarySimplexι.{u} b := by
  apply (cancel_mono (SSet.boundary.{u} m).ι).1
  rw [Category.assoc, boundarySimplexι_ι, boundarySimplexι_ι, ← SSet.stdSimplex.map_comp]
  apply SSet.stdSimplex.congr_map
  exact congrArg Quiver.Hom.unop (StructuredArrow.w g.hom)

private lemma boundaryFaceMap_naturality {m : ℕ}
    {a b : SimplicialObject.matchingIndex m} (g : a ⟶ b) :
    ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map
      (SSet.stdSimplex.map g.hom.right.unop)) ≫ boundaryFaceMap.{u} a =
        boundaryFaceMap.{u} b := by
  rw [← ofSimplicialObject.map_comp, ← SSet.simplicialSpaceDiscrete.map_comp,
    boundarySimplexι_naturality]

private def boundaryCone (m : ℕ) (Z : SimplicialSpace.{u}) :
    Cone (SimplicialObject.matchingDiagram Z.diagram m) where
  pt := (innerHomFunctor.obj (op (B m))).obj Z
  π :=
    { app := fun a => (innerHomFunctor.map (boundaryFaceMap a).op).app Z ≫
        (repIso a.obj.right.unop.len Z).hom
      naturality := by
        intro a b g
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        change (innerHomFunctor.map (boundaryFaceMap b).op).app Z ≫
            (repIso b.obj.right.unop.len Z).hom =
          ((innerHomFunctor.map (boundaryFaceMap a).op).app Z ≫
            (repIso a.obj.right.unop.len Z).hom) ≫ Z.diagram.map g.hom.right
        have hy := repIso_index g.hom.right.unop Z
        simp only [Quiver.Hom.op_unop] at hy
        rw [Category.assoc, ← hy]
        rw [← Category.assoc, ← NatTrans.comp_app, ← innerHomFunctor.map_comp]
        rw [← op_comp, boundaryFaceMap_naturality]
    }

private abbrev V (K : SSet.{u}) (Z : SimplicialSpace.{u}) : SSet.{u} :=
  SSet.Rezk.zerothRow.obj ((innerCotensor K).obj Z).diagram

private def scalarHomEquiv (K A : SSet.{u}) (Z : SimplicialSpace.{u}) :
    (K ⟶ (innerHomFunctor.obj (op (D A))).obj Z) ≃ (A ⟶ V K Z) :=
  (((innerTensorHomEquiv K (D A) Z).symm.trans
    ((innerTensorCotensorAdjunction K).homEquiv (D A) Z)).trans
      SimplicialSpace.homEquiv).trans
    (SSet.Rezk.zerothRowAdjunction.homEquiv A ((innerCotensor K).obj Z).diagram)

private lemma scalarHomEquiv_source (K : SSet.{u}) {A A' : SSet.{u}}
    (g : A ⟶ A') (Z : SimplicialSpace.{u})
    (f : K ⟶ (innerHomFunctor.obj (op (D A'))).obj Z) :
    scalarHomEquiv K A Z (f ≫
      (innerHomFunctor.map
          (ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map g)).op).app Z) =
        g ≫ scalarHomEquiv K A' Z f := by
  let d := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map g)
  have h : (innerTensorHomEquiv K (D A) Z).symm
      (f ≫ (innerHomFunctor.map d.op).app Z) =
      (innerTensor K).map d ≫ (innerTensorHomEquiv K (D A') Z).symm f := by
    apply (innerTensorHomEquiv K (D A) Z).injective
    rw [innerTensorHomEquiv_source]
    simp only [Equiv.apply_symm_apply]
  change (SSet.Rezk.zerothRowAdjunction.homEquiv A _)
      (SimplicialSpace.homEquiv
        (((innerTensorCotensorAdjunction K).homEquiv (D A) Z)
          ((innerTensorHomEquiv K (D A) Z).symm
            (f ≫ (innerHomFunctor.map d.op).app Z)))) =
    g ≫ (SSet.Rezk.zerothRowAdjunction.homEquiv A' _)
      (SimplicialSpace.homEquiv
        (((innerTensorCotensorAdjunction K).homEquiv (D A') Z)
          ((innerTensorHomEquiv K (D A') Z).symm f)))
  rw [h, (innerTensorCotensorAdjunction K).homEquiv_naturality_left]
  exact SSet.Rezk.zerothRowAdjunction.homEquiv_naturality_left g _

private def scalarRepEquiv (K : SSet.{u}) (Z : SimplicialSpace.{u}) (n : ℕ) :
    (K ⟶ Z.diagram.obj (op ⦋n⦌)) ≃ ((Δ[n] : SSet.{u}) ⟶ V K Z) :=
  (Iso.homCongr (Iso.refl K) (repIso n Z).symm).trans
    (scalarHomEquiv K (Δ[n] : SSet.{u}) Z)

private lemma scalarRepEquiv_index (K : SSet.{u}) (Z : SimplicialSpace.{u})
    {k l : ℕ} (g : ⦋k⦌ ⟶ ⦋l⦌) (h : K ⟶ Z.diagram.obj (op ⦋l⦌)) :
    scalarRepEquiv K Z k (h ≫ Z.diagram.map g.op) =
      SSet.stdSimplex.map g ≫ scalarRepEquiv K Z l h := by
  have hi : Z.diagram.map g.op ≫ (repIso k Z).inv =
      (repIso l Z).inv ≫
        (innerHomFunctor.map (ofSimplicialObject.map
          (SSet.simplicialSpaceDiscrete.map (SSet.stdSimplex.map g))).op).app Z := by
    apply (cancel_mono (repIso k Z).hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, repIso_index, Iso.inv_hom_id_assoc]
  simp only [scalarRepEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.symm_hom, Category.id_comp]
  rw [Category.assoc, hi, ← Category.assoc, scalarHomEquiv_source]

private lemma scalar_projection (K : SSet.{u}) (Z : SimplicialSpace.{u}) (m : ℕ)
    (a : SimplicialObject.matchingIndex m)
    (f : K ⟶ (boundaryCone m Z).pt) :
    scalarRepEquiv K Z a.obj.right.unop.len (f ≫ (boundaryCone m Z).π.app a) =
      boundarySimplexι a ≫ scalarHomEquiv K (SSet.boundary.{u} m : SSet.{u}) Z f := by
  change scalarHomEquiv K (Δ[a.obj.right.unop.len] : SSet.{u}) Z
    ((f ≫ (innerHomFunctor.map (boundaryFaceMap a).op).app Z ≫
      (repIso a.obj.right.unop.len Z).hom) ≫ (repIso a.obj.right.unop.len Z).inv) = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact scalarHomEquiv_source K (boundarySimplexι a) Z f

private abbrev faceIndex (n : ℕ) (i : Fin (n + 2)) :
    SimplicialObject.matchingIndex (n + 1) :=
  ⟨StructuredArrow.mk (SimplexCategory.δ i).op,
    ⟨by change Mono (SimplexCategory.δ i); infer_instance,
      by change n < n + 1; omega⟩⟩

private def indexHom {m : ℕ} (a b : SimplicialObject.matchingIndex m)
    (g : b.obj.right.unop ⟶ a.obj.right.unop)
    (hg : g ≫ a.obj.hom.unop = b.obj.hom.unop) : a ⟶ b :=
  ObjectProperty.homMk (StructuredArrow.homMk g.op (by
    apply Quiver.Hom.unop_inj
    exact hg))

private lemma boundarySimplexι_face (n : ℕ) (i : Fin (n + 2)) :
    boundarySimplexι.{u} (faceIndex n i) = SSet.boundary.ι.{u} i := by
  apply (cancel_mono (SSet.boundary.{u} (n + 1)).ι).1
  rw [boundarySimplexι_ι, SSet.boundary.ι_ι]
  rfl

private lemma delta_pair (n : ℕ) (i j : Fin (n + 3)) (hij : i < j) :
    SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)) ≫ SimplexCategory.δ j := by
  have h : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by
    simpa using hij
  simpa using (SimplexCategory.δ_comp_δ' h).symm

private abbrev pairIndex (n : ℕ) (i j : Fin (n + 3)) (hij : i < j) :
    SimplicialObject.matchingIndex (n + 2) :=
  ⟨StructuredArrow.mk
      (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i).op,
    ⟨by
      change Mono (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ SimplexCategory.δ i)
      infer_instance,
      by change n < n + 2; omega⟩⟩

private lemma scalarCone_sections (K : SSet.{u}) (Z : SimplicialSpace.{u}) (m : ℕ)
    (s : ∀ a : SimplicialObject.matchingIndex m, K ⟶ Z.diagram.obj a.obj.right)
    (hs : ∀ {a b : SimplicialObject.matchingIndex m} (g : a ⟶ b),
      s a ≫ Z.diagram.map g.hom.right = s b) :
    ∃! f : K ⟶ (boundaryCone m Z).pt,
      ∀ a, f ≫ (boundaryCone m Z).π.app a = s a := by
  cases m with
  | zero =>
      have h0 : IsInitial (SSet.boundary.{u} 0 : SSet.{u}) := by
        simpa only [SSet.boundary_zero] using
          (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u})))
      let f := (scalarHomEquiv K (SSet.boundary.{u} 0 : SSet.{u}) Z).symm (h0.to (V K Z))
      refine ⟨f, ?_, ?_⟩
      · intro a
        exact False.elim (Nat.not_lt_zero _ a.property.2)
      · intro g hg
        apply (scalarHomEquiv K (SSet.boundary.{u} 0 : SSet.{u}) Z).injective
        exact SSet.boundary.hom_ext₀
  | succ n =>
      let faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ V K Z) :=
        fun i => scalarRepEquiv K Z n (s (faceIndex n i))
      have hfaces : SSet.boundary.IsCompatible faces := by
        cases n with
        | zero => trivial
        | succ t =>
            intro i j hij
            let a := pairIndex t i j hij
            let gi : faceIndex (t + 1) i ⟶ a :=
              indexHom (faceIndex (t + 1) i) a
                (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) rfl
            let gj : faceIndex (t + 1) j ⟶ a :=
              indexHom (faceIndex (t + 1) j) a
                (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)))
                (delta_pair t i j hij).symm
            change SSet.stdSimplex.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))) ≫
                scalarRepEquiv K Z (t + 1) (s (faceIndex (t + 1) i)) =
              SSet.stdSimplex.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))) ≫
                scalarRepEquiv K Z (t + 1) (s (faceIndex (t + 1) j))
            rw [← scalarRepEquiv_index K Z (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))),
              ← scalarRepEquiv_index K Z (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij)))]
            exact congrArg (scalarRepEquiv K Z t) ((hs gi).trans (hs gj).symm)
      let g := hfaces.desc
      let f := (scalarHomEquiv K (SSet.boundary.{u} (n + 1) : SSet.{u}) Z).symm g
      have hproper (a : SimplicialObject.matchingIndex (n + 1)) :
          boundarySimplexι.{u} a ≫ g = scalarRepEquiv K Z a.obj.right.unop.len (s a) := by
        obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective
          a.obj.hom.unop (proper_not_surjective a)
        let q : faceIndex n i ⟶ a := indexHom (faceIndex n i) a θ hθ.symm
        have ha : boundarySimplexι.{u} a = SSet.stdSimplex.map θ ≫ SSet.boundary.ι i := by
          apply (cancel_mono (SSet.boundary.{u} (n + 1)).ι).1
          rw [boundarySimplexι_ι, Category.assoc, SSet.boundary.ι_ι]
          change SSet.stdSimplex.map a.obj.hom.unop =
            SSet.stdSimplex.map θ ≫ SSet.stdSimplex.map (SimplexCategory.δ i)
          rw [← SSet.stdSimplex.map_comp, ← hθ]
        rw [ha, Category.assoc, SSet.boundary.IsCompatible.ι_desc]
        change SSet.stdSimplex.map θ ≫ scalarRepEquiv K Z n (s (faceIndex n i)) = _
        rw [← scalarRepEquiv_index K Z θ]
        exact congrArg (scalarRepEquiv K Z a.obj.right.unop.len) (hs q)
      refine ⟨f, ?_, ?_⟩
      · intro a
        apply (scalarRepEquiv K Z a.obj.right.unop.len).injective
        rw [scalar_projection]
        change boundarySimplexι a ≫ scalarHomEquiv K (SSet.boundary.{u} (n + 1) : SSet.{u}) Z
          ((scalarHomEquiv K (SSet.boundary.{u} (n + 1) : SSet.{u}) Z).symm g) = _
        rw [Equiv.apply_symm_apply]
        exact hproper a
      · intro f' hf'
        apply (scalarHomEquiv K (SSet.boundary.{u} (n + 1) : SSet.{u}) Z).injective
        rw [Equiv.apply_symm_apply]
        apply SSet.boundary.hom_ext
        intro i
        calc
          SSet.boundary.ι i ≫ scalarHomEquiv K (SSet.boundary.{u} (n + 1) : SSet.{u}) Z f' =
              scalarRepEquiv K Z n (f' ≫ (boundaryCone (n + 1) Z).π.app (faceIndex n i)) := by
            rw [← boundarySimplexι_face]
            exact (scalar_projection K Z (n + 1) (faceIndex n i) f').symm
          _ = faces i := congrArg (scalarRepEquiv K Z n) (hf' (faceIndex n i))
          _ = SSet.boundary.ι i ≫ g := (SSet.boundary.IsCompatible.ι_desc hfaces i).symm

private def boundaryConeIsLimit (m : ℕ) (Z : SimplicialSpace.{u}) :
    IsLimit (boundaryCone m Z) :=
  coyonedaJointlyReflectsLimits _ _ (fun K => by
    apply Classical.choice
    rw [Types.isLimit_iff]
    intro s hs
    exact scalarCone_sections K.unop Z m s (fun g => hs g))

private def componentIso (m : ℕ) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.obj (op (B m))).obj Z ≅ SimplicialObject.matchingObject Z.diagram m :=
  (boundaryConeIsLimit m Z).conePointUniqueUpToIso
    (limit.isLimit (SimplicialObject.matchingDiagram Z.diagram m))

private lemma componentIso_π (m : ℕ) (Z : SimplicialSpace.{u})
    (a : SimplicialObject.matchingIndex m) :
    (componentIso m Z).hom ≫ SimplicialObject.matchingπ Z.diagram m a =
      (boundaryCone m Z).π.app a :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ a

/-- At a fixed degree, the actual inner boundary mapping functor is naturally
isomorphic to the original matching-object functor. -/
def boundaryMatchingIso (m : ℕ) :
    innerHomFunctor.obj
      (op (ofSimplicialObject.obj
        (SSet.simplicialSpaceDiscrete.obj (SSet.boundary.{u} m : SSet.{u})))) ≅
      forget ⋙ SimplicialObject.matchingObjectFunctor m :=
  NatIso.ofComponents (componentIso m) (by
    intro X Y p
    apply limit.hom_ext
    intro a
    change ((innerHomFunctor.obj (op (B m))).map p ≫ (componentIso m Y).hom) ≫
        SimplicialObject.matchingπ Y.diagram m a =
      ((componentIso m X).hom ≫ (SimplicialObject.matchingObjectFunctor m).map p.hom) ≫
        SimplicialObject.matchingπ Y.diagram m a
    rw [Category.assoc, componentIso_π]
    rw [Category.assoc, SimplicialObject.matchingObjectFunctor_map_π]
    rw [← Category.assoc, componentIso_π]
    change (innerHomFunctor.obj (op (B m))).map p ≫
        (innerHomFunctor.map (boundaryFaceMap a).op).app Y ≫ (repIso _ Y).hom =
      ((innerHomFunctor.map (boundaryFaceMap a).op).app X ≫ (repIso _ X).hom) ≫
          p.hom.app a.obj.right
    rw [← Category.assoc, (innerHomFunctor.map (boundaryFaceMap a).op).naturality p,
      Category.assoc, repIso_target, ← Category.assoc])

/-- Every original proper-face projection is retained by the fixed-degree isomorphism. -/
@[reassoc]
lemma boundaryMatchingIso_app_π (m : ℕ) (Z : SimplicialSpace.{u})
    (a : SimplicialObject.matchingIndex m) :
    ((boundaryMatchingIso.{u} m).app Z).hom ≫ SimplicialObject.matchingπ Z.diagram m a =
      (innerHomFunctor.map (boundaryFaceMap.{u} a).op).app Z ≫
        (SSet.Rezk.pointwiseYonedaIso a.obj.right.unop.len Z.diagram).hom :=
  componentIso_π m Z a

/-- Restriction along the same literal outer boundary inclusion is the original matching map. -/
@[reassoc]
lemma boundaryMatchingIso_boundary (m : ℕ) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.map (ReedyGeneratingFamilies.outerBoundaryMap.{u} m).op).app Z ≫
        ((boundaryMatchingIso.{u} m).app Z).hom =
      (SSet.Rezk.pointwiseYonedaIso m Z.diagram).hom ≫
        SimplicialObject.matchingMap Z.diagram m := by
  apply limit.hom_ext
  intro a
  change ((innerHomFunctor.map (ReedyGeneratingFamilies.outerBoundaryMap.{u} m).op).app Z ≫
      ((boundaryMatchingIso.{u} m).app Z).hom) ≫ SimplicialObject.matchingπ Z.diagram m a =
    ((SSet.Rezk.pointwiseYonedaIso m Z.diagram).hom ≫ SimplicialObject.matchingMap Z.diagram m) ≫
      SimplicialObject.matchingπ Z.diagram m a
  rw [Category.assoc, boundaryMatchingIso_app_π]
  rw [← Category.assoc, ← NatTrans.comp_app, ← innerHomFunctor.map_comp]
  rw [← op_comp, boundaryFaceMap_boundary]
  rw [Category.assoc, SimplicialObject.matchingMap_π]
  have hy := repIso_index a.obj.hom.unop Z
  simp only [Quiver.Hom.op_unop] at hy
  exact hy

end SimplicialSpace
