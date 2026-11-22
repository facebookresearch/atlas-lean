/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornCovers
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The original U-face colimit and zero-coface mapping span

The face index is the original proper-subset category. The tail meets edge01
at its original vertex one, and inner mapping uses the original target face d₀.
All data are constructed on the original objects, without a fibrancy condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SSet.Rezk.OuterHornCPresentation

/-- The literal intersection of the original U with an original indexed face. -/
def uFace (m : ℕ) (S : outerHornCFaceIndex m) : (Δ[m + 2] : SSet.{u}).Subcomplex :=
  outerHornCU m ⊓ stdSimplex.face S.val

/-- Every original U-face has its exact tail-without-zero/edge01 formula. -/
theorem uFace_eq (m : ℕ) (S : outerHornCFaceIndex m) :
    uFace.{u} m S = stdSimplex.face (S.val.erase 0) ⊔ stdSimplex.face {0, 1} :=
  outerHornCU_inf_face S

/-- The original intersection retains its original U inclusion. -/
theorem uFace_le_U (m : ℕ) (S : outerHornCFaceIndex m) : uFace.{u} m S ≤ outerHornCU m :=
  inf_le_left

/-- The original intersection retains its original ambient face inclusion. -/
theorem uFace_le_face (m : ℕ) (S : outerHornCFaceIndex m) :
    uFace.{u} m S ≤ stdSimplex.face S.val := inf_le_right

/-- Pairwise intersections use the same original face-index intersection. -/
theorem uFace_intersection (m : ℕ) (S T : outerHornCFaceIndex m) :
    uFace.{u} m S ⊓ uFace.{u} m T = uFace.{u} m (outerHornCFaceInf S T) := by
  simp only [uFace, ← outerHornCFace_intersection]
  exact inf_inf_inf_comm _ _ _ _ |>.trans (by rw [inf_idem])

/-- The full original U-face union is the literal original U. -/
theorem uFace_iSup (m : ℕ) :
    (⨆ S : outerHornCFaceIndex m, uFace.{u} m S) = outerHornCU m := by
  apply le_antisymm
  · exact iSup_le (fun S => uFace_le_U.{u} m S)
  · intro d a ha
    have hc : a ∈ (outerHornC (m + 2)).obj d := (outerHornCU_le_C m) d ha
    rw [← outerHornCFace_iSup.{u} m, Subfunctor.iSup_obj, Set.mem_iUnion] at hc
    obtain ⟨S, hS⟩ := hc
    change a ∈ (⨆ S : outerHornCFaceIndex m, uFace.{u} m S).obj d
    rw [Subfunctor.iSup_obj, Set.mem_iUnion]
    exact ⟨S, ha, hS⟩

/-- The original U-face diagram acts by the literal subset inclusions. -/
def uFaceDiagram (m : ℕ) : outerHornCFaceIndex m ⥤ SSet.{u} where
  obj S := uFace.{u} m S
  map f := Subcomplex.homOfLE (inf_le_inf_left (outerHornCU m)
    ((stdSimplex.face_le_face_iff _ _).mpr (leOfHom f)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every original diagram arrow retains its original ambient map. -/
@[reassoc (attr := simp)]
theorem uFaceDiagram_map_ι (m : ℕ) {S T : outerHornCFaceIndex m} (f : S ⟶ T) :
    (uFaceDiagram.{u} m).map f ≫ (uFace.{u} m T).ι = (uFace.{u} m S).ι := rfl

/-- The original diagram's supplied cocone has the original U as its point. -/
def uFaceCocone (m : ℕ) : Cocone (uFaceDiagram.{u} m) where
  pt := outerHornCU m
  ι :=
    { app := fun S => Subcomplex.homOfLE (uFace_le_U.{u} m S)
      naturality := fun {S T} f => by
        change (uFaceDiagram.{u} m).map f ≫ Subcomplex.homOfLE (uFace_le_U.{u} m T) =
          Subcomplex.homOfLE (uFace_le_U.{u} m S)
        rfl }

/-- The literal U-cover gives its native multicoequalizer data. -/
theorem uFaceCoverDiagram (m : ℕ) : Subcomplex.MulticoequalizerDiagram (outerHornCU.{u} m)
    (fun S : outerHornCFaceIndex m => uFace.{u} m S)
    (fun S T => uFace.{u} m (outerHornCFaceInf S T)) :=
  ⟨uFace_iSup.{u} m, fun S T => (uFace_intersection.{u} m S T).symm⟩

/-- All original compatible face maps glue to the actual original U colimit. -/
def uFaceColimit (m : ℕ) : IsColimit (uFaceCocone.{u} m) := by
  let h := uFaceCoverDiagram.{u} m
  let hc := h.isColimit
  let rel (c : Cocone (uFaceDiagram.{u} m))
      (p : outerHornCFaceIndex m × outerHornCFaceIndex m) :
      (h.multispanIndex.map Subcomplex.toSSetFunctor).fst p ≫ c.ι.app p.1 =
        (h.multispanIndex.map Subcomplex.toSSetFunctor).snd p ≫ c.ι.app p.2 := by
    change (uFaceDiagram.{u} m).map (homOfLE (outerHornCFaceInf_le_left p.1 p.2)) ≫ c.ι.app p.1 =
      (uFaceDiagram.{u} m).map (homOfLE (outerHornCFaceInf_le_right p.1 p.2)) ≫ c.ι.app p.2
    rw [c.w, c.w]
  let descend (c : Cocone (uFaceDiagram.{u} m)) : (outerHornCU m : SSet.{u}) ⟶ c.pt :=
    Multicofork.IsColimit.desc hc (fun S => c.ι.app S) (rel c)
  refine ⟨descend, ?_, ?_⟩
  · intro c S
    exact Multicofork.IsColimit.fac hc _ (rel c) S
  · intro c f hf
    apply Multicofork.IsColimit.hom_ext hc
    intro S
    exact (hf S).trans (Multicofork.IsColimit.fac hc _ (rel c) S).symm

/-- Descent of an ordinary original face family uses the constructed colimit. -/
def uFaceDesc (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S) : (outerHornCU m : SSet.{u}) ⟶ X :=
  (uFaceColimit.{u} m).desc
    { pt := X
      ι := { app := f, naturality := fun {S T} g => hf (S := S) (T := T) g } }

/-- Every original indexed piece keeps its prescribed ordinary family map. -/
@[simp, reassoc]
theorem uFaceDesc_fac (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S) (S : outerHornCFaceIndex m) :
    (uFaceCocone.{u} m).ι.app S ≫ uFaceDesc.{u} m f hf = f S := (uFaceColimit.{u} m).fac _ S

/-- The same original face factors determine every whole U map uniquely. -/
theorem uFaceDesc_unique (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S)
    (l : (outerHornCU m : SSet.{u}) ⟶ X)
    (hl : ∀ S, (uFaceCocone.{u} m).ι.app S ≫ l = f S) : l = uFaceDesc.{u} m f hf := by
  apply (uFaceColimit.{u} m).hom_ext
  intro S
  exact (hl S).trans (uFaceDesc_fac.{u} m f hf S).symm

/-- Ordinary U descent preserves every original simplex operator. -/
theorem uFaceDesc_operator (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (outerHornCU m : SSet.{u}).map α ≫ (uFaceDesc.{u} m f hf).app e =
      (uFaceDesc.{u} m f hf).app d ≫ X.map α := (uFaceDesc.{u} m f hf).naturality α

/-- The same supplied U cocone under the actual inner-discrete embedding. -/
def embeddedUFaceCocone (m : ℕ) : Cocone (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete) :=
  simplicialSpaceDiscrete.mapCocone (uFaceCocone.{u} m)

/-- The actual U cocone is colimiting after evaluation in both original degrees. -/
def embeddedUFaceColimit (m : ℕ) : IsColimit (embeddedUFaceCocone.{u} m) := by
  apply evaluationJointlyReflectsColimits
  intro d
  apply evaluationJointlyReflectsColimits
  intro e
  change IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj d).mapCocone (uFaceCocone.{u} m))
  exact isColimitOfPreserves _ (uFaceColimit.{u} m)

/-- The supplied U cocone on the actual designated simplicial-space carrier. -/
def wrappedUFaceCocone (m : ℕ) :
    Cocone (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject) :=
  SimplicialSpace.ofSimplicialObject.mapCocone (embeddedUFaceCocone.{u} m)

/-- The genuine carrier equivalence preserves the constructed U colimit. -/
def wrappedUFaceColimit (m : ℕ) : IsColimit (wrappedUFaceCocone.{u} m) :=
  isColimitOfPreserves _ (embeddedUFaceColimit.{u} m)

end SSet.Rezk.OuterHornCPresentation

namespace SSet.Rezk.OuterHornCPresentation

/-- The original sorted face map has the exact original two-interval U preimage. -/
theorem uFace_preimage (m : ℕ) (S : outerHornCFaceIndex m) :
    (uFace.{u} m S).preimage (outerHornCFaceMap S) =
      outerHornCIntervalCover (outerHornCFaceDim S) :=
  outerHornCU_intersection_preimage S

/-- Original U-face descent is compatible with arbitrary target postcomposition. -/
theorem uFaceDesc_postcomp (m : ℕ) {X Y : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S) (q : X ⟶ Y) :
    uFaceDesc.{u} m f hf ≫ q = uFaceDesc.{u} m (fun S => f S ≫ q)
      (fun {S T} g => by rw [← Category.assoc, hf (S := S) (T := T) g]) := by
  apply (uFaceColimit.{u} m).hom_ext
  intro S
  calc
    (uFaceCocone.{u} m).ι.app S ≫ (uFaceDesc.{u} m f hf ≫ q) =
        ((uFaceCocone.{u} m).ι.app S ≫ uFaceDesc.{u} m f hf) ≫ q := (Category.assoc _ _ _).symm
    _ = f S ≫ q := congrArg (fun h => h ≫ q) (uFaceDesc_fac.{u} m f hf S)
    _ = _ := (uFaceDesc_fac.{u} m (fun S => f S ≫ q)
      (fun {S T} g => by rw [← Category.assoc, hf (S := S) (T := T) g]) S).symm

/-- The ordinary original face factor holds at every original simplex value. -/
theorem uFaceDesc_app (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (uFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m).map g ≫ f T = f S) (S : outerHornCFaceIndex m)
    (d : SimplexCategoryᵒᵖ) (a : ((uFaceDiagram.{u} m).obj S).obj d) :
    (uFaceDesc.{u} m f hf).app d (((uFaceCocone.{u} m).ι.app S).app d a) = (f S).app d a :=
  congrArg (fun h => h.app d a) (uFaceDesc_fac.{u} m f hf S)

/-- Every original embedded compatible family descends through the actual supplied U colimit. -/
def embeddedUFaceDesc (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S) :
    simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u}) ⟶ X :=
  (embeddedUFaceColimit.{u} m).desc
    { pt := X, ι := { app := f, naturality := fun {S T} g => hf (S := S) (T := T) g } }

/-- The embedded descent retains every original face morphism. -/
@[simp, reassoc]
theorem embeddedUFaceDesc_fac (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) :
    (embeddedUFaceCocone.{u} m).ι.app S ≫ embeddedUFaceDesc.{u} m f hf = f S :=
  (embeddedUFaceColimit.{u} m).fac _ S

/-- Every original embedded face factor determines the descended map uniquely. -/
theorem embeddedUFaceDesc_unique (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (l : simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u}) ⟶ X)
    (hl : ∀ S, (embeddedUFaceCocone.{u} m).ι.app S ≫ l = f S) :
    l = embeddedUFaceDesc.{u} m f hf := by
  apply (embeddedUFaceColimit.{u} m).hom_ext
  intro S
  exact (hl S).trans (embeddedUFaceDesc_fac.{u} m f hf S).symm

/-- Every embedded original family factor retains its value in both original degrees. -/
theorem embeddedUFaceDesc_bidegree (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) (d e : SimplexCategoryᵒᵖ)
    (a : (((uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S).obj d).obj e) :
    ((embeddedUFaceDesc.{u} m f hf).app d).app e
        ((((embeddedUFaceCocone.{u} m).ι.app S).app d).app e a) = ((f S).app d).app e a :=
  congrArg (fun h => (h.app d).app e a) (embeddedUFaceDesc_fac.{u} m f hf S)

/-- The designated-carrier supplied colimit also gives every original compatible descent. -/
def wrappedUFaceDesc (m : ℕ) {X : SimplicialSpace.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).map g ≫
        f T = f S) :
    SimplicialSpace.ofSimplicialObject.obj
      (simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u})) ⟶ X :=
  (wrappedUFaceColimit.{u} m).desc
    { pt := X, ι := { app := f, naturality := fun {S T} g => hf (S := S) (T := T) g } }

/-- Every designated original piece retains its actual compatible-family map. -/
@[simp, reassoc]
theorem wrappedUFaceDesc_fac (m : ℕ) {X : SimplicialSpace.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).map g ≫
        f T = f S) (S : outerHornCFaceIndex m) :
    (wrappedUFaceCocone.{u} m).ι.app S ≫ wrappedUFaceDesc.{u} m f hf = f S :=
  (wrappedUFaceColimit.{u} m).fac _ S

/-- The original designated face factors determine the whole designated descent. -/
theorem wrappedUFaceDesc_unique (m : ℕ) {X : SimplicialSpace.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).map g ≫
        f T = f S)
    (l : SimplicialSpace.ofSimplicialObject.obj
      (simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u})) ⟶ X)
    (hl : ∀ S, (wrappedUFaceCocone.{u} m).ι.app S ≫ l = f S) : l = wrappedUFaceDesc.{u} m f hf := by
  apply (wrappedUFaceColimit.{u} m).hom_ext
  intro S
  exact (hl S).trans (wrappedUFaceDesc_fac.{u} m f hf S).symm

/-- The original U inclusion into the same original C. -/
def uToC (m : ℕ) : (outerHornCU m : SSet.{u}) ⟶ (outerHornC (m + 2) : SSet.{u}) :=
  Subcomplex.homOfLE (outerHornCU_le_C m)

@[reassoc (attr := simp)]
theorem uToC_ι (m : ℕ) : uToC.{u} m ≫ (outerHornC (m + 2)).ι = (outerHornCU m).ι := rfl

/-- The original zero-coface horn map lands in the literal original U. -/
def tailToU (m : ℕ) : (horn (m + 1) 0 : SSet.{u}) ⟶ (outerHornCU m : SSet.{u}) :=
  Subcomplex.lift ((horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3))) (by
    rw [← Subcomplex.image_eq_range]
    exact le_sup_left)

@[reassoc (attr := simp)]
theorem tailToU_ι (m : ℕ) : tailToU.{u} m ≫ (outerHornCU m).ι =
    (horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3)) := rfl

/-- The original ordered edge01 lands in the literal edge summand of U. -/
def edgeToU (m : ℕ) : (Δ[1] : SSet.{u}) ⟶ (outerHornCU m : SSet.{u}) :=
  (stdSimplex.facePairIso (0 : Fin (m + 3)) 1 (by change (0 : ℕ) < 1; omega)).hom ≫
    Subcomplex.homOfLE (show stdSimplex.face {0, 1} ≤ outerHornCU m from le_sup_right)

/-- The original tail retains the already constructed C-target map. -/
@[reassoc (attr := simp)]
theorem tailToU_uToC (m : ℕ) : tailToU.{u} m ≫ uToC.{u} m = outerHornCUTail m := by
  apply (cancel_mono (outerHornC (m + 2)).ι).mp
  simp only [Category.assoc, uToC_ι.{u}, tailToU_ι.{u}, outerHornCUTail_ι]

/-- The original edge retains the already constructed C-target map. -/
@[reassoc (attr := simp)]
theorem edgeToU_uToC (m : ℕ) : edgeToU.{u} m ≫ uToC.{u} m = outerHornCUEdge m := by
  simp only [edgeToU, uToC, Category.assoc, Subcomplex.homOfLE_comp, outerHornCUEdge]

/-- The original U-edge inclusion is the same increasing original edge01. -/
@[reassoc (attr := simp)]
theorem edgeToU_ι (m : ℕ) : edgeToU.{u} m ≫ (outerHornCU m).ι =
    SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (m + 2))) := by
  rw [← uToC_ι.{u} m, ← Category.assoc, edgeToU_uToC, outerHornCUEdge_ι]

private theorem singletonIso_hom_ι {n : ℕ} (i : Fin (n + 1)) :
    (stdSimplex.faceSingletonIso.{u} i).hom ≫ (stdSimplex.face {i}).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  change (Fin.orderIsoSingleton i ((stdSimplex.objEquiv a).toOrderHom j)).val = i
  rfl

/-- The original local vertex0 of the positive horn, including the horn H(1). -/
def tailVertex (m : ℕ) : (Δ[0] : SSet.{u}) ⟶ (horn (m + 1) 0 : SSet.{u}) :=
  (stdSimplex.faceSingletonIso (0 : Fin (m + 2))).hom ≫ Subcomplex.homOfLE (by
    apply le_trans ?_ (face_le_horn (⟨1, by omega⟩ : Fin (m + 2)) 0 (by
      intro h
      have hv := congrArg Fin.val h
      change 1 = 0 at hv
      omega))
    apply (stdSimplex.face_le_face_iff _ _).mpr
    simp only [Finset.singleton_subset_iff, Finset.mem_compl, Finset.mem_singleton]
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega)

/-- The local horn vertex retains its original constant-zero ambient map. -/
@[reassoc (attr := simp)]
theorem tailVertex_ι (m : ℕ) : tailVertex.{u} m ≫ (horn (m + 1) 0).ι =
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0) := by
  simp only [tailVertex, Category.assoc, Subcomplex.homOfLE_ι, singletonIso_hom_ι.{u}]

/-- The original ordered-edge overlap is its vertex-one map. -/
def edgeVertex : (Δ[0] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) := stdSimplex.δ (0 : Fin 2)

/-- The actual common overlap point in the original ambient simplex is vertex one. -/
def ambientVertex (m : ℕ) : (Δ[0] : SSet.{u}) ⟶ (Δ[m + 2] : SSet.{u}) :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 2⦌ 1)

/-- The zero-coface tail sends the original local zero to the original ambient one. -/
@[reassoc]
theorem tailVertex_tail_ι (m : ℕ) : tailVertex.{u} m ≫ tailToU.{u} m ≫ (outerHornCU m).ι =
    ambientVertex.{u} m := by
  rw [tailToU_ι.{u}, ← Category.assoc, tailVertex_ι.{u}]
  change SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 1⦌ 0) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (m + 3))) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋m + 2⦌ 1)
  rw [← SSet.stdSimplex.map_comp]
  congr 1

/-- The ordered edge's vertex one is the same original ambient vertex one. -/
@[reassoc]
theorem edgeVertex_edge_ι (m : ℕ) : edgeVertex.{u} ≫ edgeToU.{u} m ≫ (outerHornCU m).ι =
    ambientVertex.{u} m := by
  rw [edgeToU_ι.{u}]
  change SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) ≫
    SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (m + 2))) = _
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  exact SimplexCategory.Hom.ext_zero_left _ _

/-- The original tail/edge span has its exact whole-map common-vertex equation. -/
theorem tailEdge_condition (m : ℕ) : tailVertex.{u} m ≫ tailToU.{u} m = edgeVertex.{u} ≫
    edgeToU.{u} m := by
  apply (cancel_mono (outerHornCU m).ι).mp
  rw [Category.assoc, Category.assoc, tailVertex_tail_ι.{u}, edgeVertex_edge_ι.{u}]

end SSet.Rezk.OuterHornCPresentation

namespace SSet.Rezk.OuterHornCPresentation

/-- The original tail image in the original ambient simplex. -/
def tailImage (m : ℕ) : (Δ[m + 2] : SSet.{u}).Subcomplex :=
  (horn (m + 1) 0).image (stdSimplex.δ (0 : Fin (m + 3)))

/-- The original monic zero-coface/horn map gives its actual image isomorphism. -/
def tailImageIso (m : ℕ) : (horn (m + 1) 0 : SSet.{u}) ≅ (tailImage.{u} m : SSet.{u}) := by
  letI : Mono ((horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3))) := inferInstance
  exact asIso (Subcomplex.toRange ((horn (m + 1) 0).ι ≫
    stdSimplex.δ (0 : Fin (m + 3)))) ≪≫
      Subcomplex.eqToIso (Subcomplex.image_eq_range (horn (m + 1) 0)
        (stdSimplex.δ (0 : Fin (m + 3)))).symm

/-- The actual image isomorphism keeps the same original ambient composite. -/
@[reassoc (attr := simp)]
theorem tailImageIso_hom_ι (m : ℕ) : (tailImageIso.{u} m).hom ≫ (tailImage.{u} m).ι =
    (horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3)) := by
  simp only [tailImageIso, Iso.trans_hom, asIso_hom, Subcomplex.eqToIso]
  rw [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]

/-- The literal tail image intersects the ordered edge precisely at ambient vertex one. -/
theorem tailImage_edge_intersection (m : ℕ) :
    tailImage.{u} m ⊓ stdSimplex.face {0, 1} = stdSimplex.face {1} := by
  change (horn (m + 1) 0).image (stdSimplex.δ (0 : Fin (m + 3))) ⊓
    stdSimplex.face {0, 1} = _
  have he : stdSimplex.face {(0 : Fin (m + 3)), 1} ≤ outerHornC.{u} (m + 2) :=
    outerHornCFace_le_C (outerHornCFaceMin m)
  rw [outerHorn_image_cofaceZero, inf_right_comm]
  change (outerHornC (m + 2) ⊓ stdSimplex.face {(0 : Fin (m + 3)), 1}) ⊓
    stdSimplex.face {0}ᶜ = stdSimplex.face {1}
  rw [inf_eq_right.mpr he, stdSimplex.face_inter_face]
  have hset : ({(0 : Fin (m + 3)), 1} : Finset (Fin (m + 3))) ⊓ {0}ᶜ = {1} := by
    rw [Finset.inf_eq_inter]
    apply Finset.ext
    intro i
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl]
    constructor
    · rintro ⟨h0 | h1, hn⟩
      · exact (hn h0).elim
      · exact h1
    · intro h1
      refine ⟨Or.inr h1, ?_⟩
      intro h0
      have hv := congrArg Fin.val (h1.symm.trans h0)
      have hone : (1 : Fin (m + 3)).val = 1 := by
        change 1 % (m + 3) = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [hone] at hv
      change 1 = 0 at hv
      omega
  rw [hset]

/-- The literal subcomplex union/intersection square is the original U square. -/
theorem tailEdgeSubcomplexSquare (m : ℕ) :
    Subcomplex.BicartSq (stdSimplex.face {1}) (tailImage.{u} m)
      (stdSimplex.face {0, 1}) (outerHornCU m) :=
  ⟨rfl, tailImage_edge_intersection.{u} m⟩

/-- The original overlap singleton is represented by its actual original point. -/
def overlapIso (m : ℕ) : (Δ[0] : SSet.{u}) ≅ (stdSimplex.face {(1 : Fin (m + 3))} : SSet.{u}) :=
  stdSimplex.faceSingletonIso 1

/-- The original edge representation, before its U inclusion. -/
def edgeImageIso (m : ℕ) :
    (Δ[1] : SSet.{u}) ≅ (stdSimplex.face {(0 : Fin (m + 3)), 1} : SSet.{u}) :=
  stdSimplex.facePairIso 0 1 (by change (0 : ℕ) < 1; omega)

/-- The original span arrows form their constructed native pushout. -/
theorem tailEdge_isPushout (m : ℕ) :
    IsPushout (tailVertex.{u} m) edgeVertex.{u} (tailToU.{u} m) (edgeToU.{u} m) := by
  apply (tailEdgeSubcomplexSquare.{u} m).isPushout.of_iso'
    (overlapIso.{u} m) (tailImageIso.{u} m) (edgeImageIso.{u} m) (Iso.refl _)
  · apply (cancel_mono (tailImage.{u} m).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, overlapIso,
      singletonIso_hom_ι.{u}, tailImageIso_hom_ι.{u}]
    change ambientVertex.{u} m = tailVertex.{u} m ≫
      (horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3))
    rw [← tailToU_ι.{u}]
    exact (tailVertex_tail_ι.{u} m).symm
  · apply (cancel_mono (stdSimplex.face {(0 : Fin (m + 3)), 1}).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, overlapIso, singletonIso_hom_ι.{u}]
    change ambientVertex.{u} m = edgeVertex.{u} ≫ edgeToU.{u} m ≫ (outerHornCU m).ι
    exact (edgeVertex_edge_ι.{u} m).symm
  · apply (cancel_mono (outerHornCU m).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, tailImageIso_hom_ι.{u},
      tailToU_ι.{u}, Iso.refl_hom, Category.comp_id]
  · simp only [edgeToU, edgeImageIso, Iso.refl_hom, Category.comp_id]

/-- The original span cocone retains the actual two inclusion maps. -/
def tailEdgeCocone (m : ℕ) : PushoutCocone (tailVertex.{u} m) edgeVertex.{u} :=
  PushoutCocone.mk (tailToU.{u} m) (edgeToU.{u} m) (tailEdge_condition.{u} m)

/-- The actual original span cocone is supplied with its constructed colimit. -/
def tailEdgeColimit (m : ℕ) : IsColimit (tailEdgeCocone.{u} m) :=
  (tailEdge_isPushout.{u} m).isColimit

/-- The chosen pushout compares to the original U by its constructed native isomorphism. -/
def tailEdgePushoutIso (m : ℕ) : pushout (tailVertex.{u} m) edgeVertex.{u} ≅
    (outerHornCU m : SSet.{u}) :=
  (tailEdge_isPushout.{u} m).isoPushout.symm

/-- The chosen original tail leg has its actual forward factor. -/
@[reassoc (attr := simp)]
theorem tailEdgePushoutIso_inl (m : ℕ) :
    pushout.inl (tailVertex.{u} m) edgeVertex.{u} ≫ (tailEdgePushoutIso.{u} m).hom =
        tailToU.{u} m :=
  (tailEdge_isPushout.{u} m).inl_isoPushout_inv

/-- The chosen original edge leg has its actual forward factor. -/
@[reassoc (attr := simp)]
theorem tailEdgePushoutIso_inr (m : ℕ) :
    pushout.inr (tailVertex.{u} m) edgeVertex.{u} ≫ (tailEdgePushoutIso.{u} m).hom =
        edgeToU.{u} m :=
  (tailEdge_isPushout.{u} m).inr_isoPushout_inv

/-- The original tail has its actual inverse chosen-pushout factor. -/
@[reassoc (attr := simp)]
theorem tailEdgePushoutIso_inv_tail (m : ℕ) :
    tailToU.{u} m ≫ (tailEdgePushoutIso.{u} m).inv =
        pushout.inl (tailVertex.{u} m) edgeVertex.{u} :=
  (tailEdge_isPushout.{u} m).inl_isoPushout_hom

/-- The original edge has its actual inverse chosen-pushout factor. -/
@[reassoc (attr := simp)]
theorem tailEdgePushoutIso_inv_edge (m : ℕ) :
    edgeToU.{u} m ≫ (tailEdgePushoutIso.{u} m).inv =
        pushout.inr (tailVertex.{u} m) edgeVertex.{u} :=
  (tailEdge_isPushout.{u} m).inr_isoPushout_hom

/-- Every ordinary original pair of compatible span legs has its actual U descent. -/
def tailEdgeDesc (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) : (outerHornCU m : SSet.{u}) ⟶ X :=
  (tailEdgePushoutIso.{u} m).inv ≫ pushout.desc f g h

/-- The constructed U descent retains its prescribed original tail map. -/
@[reassoc (attr := simp)]
theorem tailEdgeDesc_tail (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) : tailToU.{u} m ≫
        tailEdgeDesc.{u} m f g h = f := by
  simp only [tailEdgeDesc, ← Category.assoc, tailEdgePushoutIso_inv_tail.{u}, pushout.inl_desc]

/-- The constructed U descent retains its prescribed original edge map. -/
@[reassoc (attr := simp)]
theorem tailEdgeDesc_edge (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) : edgeToU.{u} m ≫
        tailEdgeDesc.{u} m f g h = g := by
  simp only [tailEdgeDesc, ← Category.assoc, tailEdgePushoutIso_inv_edge.{u}, pushout.inr_desc]

/-- Both original compatible span factors determine every U descent uniquely. -/
theorem tailEdgeDesc_unique (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) (l : (outerHornCU m : SSet.{u}) ⟶ X)
    (hl : tailToU.{u} m ≫ l = f) (hr : edgeToU.{u} m ≫ l = g) : l = tailEdgeDesc.{u} m f g h := by
  apply (cancel_epi (tailEdgePushoutIso.{u} m).hom).mp
  apply pushout.hom_ext
  · simp only [← Category.assoc, tailEdgePushoutIso_inl.{u}, hl, tailEdgeDesc_tail.{u}]
  · simp only [← Category.assoc, tailEdgePushoutIso_inr.{u}, hr, tailEdgeDesc_edge.{u}]

end SSet.Rezk.OuterHornCPresentation

namespace SimplicialSpace.OuterHornCPresentation

open SSet.Rezk SSet.Rezk.OuterHornCPresentation

private theorem discreteEmbedding_preservesSpan :
    PreservesColimitsOfShape WalkingSpan
      (SSet.simplicialSpaceDiscrete.{u} ⋙ ofSimplicialObject) := by
  let _ : PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
    ⟨fun {K} => ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun d => ?_)
      change IsColimit
        ((((evaluation _ _).obj d ⋙ SimplicialObject.const (Type u)).mapCocone c))
      exact isColimitOfPreserves _ hc⟩⟩⟩
  infer_instance

/-- The actual original inner mapping functor, with its covariant opposite target. -/
def mappingOpposite (W : SimplicialSpace.{u}) : SSet.{u} ⥤ SSet.{u}ᵒᵖ :=
  (SSet.simplicialSpaceDiscrete ⋙ ofSimplicialObject) ⋙ (innerHomFunctor.flip.obj W).rightOp

private theorem mappingOpposite_preservesSpan (W : SimplicialSpace.{u}) :
    PreservesColimitsOfShape WalkingSpan (mappingOpposite W) := by
  let _ := discreteEmbedding_preservesSpan.{u}
  let _ := innerHom_rightOp_preservesColimitsOfShape WalkingSpan W
  change PreservesColimitsOfShape WalkingSpan
    ((SSet.simplicialSpaceDiscrete ⋙ ofSimplicialObject) ⋙ (innerHomFunctor.flip.obj W).rightOp)
  infer_instance

/-- The actual supplied original U span maps to its original inner mapping pullback. -/
theorem rawMapping_isPullback (W : SimplicialSpace.{u}) (m : ℕ) :
    IsPullback ((discreteSourceMapping W).map (tailToU.{u} m).op)
      ((discreteSourceMapping W).map (edgeToU.{u} m).op)
      ((discreteSourceMapping W).map (tailVertex.{u} m).op)
      ((discreteSourceMapping W).map edgeVertex.{u}.op) := by
  let _ := mappingOpposite_preservesSpan W
  have h := Functor.map_isPushout (mappingOpposite W) (tailEdge_isPushout.{u} m)
  exact h.unop.flip

/-- The original tail point map, normalized by the original degree-zero Yoneda isomorphism. -/
def tailBase (W : SimplicialSpace.{u}) (m : ℕ) :
    (discreteSourceMapping W).obj (op (SSet.horn (m + 1) 0 : SSet.{u})) ⟶
      W.diagram.obj (op ⦋0⦌) :=
  (discreteSourceMapping W).map (tailVertex.{u} m).op ≫ (discreteYonedaIso W 0).hom

/-- The original ordered edge's overlap is its actual target face d₀. -/
def edgeBase (W : SimplicialSpace.{u}) : W.diagram.obj (op ⦋1⦌) ⟶ W.diagram.obj (op ⦋0⦌) :=
  W.diagram.δ (0 : Fin 2)

/-- The original chosen tail mapping pullback uses the same two point maps. -/
def tailPullback (W : SimplicialSpace.{u}) (m : ℕ) : SSet.{u} :=
  pullback (tailBase W m) (edgeBase W)

/-- The original chosen pullback's tail projection. -/
def tailPullbackFst (W : SimplicialSpace.{u}) (m : ℕ) : tailPullback W m ⟶
    (discreteSourceMapping W).obj (op (SSet.horn (m + 1) 0 : SSet.{u})) :=
  pullback.fst (tailBase W m) (edgeBase W)

/-- The original chosen pullback's ordered-edge projection. -/
def tailPullbackSnd (W : SimplicialSpace.{u}) (m : ℕ) : tailPullback W m ⟶
    W.diagram.obj (op ⦋1⦌) := pullback.snd (tailBase W m) (edgeBase W)

/-- The two original chosen projections have their original target-base equation. -/
theorem tailPullback_condition (W : SimplicialSpace.{u}) (m : ℕ) :
    tailPullbackFst W m ≫ tailBase W m = tailPullbackSnd W m ≫ edgeBase W :=
  pullback.condition

/-- The original mapped U square has the exact Yoneda-normalized d₀ base. -/
theorem normalizedMapping_isPullback (W : SimplicialSpace.{u}) (m : ℕ) :
    IsPullback ((discreteSourceMapping W).map (tailToU.{u} m).op)
      ((discreteSourceMapping W).map (edgeToU.{u} m).op ≫ (discreteYonedaIso W 1).hom)
      (tailBase W m) (edgeBase W) := by
  apply (rawMapping_isPullback W m).of_iso (Iso.refl _) (Iso.refl _)
    (discreteYonedaIso W 1) (discreteYonedaIso W 0)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [tailBase, Iso.refl_hom, Category.id_comp]
  · exact discreteYonedaIso_naturality_index W (SimplexCategory.δ (0 : Fin 2))

/-- The actual U mapping object compares to its original chosen tail pullback. -/
def tailMappingIso (W : SimplicialSpace.{u}) (m : ℕ) :
    (discreteSourceMapping W).obj (op (outerHornCU m : SSet.{u})) ≅ tailPullback W m :=
  (normalizedMapping_isPullback W m).isoPullback

/-- The forward comparison retains the original tail restriction. -/
@[reassoc (attr := simp)]
theorem tailMappingIso_hom_fst (W : SimplicialSpace.{u}) (m : ℕ) :
    (tailMappingIso W m).hom ≫ tailPullbackFst W m =
      (discreteSourceMapping W).map (tailToU.{u} m).op :=
  (normalizedMapping_isPullback W m).isoPullback_hom_fst

/-- The forward comparison retains the original ordered-edge restriction. -/
@[reassoc (attr := simp)]
theorem tailMappingIso_hom_snd (W : SimplicialSpace.{u}) (m : ℕ) :
    (tailMappingIso W m).hom ≫ tailPullbackSnd W m =
      (discreteSourceMapping W).map (edgeToU.{u} m).op ≫ (discreteYonedaIso W 1).hom :=
  (normalizedMapping_isPullback W m).isoPullback_hom_snd

/-- The inverse comparison retains the original tail projection. -/
@[reassoc (attr := simp)]
theorem tailMappingIso_inv_tail (W : SimplicialSpace.{u}) (m : ℕ) :
    (tailMappingIso W m).inv ≫ (discreteSourceMapping W).map (tailToU.{u} m).op =
      tailPullbackFst W m := (normalizedMapping_isPullback W m).isoPullback_inv_fst

/-- The inverse comparison retains the original ordered-edge projection. -/
@[reassoc (attr := simp)]
theorem tailMappingIso_inv_edge (W : SimplicialSpace.{u}) (m : ℕ) :
    (tailMappingIso W m).inv ≫ (discreteSourceMapping W).map (edgeToU.{u} m).op ≫
        (discreteYonedaIso W 1).hom = tailPullbackSnd W m :=
  (normalizedMapping_isPullback W m).isoPullback_inv_snd

/-- Every original target arrow preserves the tail point map. -/
@[reassoc]
theorem tailBase_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    tailBase W m ≫ q.hom.app (op ⦋0⦌) =
      (discreteSourceMappingMap q).app (op (SSet.horn (m + 1) 0 : SSet.{u})) ≫ tailBase V m := by
  simp only [tailBase]
  rw [Category.assoc, ← discreteYonedaIso_naturality_target q 0,
    ← Category.assoc, (discreteSourceMappingMap q).naturality, Category.assoc]

/-- Every original target arrow preserves the original target face d₀. -/
@[reassoc]
theorem edgeBase_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) :
    edgeBase W ≫ q.hom.app (op ⦋0⦌) = q.hom.app (op ⦋1⦌) ≫ edgeBase V :=
  q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op

/-- The original chosen pullback moves by the original tail, edge and point maps. -/
def tailPullbackMap {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    tailPullback W m ⟶ tailPullback V m :=
  pullback.map (tailBase W m) (edgeBase W) (tailBase V m) (edgeBase V)
    ((discreteSourceMappingMap q).app (op (SSet.horn (m + 1) 0 : SSet.{u})))
    (q.hom.app (op ⦋1⦌)) (q.hom.app (op ⦋0⦌))
    (tailBase_natural q m) (edgeBase_natural q)

/-- The moving chosen tail projection keeps its original mapping target action. -/
@[reassoc (attr := simp)]
theorem tailPullbackMap_fst {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    tailPullbackMap q m ≫ tailPullbackFst V m =
      tailPullbackFst W m ≫
        (discreteSourceMappingMap q).app (op (SSet.horn (m + 1) 0 : SSet.{u})) :=
  pullback.lift_fst _ _ _

/-- The moving chosen edge projection keeps its original degree-one target action. -/
@[reassoc (attr := simp)]
theorem tailPullbackMap_snd {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    tailPullbackMap q m ≫ tailPullbackSnd V m =
      tailPullbackSnd W m ≫ q.hom.app (op ⦋1⦌) := pullback.lift_snd _ _ _

/-- The forward original U/pullback comparison is natural for every original target arrow. -/
@[reassoc]
theorem tailMappingIso_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    (discreteSourceMappingMap q).app (op (outerHornCU m : SSet.{u})) ≫
        (tailMappingIso V m).hom = (tailMappingIso W m).hom ≫ tailPullbackMap q m := by
  apply pullback.hom_ext (f := tailBase V m) (g := edgeBase V)
  · change ((discreteSourceMappingMap q).app (op (outerHornCU m : SSet.{u})) ≫
      (tailMappingIso V m).hom) ≫ tailPullbackFst V m =
      ((tailMappingIso W m).hom ≫ tailPullbackMap q m) ≫ tailPullbackFst V m
    simp only [Category.assoc, tailMappingIso_hom_fst, tailPullbackMap_fst,
      tailMappingIso_hom_fst_assoc]
    exact ((discreteSourceMappingMap q).naturality (tailToU.{u} m).op).symm
  · change ((discreteSourceMappingMap q).app (op (outerHornCU m : SSet.{u})) ≫
      (tailMappingIso V m).hom) ≫ tailPullbackSnd V m =
      ((tailMappingIso W m).hom ≫ tailPullbackMap q m) ≫ tailPullbackSnd V m
    simp only [Category.assoc, tailMappingIso_hom_snd, tailPullbackMap_snd,
      tailMappingIso_hom_snd_assoc]
    rw [← Category.assoc, ← (discreteSourceMappingMap q).naturality (edgeToU.{u} m).op,
      Category.assoc, discreteYonedaIso_naturality_target q 1]

/-- The inverse original U/pullback comparison retains the same original target naturality. -/
@[reassoc]
theorem tailMappingIso_inv_natural {W V : SimplicialSpace.{u}} (q : W ⟶ V) (m : ℕ) :
    (tailMappingIso W m).inv ≫ (discreteSourceMappingMap q).app (op (outerHornCU m : SSet.{u})) =
      tailPullbackMap q m ≫ (tailMappingIso V m).inv := by
  apply (cancel_mono (tailMappingIso V m).hom).mp
  rw [Category.assoc, tailMappingIso_natural, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SimplicialSpace.OuterHornCPresentation

namespace SSet.Rezk.OuterHornCPresentation

/-- At the first index the actual U-face is the original whole edge01. -/
theorem uFace_zero (S : outerHornCFaceIndex 0) : uFace.{u} 0 S = outerHornCU 0 := by
  change outerHornCU 0 ⊓ stdSimplex.face S.val = outerHornCU 0
  rw [outerHornCFaceIndex_zero S]
  rw [outerHornCU_zero]
  exact inf_eq_left.mpr (le_refl (stdSimplex.face.{u} {(0 : Fin 3), 1}))

/-- The original first U is represented by the same increasing edge01. -/
def uZeroEdgeIso : (Δ[1] : SSet.{u}) ≅ (outerHornCU 0 : SSet.{u}) :=
  stdSimplex.facePairIso.{u} (0 : Fin 3) 1 (by decide) ≪≫
    Subcomplex.eqToIso (outerHornCU_zero.{u}).symm

/-- The representation of U(2) retains the actual original edge map. -/
@[simp]
theorem uZeroEdgeIso_hom : uZeroEdgeIso.{u}.hom = edgeToU.{u} 0 := by
  simp only [uZeroEdgeIso, Iso.trans_hom, Subcomplex.eqToIso, edgeToU]

/-- Both original outer operators act naturally on the actual embedded descent. -/
theorem embeddedUFaceDesc_outer (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u})).map α ≫
        (embeddedUFaceDesc m f hf).app e = (embeddedUFaceDesc m f hf).app d ≫ X.map α :=
  (embeddedUFaceDesc m f hf).naturality α

/-- Both original inner operators act naturally on the same embedded descent. -/
theorem embeddedUFaceDesc_inner (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (d : SimplexCategoryᵒᵖ) {e k : SimplexCategoryᵒᵖ} (β : e ⟶ k) :
    ((simplicialSpaceDiscrete.obj (outerHornCU m : SSet.{u})).obj d).map β ≫
        ((embeddedUFaceDesc m f hf).app d).app k =
      ((embeddedUFaceDesc m f hf).app d).app e ≫ (X.obj d).map β :=
  ((embeddedUFaceDesc m f hf).app d).naturality β

/-- Every designated original factor also keeps its value in both original degrees. -/
theorem wrappedUFaceDesc_bidegree (m : ℕ) {X : SimplicialSpace.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (uFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete ⋙ SimplicialSpace.ofSimplicialObject).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (uFaceDiagram m ⋙ simplicialSpaceDiscrete ⋙
          SimplicialSpace.ofSimplicialObject).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) (d e : SimplexCategoryᵒᵖ)
    (a : (((uFaceDiagram m ⋙ simplicialSpaceDiscrete).obj S).obj d).obj e) :
    (((wrappedUFaceDesc m f hf).hom.app d).app e)
      (((((wrappedUFaceCocone m).ι.app S).hom.app d).app e) a) = ((f S).hom.app d).app e a :=
  congrArg (fun h => (h.hom.app d).app e a) (wrappedUFaceDesc_fac m f hf S)

/-- The original compatible span descent retains every original simplex operator. -/
theorem tailEdgeDesc_operator (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (outerHornCU m : SSet.{u}).map α ≫ (tailEdgeDesc m f g h).app e =
      (tailEdgeDesc m f g h).app d ≫ X.map α := (tailEdgeDesc m f g h).naturality α

/-- Every original compatible span descent retains its original tail simplex values. -/
theorem tailEdgeDesc_tail_app (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) (d : SimplexCategoryᵒᵖ)
    (a : (horn (m + 1) 0 : SSet.{u}).obj d) :
    (tailEdgeDesc m f g h).app d ((tailToU.{u} m).app d a) = f.app d a :=
  congrArg (fun l => l.app d a) (tailEdgeDesc_tail m f g h)

/-- Every original compatible span descent retains its original edge simplex values. -/
theorem tailEdgeDesc_edge_app (m : ℕ) {X : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) (d : SimplexCategoryᵒᵖ)
    (a : (Δ[1] : SSet.{u}).obj d) :
    (tailEdgeDesc m f g h).app d ((edgeToU.{u} m).app d a) = g.app d a :=
  congrArg (fun l => l.app d a) (tailEdgeDesc_edge m f g h)

/-- Both ordinary compatible span legs permit arbitrary original target postcomposition. -/
theorem tailEdgeDesc_postcomp (m : ℕ) {X Y : SSet.{u}}
    (f : (horn (m + 1) 0 : SSet.{u}) ⟶ X) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : tailVertex.{u} m ≫ f = edgeVertex.{u} ≫ g) (q : X ⟶ Y) :
    tailEdgeDesc m f g h ≫ q = tailEdgeDesc m (f ≫ q) (g ≫ q)
      (by rw [← Category.assoc, ← Category.assoc, h]) := by
  apply tailEdgeDesc_unique m (f ≫ q) (g ≫ q) _
  · rw [← Category.assoc, tailEdgeDesc_tail]
  · rw [← Category.assoc, tailEdgeDesc_edge]

end SSet.Rezk.OuterHornCPresentation

namespace SimplicialSpace.OuterHornCPresentation

open SSet.Rezk SSet.Rezk.OuterHornCPresentation

/-- The original U(2) mapping object has its actual represented-edge identification. -/
def uZeroMappingIso (W : SimplicialSpace.{u}) :
    (discreteSourceMapping W).obj (op (outerHornCU 0 : SSet.{u})) ≅ W.diagram.obj (op ⦋1⦌) :=
  asIso ((discreteSourceMapping W).map uZeroEdgeIso.{u}.hom.op) ≪≫ discreteYonedaIso W 1

/-- The represented-edge mapping comparison uses the same original U-edge inclusion. -/
@[simp, reassoc]
theorem uZeroMappingIso_hom (W : SimplicialSpace.{u}) :
    (uZeroMappingIso W).hom =
      (discreteSourceMapping W).map (edgeToU.{u} 0).op ≫ (discreteYonedaIso W 1).hom := by
  simp only [uZeroMappingIso, Iso.trans_hom, asIso_hom, uZeroEdgeIso_hom]

/-- The chosen first tail pullback has its actual original degree-one identification. -/
def tailPullbackZeroIso (W : SimplicialSpace.{u}) :
    tailPullback W 0 ≅ W.diagram.obj (op ⦋1⦌) :=
  (tailMappingIso W 0).symm ≪≫ uZeroMappingIso W

/-- The chosen degree-one identification is the actual original second projection. -/
@[simp]
theorem tailPullbackZeroIso_hom (W : SimplicialSpace.{u}) :
    (tailPullbackZeroIso W).hom = tailPullbackSnd W 0 := by
  simp only [tailPullbackZeroIso, Iso.trans_hom, Iso.symm_hom,
    uZeroMappingIso_hom, tailMappingIso_inv_edge]

/-- The inverse degree-one identification keeps the same original second projection. -/
@[reassoc (attr := simp)]
theorem tailPullbackZeroIso_inv_snd (W : SimplicialSpace.{u}) :
    (tailPullbackZeroIso W).inv ≫ tailPullbackSnd W 0 = 𝟙 (W.diagram.obj (op ⦋1⦌)) := by
  rw [← tailPullbackZeroIso_hom]
  exact (tailPullbackZeroIso W).inv_hom_id

/-- The first actual U/pullback comparison normalizes to the original W₁ identity. -/
theorem tailMappingIso_zero_normalization (W : SimplicialSpace.{u}) :
    (uZeroMappingIso W).inv ≫ (tailMappingIso W 0).hom ≫ (tailPullbackZeroIso W).hom =
      𝟙 (W.diagram.obj (op ⦋1⦌)) := by
  simp only [tailPullbackZeroIso, Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id]

/-- Every original scalar operator is retained by the forward comparison. -/
theorem tailMappingIso_hom_operator (W : SimplicialSpace.{u}) (m : ℕ)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    ((discreteSourceMapping W).obj (op (outerHornCU m : SSet.{u}))).map α ≫
        (tailMappingIso W m).hom.app e =
      (tailMappingIso W m).hom.app d ≫ (tailPullback W m).map α :=
  (tailMappingIso W m).hom.naturality α

/-- Every original scalar operator is retained by the inverse comparison. -/
theorem tailMappingIso_inv_operator (W : SimplicialSpace.{u}) (m : ℕ)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (tailPullback W m).map α ≫ (tailMappingIso W m).inv.app e =
      (tailMappingIso W m).inv.app d ≫
        ((discreteSourceMapping W).obj (op (outerHornCU m : SSet.{u}))).map α :=
  (tailMappingIso W m).inv.naturality α

end SimplicialSpace.OuterHornCPresentation
