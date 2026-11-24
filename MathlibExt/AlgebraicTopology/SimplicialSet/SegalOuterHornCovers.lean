/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SegalOuterHornDecomposition
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# The original auxiliary-face colimit and its interval intersections

The proper faces containing the original vertices zero and one form the
literal finite face diagram of C. Its colimit is constructed through all
original intersections. Increasing enumeration gives the original face
coordinates, and the zero-coface horn union intersects each face in the
actual two-interval cover.

Source: Rezk (2001), Section 11.11.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Rezk

/-- Original proper vertex subsets containing the distinct vertices zero and one. -/
abbrev outerHornCFaceIndex (m : ℕ) :=
  {S : Finset (Fin (m + 3)) // 0 ∈ S ∧ 1 ∈ S ∧ S ≠ Finset.univ}

/-- The original intersection remains in the same finite face index. -/
def outerHornCFaceInf {m : ℕ} (S T : outerHornCFaceIndex m) : outerHornCFaceIndex m :=
  ⟨S.val ∩ T.val, ⟨Finset.mem_inter.mpr ⟨S.property.1, T.property.1⟩,
    Finset.mem_inter.mpr ⟨S.property.2.1, T.property.2.1⟩, by
      intro h
      apply S.property.2.2
      apply Finset.eq_univ_of_forall
      intro j
      have hj : j ∈ S.val ∩ T.val :=
        (congrArg (fun U : Finset (Fin (m + 3)) => j ∈ U) h).mpr (Finset.mem_univ j)
      exact (Finset.mem_inter.mp hj).1⟩⟩

/-- The intersection retains its original left inclusion. -/
theorem outerHornCFaceInf_le_left {m : ℕ} (S T : outerHornCFaceIndex m) :
    outerHornCFaceInf S T ≤ S := Finset.inter_subset_left

/-- The intersection retains its original right inclusion. -/
theorem outerHornCFaceInf_le_right {m : ℕ} (S T : outerHornCFaceIndex m) :
    outerHornCFaceInf S T ≤ T := Finset.inter_subset_right

private theorem missing_vertex_ge_two {m : ℕ} (S : outerHornCFaceIndex m)
    (j : Fin (m + 3)) (hj : j ∉ S.val) : 2 ≤ j.val := by
  have h0 : j.val ≠ 0 := by
    intro h
    have e : j = 0 := Fin.ext h
    exact hj (e ▸ S.property.1)
  have h1 : j.val ≠ 1 := by
    intro h
    have e : j = 1 := Fin.ext h
    exact hj (e ▸ S.property.2.1)
  omega

/-- Every original face of this index is a face of the same auxiliary C. -/
theorem outerHornCFace_le_C {m : ℕ} (S : outerHornCFaceIndex m) :
    stdSimplex.face.{u} S.val ≤ outerHornC (m + 2) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin (m + 3), j ∉ S.val := by
    by_contra! h
    exact S.property.2.2 (Finset.eq_univ_of_forall h)
  intro d a ha
  change a ∈ (outerHornC (m + 2)).obj (op ⦋d.unop.len⦌)
  rw [mem_outerHornC_iff]
  refine ⟨j, missing_vertex_ge_two S j hj, ?_⟩
  rintro ⟨i, rfl⟩
  exact hj ((stdSimplex.mem_face_iff S.val a).mp ha i)

/-- The indexed faces have exactly the original auxiliary union, in all degrees. -/
theorem outerHornCFace_iSup (m : ℕ) :
    (⨆ S : outerHornCFaceIndex m, stdSimplex.face.{u} S.val) = outerHornC (m + 2) := by
  apply le_antisymm
  · exact iSup_le (fun S => outerHornCFace_le_C S)
  · intro d a ha
    let b : (Δ[m + 2] : SSet.{u}) _⦋d.unop.len⦌ := a
    change b ∈ (outerHornC (m + 2)).obj (op ⦋d.unop.len⦌) at ha
    change b ∈ (⨆ S : outerHornCFaceIndex m, stdSimplex.face.{u} S.val).obj
      (op ⦋d.unop.len⦌)
    obtain ⟨j, hj, hmissing⟩ := (mem_outerHornC_iff b).mp ha
    let S : Finset (Fin (m + 3)) :=
      Finset.image (fun i : Fin (d.unop.len + 1) => b i) Finset.univ ∪ {0, 1}
    have hnot : j ∉ S := by
      simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      rintro (⟨i, rfl⟩ | h | h)
      · exact hmissing ⟨i, rfl⟩
      · have hv := congrArg Fin.val h
        simp only [Fin.val_zero] at hv
        omega
      · have hv := congrArg Fin.val h
        change j.val = 1 at hv
        omega
    let s : outerHornCFaceIndex m := ⟨S, by simp [S], by simp [S], by
      intro h
      exact hnot (h ▸ Finset.mem_univ j)⟩
    rw [Subfunctor.iSup_obj, Set.mem_iUnion]
    refine ⟨s, ?_⟩
    rw [stdSimplex.mem_face_iff]
    intro i
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Every original face intersection is the same original indexed intersection. -/
theorem outerHornCFace_intersection {m : ℕ} (S T : outerHornCFaceIndex m) :
    stdSimplex.face.{u} S.val ⊓ stdSimplex.face T.val =
      stdSimplex.face (outerHornCFaceInf S T).val :=
  stdSimplex.face_inter_face _ _

/-- The actual finite diagram uses the literal original face inclusions. -/
def outerHornCFaceDiagram (m : ℕ) : outerHornCFaceIndex m ⥤ SSet.{u} where
  obj S := stdSimplex.face S.val
  map f := Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Its original cocone has the same auxiliary C as its point. -/
def outerHornCFaceCocone (m : ℕ) : Cocone (outerHornCFaceDiagram.{u} m) where
  pt := outerHornC (m + 2)
  ι :=
    { app := fun S => Subcomplex.homOfLE (outerHornCFace_le_C S)
      naturality := fun {S T} g => by
        change (outerHornCFaceDiagram m).map g ≫
          Subcomplex.homOfLE (outerHornCFace_le_C T) =
            Subcomplex.homOfLE (outerHornCFace_le_C S)
        rfl }

/-- The whole nonfiltered finite face-poset diagram has its original colimit. -/
def outerHornCFaceColimit (m : ℕ) :
    IsColimit (outerHornCFaceCocone.{u} m) := by
  let h : Subcomplex.MulticoequalizerDiagram (outerHornC.{u} (m + 2))
      (fun S : outerHornCFaceIndex m => stdSimplex.face S.val)
      (fun S T => stdSimplex.face (outerHornCFaceInf S T).val) :=
    ⟨outerHornCFace_iSup m, fun S T => (outerHornCFace_intersection S T).symm⟩
  let hc := h.isColimit
  let rel (c : Cocone (outerHornCFaceDiagram.{u} m))
      (p : outerHornCFaceIndex m × outerHornCFaceIndex m) :
      (h.multispanIndex.map Subcomplex.toSSetFunctor).fst p ≫ c.ι.app p.1 =
        (h.multispanIndex.map Subcomplex.toSSetFunctor).snd p ≫ c.ι.app p.2 := by
    change (outerHornCFaceDiagram m).map (homOfLE (outerHornCFaceInf_le_left p.1 p.2)) ≫
        c.ι.app p.1 =
      (outerHornCFaceDiagram m).map (homOfLE (outerHornCFaceInf_le_right p.1 p.2)) ≫
        c.ι.app p.2
    rw [c.w, c.w]
  let descend (c : Cocone (outerHornCFaceDiagram.{u} m)) :
      (outerHornC (m + 2) : SSet.{u}) ⟶ c.pt :=
    Multicofork.IsColimit.desc hc (fun S => c.ι.app S) (rel c)
  refine ⟨descend, ?_, ?_⟩
  · intro c S
    exact Multicofork.IsColimit.fac hc _ (rel c) S
  · intro c f hf
    apply Multicofork.IsColimit.hom_ext hc
    intro S
    exact (hf S).trans (Multicofork.IsColimit.fac hc _ (rel c) S).symm

/-- Descent of every original compatible family, with no colimit outcome input. -/
def outerHornCFaceDesc (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S) :
    (outerHornC (m + 2) : SSet.{u}) ⟶ X :=
  (outerHornCFaceColimit m).desc
    { pt := X
      ι :=
        { app := f
          naturality := fun {S T} g => by
            change (outerHornCFaceDiagram m).map g ≫ f T = f S
            exact hf g } }

/-- Every original face has its prescribed strict descent factor. -/
@[reassoc (attr := simp)]
theorem outerHornCFaceDesc_fac (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S) (S : outerHornCFaceIndex m) :
    Subcomplex.homOfLE (outerHornCFace_le_C S) ≫ outerHornCFaceDesc m f hf = f S :=
  (outerHornCFaceColimit m).fac _ S

/-- All original face factors determine the descended arrow uniquely. -/
theorem outerHornCFaceDesc_unique (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S)
    (l : (outerHornC (m + 2) : SSet.{u}) ⟶ X)
    (hl : ∀ S, Subcomplex.homOfLE (outerHornCFace_le_C S) ≫ l = f S) :
    l = outerHornCFaceDesc m f hf := by
  apply (outerHornCFaceColimit m).hom_ext
  intro S
  exact (hl S).trans (outerHornCFaceDesc_fac m f hf S).symm

/-- Descent retains original postcomposition on every supplied face. -/
theorem outerHornCFaceDesc_postcomp (m : ℕ) {X Y : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S) (t : X ⟶ Y) :
    outerHornCFaceDesc m (fun S => f S ≫ t)
      (fun g => (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ t) (hf g))) = outerHornCFaceDesc m f hf ≫ t := by
  apply (outerHornCFaceColimit m).hom_ext
  intro S
  change Subcomplex.homOfLE (outerHornCFace_le_C S) ≫ _ =
    Subcomplex.homOfLE (outerHornCFace_le_C S) ≫ _
  rw [outerHornCFaceDesc_fac, outerHornCFaceDesc_fac_assoc]
  rfl

/-- The local dimension is fixed by the original number of face vertices. -/
def outerHornCFaceDim {m : ℕ} (S : outerHornCFaceIndex m) : ℕ := S.val.card - 1

private theorem face_card_ge_two {m : ℕ} (S : outerHornCFaceIndex m) : 2 ≤ S.val.card := by
  have h01 : (0 : Fin (m + 3)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have hp : ({0, 1} : Finset (Fin (m + 3))) ⊆ S.val := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨S.property.1, S.property.2.1⟩
  have h := Finset.card_le_card hp
  simpa only [Finset.card_pair h01] using h

/-- Every represented face has a positive original local dimension. -/
theorem outerHornCFaceDim_pos {m : ℕ} (S : outerHornCFaceIndex m) :
    1 ≤ outerHornCFaceDim S := by
  have h := face_card_ge_two S
  dsimp [outerHornCFaceDim]
  omega

/-- The original cardinality is exactly the successor of the local dimension. -/
theorem outerHornCFace_card {m : ℕ} (S : outerHornCFaceIndex m) :
    S.val.card = outerHornCFaceDim S + 1 := by
  have h := face_card_ge_two S
  dsimp [outerHornCFaceDim]
  omega

/-- The proper face has local dimension strictly below the original ambient dimension. -/
theorem outerHornCFaceDim_lt {m : ℕ} (S : outerHornCFaceIndex m) :
    outerHornCFaceDim S < m + 2 := by
  have hs : S.val ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, S.property.2.2⟩
  have h := Finset.card_lt_card hs
  rw [Finset.card_univ, Fintype.card_fin] at h
  have he := outerHornCFace_card S
  omega

/-- Canonical increasing enumeration; the cardinality proof is constructed internally. -/
def outerHornCFaceOrderIso {m : ℕ} (S : outerHornCFaceIndex m) :
    Fin (outerHornCFaceDim S + 1) ≃o S.val :=
  S.val.orderIsoOfFin (outerHornCFace_card S)

/-- Every original increasing coordinate has its original sorted value. -/
theorem outerHornCFaceOrderIso_forward {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    (outerHornCFaceOrderIso S i).val = S.val.orderEmbOfFin (outerHornCFace_card S) i := rfl

/-- Inverse coordinates are the positions of the same original face elements. -/
theorem outerHornCFaceOrderIso_inverse {m : ℕ} (S : outerHornCFaceIndex m) (i : S.val) :
    ((outerHornCFaceOrderIso S).symm i).val = S.val.sort.idxOf i.val :=
  Finset.orderIsoOfFin_symm_apply _ _ _

/-- Increasing enumeration retains the original ambient vertex zero. -/
theorem outerHornCFaceOrderIso_zero {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCFaceOrderIso S 0).val = 0 := by
  have h := (outerHornCFaceOrderIso S).monotone
    (Fin.zero_le ((outerHornCFaceOrderIso S).symm ⟨0, S.property.1⟩))
  rw [OrderIso.apply_symm_apply] at h
  exact le_antisymm h (Fin.zero_le _)

private def faceOne {m : ℕ} (S : outerHornCFaceIndex m) : Fin (outerHornCFaceDim S + 1) :=
  ⟨1, by have h := outerHornCFaceDim_pos S; omega⟩

/-- The second increasing face coordinate is the original ambient vertex one. -/
theorem outerHornCFaceOrderIso_one {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCFaceOrderIso S ⟨1, by have h := outerHornCFaceDim_pos S; omega⟩).val = 1 := by
  let e := outerHornCFaceOrderIso S
  have hzero : e 0 = ⟨0, S.property.1⟩ := Subtype.ext (outerHornCFaceOrderIso_zero S)
  have hpositive : (0 : Fin (outerHornCFaceDim S + 1)) < e.symm ⟨1, S.property.2.1⟩ := by
    have h : (⟨0, S.property.1⟩ : S.val) < ⟨1, S.property.2.1⟩ := by
      change (0 : ℕ) < 1
      omega
    have hh := e.symm.strictMono h
    rw [← hzero, OrderIso.symm_apply_apply] at hh
    exact hh
  have hle : faceOne S ≤ e.symm ⟨1, S.property.2.1⟩ := by
    change 1 ≤ (e.symm ⟨1, S.property.2.1⟩).val
    exact hpositive
  have hupper := e.monotone hle
  rw [OrderIso.apply_symm_apply] at hupper
  have hlower := e.strictMono (show (0 : Fin (outerHornCFaceDim S + 1)) < faceOne S from by
    change 0 < 1
    omega)
  rw [hzero] at hlower
  exact le_antisymm hupper hlower

/-- The actual ordinal map given by the original increasing face enumeration. -/
def outerHornCFaceSimplex {m : ℕ} (S : outerHornCFaceIndex m) :
    ⦋outerHornCFaceDim S⦌ ⟶ ⦋m + 2⦌ :=
  SimplexCategory.mkHom (S.val.orderEmbOfFin (outerHornCFace_card S)).toOrderHom

/-- The same increasing enumeration as an original map of standard simplexes. -/
def outerHornCFaceMap {m : ℕ} (S : outerHornCFaceIndex m) :
    (Δ[outerHornCFaceDim S] : SSet.{u}) ⟶ Δ[m + 2] :=
  stdSimplex.map (outerHornCFaceSimplex S)

/-- Canonical face representation; no order isomorphism is supplied by a caller. -/
def outerHornCFaceIso {m : ℕ} (S : outerHornCFaceIndex m) :
    (Δ[outerHornCFaceDim S] : SSet.{u}) ≅ (stdSimplex.face S.val : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy _ _ (outerHornCFaceOrderIso S))

/-- The forward face representation retains its original ambient simplex map. -/
@[reassoc (attr := simp)]
theorem outerHornCFaceIso_hom_ι {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCFaceIso.{u} S).hom ≫ (stdSimplex.face S.val).ι = outerHornCFaceMap S := rfl

/-- Every original word coordinate has its same increasing face value, including repetitions. -/
theorem outerHornCFaceIso_hom_coord {m d : ℕ} (S : outerHornCFaceIndex m)
    (a : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((outerHornCFaceIso S).hom.app (op ⦋d⦌) a).val i =
      (outerHornCFaceOrderIso S (a i)).val := rfl

/-- Every inverse word coordinate is its original position in the same sorted face. -/
theorem outerHornCFaceIso_inv_coord {m d : ℕ} (S : outerHornCFaceIndex m)
    (a : (stdSimplex.face S.val : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (((outerHornCFaceIso S).inv.app (op ⦋d⦌) a) i).val = S.val.sort.idxOf (a.val i) := by
  change ((outerHornCFaceOrderIso S).symm
    ⟨a.val i, (stdSimplex.mem_face_iff S.val a.val).mp a.property i⟩).val = _
  exact outerHornCFaceOrderIso_inverse S _

/-- The forward coordinates retain every original simplex operator. -/
theorem outerHornCFaceIso_hom_operator {m : ℕ} (S : outerHornCFaceIndex m)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (Δ[outerHornCFaceDim S] : SSet.{u}).map α ≫ (outerHornCFaceIso S).hom.app e =
      (outerHornCFaceIso S).hom.app d ≫ (stdSimplex.face S.val : SSet.{u}).map α :=
  (outerHornCFaceIso S).hom.naturality α

/-- The inverse coordinates retain the other original operator square. -/
theorem outerHornCFaceIso_inv_operator {m : ℕ} (S : outerHornCFaceIndex m)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (stdSimplex.face S.val : SSet.{u}).map α ≫ (outerHornCFaceIso S).inv.app e =
      (outerHornCFaceIso S).inv.app d ≫ (Δ[outerHornCFaceDim S] : SSet.{u}).map α :=
  (outerHornCFaceIso S).inv.naturality α

/-- The original ordered comparison for every inclusion of original indexed faces. -/
def outerHornCFaceComparison {m : ℕ} (S T : outerHornCFaceIndex m) (h : S.val ⊆ T.val) :
    ⦋outerHornCFaceDim S⦌ ⟶ ⦋outerHornCFaceDim T⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i => (outerHornCFaceOrderIso T).symm
        ⟨(outerHornCFaceOrderIso S i).val, h (outerHornCFaceOrderIso S i).property⟩
      monotone' := fun _ _ hi => (outerHornCFaceOrderIso T).symm.monotone
        ((outerHornCFaceOrderIso S).monotone hi) }

/-- Original identity face inclusions keep the identity ordered comparison. -/
theorem outerHornCFaceComparison_id {m : ℕ} (S : outerHornCFaceIndex m) :
    outerHornCFaceComparison S S (Finset.Subset.refl _) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (outerHornCFaceOrderIso S).symm (outerHornCFaceOrderIso S i) = i
  exact OrderIso.symm_apply_apply _ _

/-- Every original pair of face inclusions retains its actual ordered composite. -/
theorem outerHornCFaceComparison_comp {m : ℕ} (S T V : outerHornCFaceIndex m)
    (h : S.val ⊆ T.val) (h' : T.val ⊆ V.val) :
    outerHornCFaceComparison S V (h.trans h') =
      outerHornCFaceComparison S T h ≫ outerHornCFaceComparison T V h' := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (outerHornCFaceOrderIso V).symm
      ⟨(outerHornCFaceOrderIso S i).val, h' (h (outerHornCFaceOrderIso S i).property)⟩ =
    (outerHornCFaceOrderIso V).symm
      ⟨(outerHornCFaceOrderIso T
        ((outerHornCFaceOrderIso T).symm
          ⟨(outerHornCFaceOrderIso S i).val, h (outerHornCFaceOrderIso S i).property⟩)).val, _⟩
  apply congrArg (outerHornCFaceOrderIso V).symm
  apply Subtype.ext
  let x : T.val :=
    ⟨(outerHornCFaceOrderIso S i).val, h (outerHornCFaceOrderIso S i).property⟩
  have hx := (outerHornCFaceOrderIso T).apply_symm_apply x
  exact (congrArg (fun a : T.val => a.val) hx).symm

/-- The ordered inclusion comparison retains the same original ambient enumeration. -/
theorem outerHornCFaceComparison_ambient {m : ℕ} (S T : outerHornCFaceIndex m)
    (h : S.val ⊆ T.val) :
    outerHornCFaceComparison S T h ≫ outerHornCFaceSimplex T = outerHornCFaceSimplex S := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (outerHornCFaceOrderIso T
    ((outerHornCFaceOrderIso T).symm
      ⟨(outerHornCFaceOrderIso S i).val, h (outerHornCFaceOrderIso S i).property⟩)).val =
        (outerHornCFaceOrderIso S i).val
  exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)

/-- Both original forward face maps commute for every face inclusion. -/
theorem outerHornCFaceIso_comparison_hom {m : ℕ} (S T : outerHornCFaceIndex m)
    (h : S.val ⊆ T.val) :
    (outerHornCFaceIso.{u} S).hom ≫
        Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr h) =
      stdSimplex.map (outerHornCFaceComparison S T h) ≫ (outerHornCFaceIso T).hom := by
  apply (cancel_mono (stdSimplex.face T.val).ι).mp
  calc
    ((outerHornCFaceIso S).hom ≫
        Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr h)) ≫
          (stdSimplex.face T.val).ι =
      (outerHornCFaceIso S).hom ≫ (stdSimplex.face S.val).ι := by rfl
    _ = outerHornCFaceMap S := outerHornCFaceIso_hom_ι S
    _ = stdSimplex.map (outerHornCFaceComparison S T h) ≫ outerHornCFaceMap T := by
      unfold outerHornCFaceMap
      rw [← stdSimplex.map_comp, outerHornCFaceComparison_ambient]
    _ = (stdSimplex.map (outerHornCFaceComparison S T h) ≫ (outerHornCFaceIso T).hom) ≫
      (stdSimplex.face T.val).ι := by rw [Category.assoc, outerHornCFaceIso_hom_ι]

/-- Every original face inclusion retains the inverse comparison square as well. -/
theorem outerHornCFaceIso_comparison_inv {m : ℕ} (S T : outerHornCFaceIndex m)
    (h : S.val ⊆ T.val) :
    Subcomplex.homOfLE ((stdSimplex.face_le_face_iff _ _).mpr h) ≫ (outerHornCFaceIso.{u} T).inv =
      (outerHornCFaceIso S).inv ≫ stdSimplex.map (outerHornCFaceComparison S T h) := by
  apply (cancel_mono (outerHornCFaceIso T).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ← outerHornCFaceIso_comparison_hom, Iso.inv_hom_id_assoc]

private theorem cofaceZero_apply {n d : ℕ} (a : (Δ[n] : SSet.{u}) _⦋d⦌)
    (i : Fin (d + 1)) :
    ((stdSimplex.δ (0 : Fin (n + 2))).app (op ⦋d⦌) a) i =
      (0 : Fin (n + 2)).succAbove (a i) := rfl

private theorem zero_succAbove_ge_two {n : ℕ} (i : Fin (n + 1)) :
    2 ≤ ((0 : Fin (n + 2)).succAbove i).val ↔ i ≠ 0 := by
  simp only [Fin.zero_succAbove, Fin.val_succ]
  constructor
  · intro h hi
    subst i
    simp at h
  · intro h
    have hi : i.val ≠ 0 := fun e => h (Fin.ext e)
    omega

/-- The original zero coface pulls C back to the original preceding outer horn. -/
theorem outerHornC_preimage_cofaceZero (n : ℕ) :
    (outerHornC.{u} (n + 1)).preimage (stdSimplex.δ (0 : Fin (n + 2))) = horn n 0 := by
  ext d a
  change (((stdSimplex.δ (0 : Fin (n + 2))).app (op ⦋d.unop.len⦌) a) ∈
      (outerHornC (n + 1)).obj (op ⦋d.unop.len⦌)) ↔
    a ∈ (horn n 0).obj (op ⦋d.unop.len⦌)
  rw [mem_outerHornC_iff, mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, ha⟩
    have hj0 : j ≠ 0 := fun h => by subst j; simp at hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj0
    refine ⟨i, (zero_succAbove_ge_two i).mp (hi ▸ hj), ?_⟩
    rintro ⟨b, hb⟩
    apply ha
    refine ⟨b, ?_⟩
    rw [cofaceZero_apply, hb]
    exact hi
  · rintro ⟨i, hi, ha⟩
    refine ⟨(0 : Fin (n + 2)).succAbove i, (zero_succAbove_ge_two i).mpr hi, ?_⟩
    rintro ⟨b, hb⟩
    apply ha
    refine ⟨b, ?_⟩
    rw [cofaceZero_apply] at hb
    exact Fin.succAbove_right_injective hb

/-- The zero-coface horn image is the literal auxiliary/zero-face intersection. -/
theorem outerHorn_image_cofaceZero (n : ℕ) :
    (horn.{u} n 0).image (stdSimplex.δ (0 : Fin (n + 2))) =
      outerHornC (n + 1) ⊓ stdSimplex.face {(0 : Fin (n + 2))}ᶜ := by
  apply le_antisymm
  · exact le_inf
      (by rw [Subcomplex.image_le_iff, outerHornC_preimage_cofaceZero])
      (by simpa only [stdSimplex.range_δ] using
        (horn.{u} n 0).image_le_range (stdSimplex.δ (0 : Fin (n + 2))))
  · intro d a ha
    have hr : a ∈ (Subcomplex.range (stdSimplex.δ (0 : Fin (n + 2)))).obj d := by
      rw [stdSimplex.range_δ]
      exact ha.2
    obtain ⟨b, hb⟩ := hr
    have hc : b ∈ ((outerHornC (n + 1)).preimage
        (stdSimplex.δ (0 : Fin (n + 2)))).obj d := by
      change (stdSimplex.δ (0 : Fin (n + 2))).app d b ∈ (outerHornC (n + 1)).obj d
      simpa only [hb] using ha.1
    rw [outerHornC_preimage_cofaceZero] at hc
    exact ⟨b, hc, hb⟩

/-- The original minimal proper indexed face is the edge on zero and one. -/
def outerHornCFaceMin (m : ℕ) : outerHornCFaceIndex m :=
  ⟨{0, 1}, by simp, by simp, by
    intro h
    let j : Fin (m + 3) := ⟨2, by omega⟩
    have hj : j ∈ ({0, 1} : Finset (Fin (m + 3))) :=
      (congrArg (fun S : Finset (Fin (m + 3)) => j ∈ S) h).mpr (Finset.mem_univ j)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with h0 | h1
    · have hv := congrArg Fin.val h0
      change 2 = 0 at hv
      omega
    · have hv := congrArg Fin.val h1
      change 2 = 1 at hv
      omega⟩

/-- The original zero-coface horn union and the original edge01. -/
def outerHornCU (m : ℕ) : (Δ[m + 2] : SSet.{u}).Subcomplex :=
  (horn (m + 1) 0).image (stdSimplex.δ (0 : Fin (m + 3))) ⊔ stdSimplex.face {0, 1}

/-- Both original parts of U lie in the same auxiliary C. -/
theorem outerHornCU_le_C (m : ℕ) : outerHornCU.{u} m ≤ outerHornC (m + 2) := by
  unfold outerHornCU
  rw [outerHorn_image_cofaceZero]
  exact sup_le inf_le_left (outerHornCFace_le_C (outerHornCFaceMin m))

/-- The original tail map into C is the same zero-coface/horn composite. -/
def outerHornCUTail (m : ℕ) : (horn (m + 1) 0 : SSet.{u}) ⟶ (outerHornC (m + 2) : SSet.{u}) :=
  Subcomplex.lift ((horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3))) (by
    rw [← Subcomplex.image_eq_range, outerHorn_image_cofaceZero]
    exact inf_le_left)

/-- The tail retains its original zero-coface factor equation. -/
@[reassoc (attr := simp)]
theorem outerHornCUTail_ι (m : ℕ) :
    outerHornCUTail.{u} m ≫ (outerHornC (m + 2)).ι =
      (horn (m + 1) 0).ι ≫ stdSimplex.δ (0 : Fin (m + 3)) := rfl

/-- The original edge01 enters C by its native ordered-pair representation. -/
def outerHornCUEdge (m : ℕ) : (Δ[1] : SSet.{u}) ⟶ (outerHornC (m + 2) : SSet.{u}) :=
  (stdSimplex.facePairIso (0 : Fin (m + 3)) 1 (by change (0 : ℕ) < 1; omega)).hom ≫
    Subcomplex.homOfLE (outerHornCFace_le_C (outerHornCFaceMin m))

/-- The edge enters along the same original increasing edge01 map. -/
@[reassoc (attr := simp)]
theorem outerHornCUEdge_ι (m : ℕ) :
    outerHornCUEdge.{u} m ≫ (outerHornC (m + 2)).ι =
      stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (m + 2))) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  change (Fin.orderIsoPair (0 : Fin (m + 3)) 1 (by change (0 : ℕ) < 1; omega)
      ((stdSimplex.objEquiv a).toOrderHom i)).val =
    (SimplexCategory.mkOfSucc (0 : Fin (m + 2))).toOrderHom
      ((stdSimplex.objEquiv a).toOrderHom i)
  generalize h : (stdSimplex.objEquiv a).toOrderHom i = j
  fin_cases j <;> rfl

/-- The exact U intersection with every original proper face, in both directions. -/
theorem outerHornCU_inf_face {m : ℕ} (S : outerHornCFaceIndex m) :
    outerHornCU.{u} m ⊓ stdSimplex.face S.val =
      stdSimplex.face (S.val.erase 0) ⊔ stdSimplex.face {0, 1} := by
  have hS := outerHornCFace_le_C.{u} S
  have hpair : ({0, 1} : Finset (Fin (m + 3))) ⊆ S.val := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨S.property.1, S.property.2.1⟩
  have he : stdSimplex.face.{u} {0, 1} ≤ stdSimplex.face S.val :=
    (stdSimplex.face_le_face_iff _ _).mpr hpair
  have hErase : S.val ⊓ {(0 : Fin (m + 3))}ᶜ = S.val.erase 0 := by
    ext i
    simp [and_comm]
  have hface : stdSimplex.face.{u} S.val ⊓ stdSimplex.face {(0 : Fin (m + 3))}ᶜ =
      stdSimplex.face (S.val.erase 0) := by
    rw [stdSimplex.face_inter_face, hErase]
  rw [outerHornCU, outerHorn_image_cofaceZero, ← hface]
  ext d a
  change (((a ∈ (outerHornC (m + 2)).obj d ∧
    a ∈ (stdSimplex.face {(0 : Fin (m + 3))}ᶜ).obj d) ∨
      a ∈ (stdSimplex.face {0, 1}).obj d) ∧ a ∈ (stdSimplex.face S.val).obj d) ↔
    (a ∈ (stdSimplex.face S.val).obj d ∧
      a ∈ (stdSimplex.face {(0 : Fin (m + 3))}ᶜ).obj d) ∨
        a ∈ (stdSimplex.face {0, 1}).obj d
  constructor
  · rintro ⟨(⟨_, hz⟩ | hEdge), hs⟩
    · exact Or.inl ⟨hs, hz⟩
    · exact Or.inr hEdge
  · rintro (⟨hs, hz⟩ | hEdge)
    · exact ⟨Or.inl ⟨hS d hs, hz⟩, hs⟩
    · exact ⟨Or.inr hEdge, he d hEdge⟩

/-- The exact two original interval blocks, without a locality premise. -/
def outerHornCIntervalCover (ell : ℕ) : (Δ[ell] : SSet.{u}).Subcomplex :=
  stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ⊔
    stdSimplex.face (Finset.Icc 0 1)

/-- The two original interval faces meet at the original vertex one. -/
theorem outerHornCInterval_intersection (ell : ℕ) (hell : 1 ≤ ell) :
    stdSimplex.face.{u} (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ⊓
        stdSimplex.face (Finset.Icc 0 1) = stdSimplex.face {1} := by
  rw [stdSimplex.face_inter_face]
  apply congrArg (fun S : Finset (Fin (ell + 1)) => stdSimplex.face.{u} S)
  apply Finset.ext
  intro i
  rw [Finset.inf_eq_inter]
  simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, _⟩, _, h2⟩
    exact le_antisymm h2 h1
  · intro h
    subst i
    have hv : (1 : Fin (ell + 1)).val = 1 := by
      change 1 % (ell + 1) = 1
      exact Nat.mod_eq_of_lt (by omega)
    have hlast : (1 : Fin (ell + 1)) ≤ Fin.last ell := by
      change (1 : Fin (ell + 1)).val ≤ ell
      rw [hv]
      exact hell
    exact ⟨⟨le_rfl, hlast⟩, Fin.zero_le _, le_rfl⟩

/-- The original two-face union is its genuine vertex-one pushout. -/
theorem outerHornCInterval_isPushout (ell : ℕ) (hell : 1 ≤ ell) :
    IsPushout
      (Subcomplex.homOfLE (show stdSimplex.face.{u} {1} ≤
        stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) from by
          rw [← outerHornCInterval_intersection ell hell]; exact inf_le_left))
      (Subcomplex.homOfLE (show stdSimplex.face.{u} {1} ≤
        stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) from by
          rw [← outerHornCInterval_intersection ell hell]; exact inf_le_right))
      (Subcomplex.homOfLE (le_sup_left : stdSimplex.face.{u}
        (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ≤ outerHornCIntervalCover ell))
      (Subcomplex.homOfLE (le_sup_right : stdSimplex.face.{u}
        (Finset.Icc (0 : Fin (ell + 1)) 1) ≤ outerHornCIntervalCover ell)) :=
  (show Subcomplex.BicartSq (stdSimplex.face.{u} {1})
    (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)))
    (stdSimplex.face (Finset.Icc 0 1)) (outerHornCIntervalCover ell) from
      ⟨rfl, outerHornCInterval_intersection ell hell⟩).isPushout

/-- At local dimension one the two original interval blocks give the whole original edge. -/
@[simp]
theorem outerHornCIntervalCover_one : outerHornCIntervalCover.{u} 1 = ⊤ := by
  have he : (Finset.Icc (0 : Fin 2) 1) = Finset.univ := by
    ext i
    fin_cases i <;> simp
  rw [outerHornCIntervalCover, he, stdSimplex.face_univ, sup_top_eq]

private theorem face_index_one_val {m : ℕ} (S : outerHornCFaceIndex m) :
    (1 : Fin (outerHornCFaceDim S + 1)).val = 1 := by
  change 1 % (outerHornCFaceDim S + 1) = 1
  exact Nat.mod_eq_of_lt (by have h := outerHornCFaceDim_pos S; omega)

private theorem face_enum_one {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCFaceOrderIso S (1 : Fin (outerHornCFaceDim S + 1))).val = 1 := by
  have h : (1 : Fin (outerHornCFaceDim S + 1)) = faceOne S :=
    Fin.ext (face_index_one_val S)
  rw [h]
  exact outerHornCFaceOrderIso_one S

private theorem face_enum_zero_iff {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    (outerHornCFaceOrderIso S i).val = 0 ↔ i = 0 := by
  constructor
  · intro h
    apply (outerHornCFaceOrderIso S).injective
    apply Subtype.ext
    exact h.trans (outerHornCFaceOrderIso_zero S).symm
  · rintro rfl
    exact outerHornCFaceOrderIso_zero S

private theorem face_enum_one_iff {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    (outerHornCFaceOrderIso S i).val = 1 ↔ i = 1 := by
  constructor
  · intro h
    apply (outerHornCFaceOrderIso S).injective
    apply Subtype.ext
    exact h.trans (face_enum_one S).symm
  · rintro rfl
    exact face_enum_one S

private theorem face_index_mem_tail {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    i ∈ Finset.Icc (1 : Fin (outerHornCFaceDim S + 1)) (Fin.last _) ↔ i ≠ 0 := by
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hi, _⟩ h
    subst i
    have h1 := face_index_one_val S
    change (1 : Fin (outerHornCFaceDim S + 1)).val ≤ 0 at hi
    omega
  · intro h
    refine ⟨?_, Fin.le_last _⟩
    have hi : i.val ≠ 0 := fun he => h (Fin.ext he)
    have h1 := face_index_one_val S
    change (1 : Fin (outerHornCFaceDim S + 1)).val ≤ i.val
    omega

private theorem face_index_mem_edge {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    i ∈ Finset.Icc (0 : Fin (outerHornCFaceDim S + 1)) 1 ↔ i = 0 ∨ i = 1 := by
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨_, hi⟩
    have h1 := face_index_one_val S
    change i.val ≤ (1 : Fin (outerHornCFaceDim S + 1)).val at hi
    have he : i.val = 0 ∨ i.val = 1 := by omega
    rcases he with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext (he.trans h1.symm))
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Fin.zero_le _⟩
    · exact ⟨Fin.zero_le _, le_rfl⟩

private theorem face_enum_mem_erase {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    (outerHornCFaceOrderIso S i).val ∈ S.val.erase 0 ↔
      i ∈ Finset.Icc (1 : Fin (outerHornCFaceDim S + 1)) (Fin.last _) := by
  rw [Finset.mem_erase, face_index_mem_tail]
  have hi := (outerHornCFaceOrderIso S i).property
  exact (and_iff_left hi).trans (not_congr (face_enum_zero_iff S i))

private theorem face_enum_mem_pair {m : ℕ} (S : outerHornCFaceIndex m)
    (i : Fin (outerHornCFaceDim S + 1)) :
    (outerHornCFaceOrderIso S i).val ∈ ({0, 1} : Finset (Fin (m + 3))) ↔
      i ∈ Finset.Icc (0 : Fin (outerHornCFaceDim S + 1)) 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, face_enum_zero_iff,
    face_enum_one_iff, face_index_mem_edge]

/-- Every coordinate of the original ambient face map retains the same sorted value. -/
theorem outerHornCFaceMap_coord {m d : ℕ} (S : outerHornCFaceIndex m)
    (a : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((outerHornCFaceMap S).app (op ⦋d⦌) a) i =
      (outerHornCFaceOrderIso S (a i)).val := rfl

/-- The original sorted map pulls U back to exactly the two stated original interval blocks. -/
theorem outerHornCU_preimage_face {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCU.{u} m).preimage (outerHornCFaceMap S) =
      outerHornCIntervalCover (outerHornCFaceDim S) := by
  ext d a
  let b : (Δ[outerHornCFaceDim S] : SSet.{u}) _⦋d.unop.len⦌ := a
  let q := (outerHornCFaceMap S).app (op ⦋d.unop.len⦌) b
  have hq : q ∈ (stdSimplex.face S.val).obj (op ⦋d.unop.len⦌) :=
    ((outerHornCFaceIso S).hom.app (op ⦋d.unop.len⦌) b).property
  have hmem : q ∈ (outerHornCU m).obj (op ⦋d.unop.len⦌) ↔
      q ∈ (outerHornCU m ⊓ stdSimplex.face S.val).obj (op ⦋d.unop.len⦌) :=
    ⟨fun h => ⟨h, hq⟩, fun h => h.1⟩
  change q ∈ (outerHornCU m).obj (op ⦋d.unop.len⦌) ↔
    b ∈ (outerHornCIntervalCover (outerHornCFaceDim S)).obj (op ⦋d.unop.len⦌)
  rw [hmem, outerHornCU_inf_face, outerHornCIntervalCover]
  simp only [Subfunctor.max_obj, Set.mem_union]
  rw [stdSimplex.mem_face_iff, stdSimplex.mem_face_iff,
    stdSimplex.mem_face_iff, stdSimplex.mem_face_iff]
  simp only [q, outerHornCFaceMap_coord]
  simp_rw [face_enum_mem_erase, face_enum_mem_pair]

/-- The same map pulls the literal U/face intersection back to the same interval cover. -/
theorem outerHornCU_intersection_preimage {m : ℕ} (S : outerHornCFaceIndex m) :
    (outerHornCU.{u} m ⊓ stdSimplex.face S.val).preimage (outerHornCFaceMap S) =
      outerHornCIntervalCover (outerHornCFaceDim S) := by
  rw [Subcomplex.preimage_min, outerHornCU_preimage_face]
  have hface : (stdSimplex.face.{u} S.val).preimage (outerHornCFaceMap S) = ⊤ := by
    ext d a
    change (outerHornCFaceMap S).app d a ∈ (stdSimplex.face S.val).obj d ↔ True
    exact ⟨fun _ => trivial, fun _ => ((outerHornCFaceIso S).hom.app d a).property⟩
  rw [hface, inf_top_eq]

/-- The original vertex-one leg into the local tail interval. -/
theorem outerHornCInterval_vertex_le_tail (ell : ℕ) (hell : 1 ≤ ell) :
    stdSimplex.face.{u} {1} ≤
      stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) := by
  rw [← outerHornCInterval_intersection ell hell]
  exact inf_le_left

/-- The other original vertex-one leg into the local edge interval. -/
theorem outerHornCInterval_vertex_le_edge (ell : ℕ) (hell : 1 ≤ ell) :
    stdSimplex.face.{u} {1} ≤ stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) := by
  rw [← outerHornCInterval_intersection ell hell]
  exact inf_le_right

/-- Descent of the original compatible interval legs, with no pushout premise. -/
def outerHornCIntervalDesc (ell : ℕ) (hell : 1 ≤ ell) {X : SSet.{u}}
    (f : (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) : SSet.{u}) ⟶ X)
    (g : (stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) : SSet.{u}) ⟶ X)
    (h : Subcomplex.homOfLE (outerHornCInterval_vertex_le_tail ell hell) ≫ f =
      Subcomplex.homOfLE (outerHornCInterval_vertex_le_edge ell hell) ≫ g) :
    (outerHornCIntervalCover ell : SSet.{u}) ⟶ X :=
  (outerHornCInterval_isPushout ell hell).desc f g h

/-- The original tail interval has its prescribed strict descent factor. -/
@[reassoc]
theorem outerHornCIntervalDesc_tail (ell : ℕ) (hell : 1 ≤ ell) {X : SSet.{u}}
    (f : (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) : SSet.{u}) ⟶ X)
    (g : (stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) : SSet.{u}) ⟶ X)
    (h : Subcomplex.homOfLE (outerHornCInterval_vertex_le_tail ell hell) ≫ f =
      Subcomplex.homOfLE (outerHornCInterval_vertex_le_edge ell hell) ≫ g) :
    Subcomplex.homOfLE (le_sup_left : stdSimplex.face.{u}
        (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ≤ outerHornCIntervalCover ell) ≫
      outerHornCIntervalDesc ell hell f g h = f :=
  (outerHornCInterval_isPushout ell hell).inl_desc f g h

/-- The original edge interval has its other prescribed strict descent factor. -/
@[reassoc]
theorem outerHornCIntervalDesc_edge (ell : ℕ) (hell : 1 ≤ ell) {X : SSet.{u}}
    (f : (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) : SSet.{u}) ⟶ X)
    (g : (stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) : SSet.{u}) ⟶ X)
    (h : Subcomplex.homOfLE (outerHornCInterval_vertex_le_tail ell hell) ≫ f =
      Subcomplex.homOfLE (outerHornCInterval_vertex_le_edge ell hell) ≫ g) :
    Subcomplex.homOfLE (le_sup_right : stdSimplex.face.{u}
        (Finset.Icc (0 : Fin (ell + 1)) 1) ≤ outerHornCIntervalCover ell) ≫
      outerHornCIntervalDesc ell hell f g h = g :=
  (outerHornCInterval_isPushout ell hell).inr_desc f g h

/-- Both original interval legs determine the descended arrow uniquely. -/
theorem outerHornCIntervalDesc_unique (ell : ℕ) (hell : 1 ≤ ell) {X : SSet.{u}}
    (f : (stdSimplex.face (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) : SSet.{u}) ⟶ X)
    (g : (stdSimplex.face (Finset.Icc (0 : Fin (ell + 1)) 1) : SSet.{u}) ⟶ X)
    (h : Subcomplex.homOfLE (outerHornCInterval_vertex_le_tail ell hell) ≫ f =
      Subcomplex.homOfLE (outerHornCInterval_vertex_le_edge ell hell) ≫ g)
    (l : (outerHornCIntervalCover ell : SSet.{u}) ⟶ X)
    (hf : Subcomplex.homOfLE (le_sup_left : stdSimplex.face.{u}
      (Finset.Icc (1 : Fin (ell + 1)) (Fin.last ell)) ≤ outerHornCIntervalCover ell) ≫ l = f)
    (hg : Subcomplex.homOfLE (le_sup_right : stdSimplex.face.{u}
      (Finset.Icc (0 : Fin (ell + 1)) 1) ≤ outerHornCIntervalCover ell) ≫ l = g) :
    l = outerHornCIntervalDesc ell hell f g h := by
  apply (outerHornCInterval_isPushout ell hell).hom_ext
  · exact hf.trans (outerHornCIntervalDesc_tail ell hell f g h).symm
  · exact hg.trans (outerHornCIntervalDesc_edge ell hell f g h).symm

/-- The degree-two face index has exactly the original face on zero and one. -/
theorem outerHornCFaceIndex_zero (S : outerHornCFaceIndex 0) : S.val = {0, 1} := by
  have h0 := S.property.1
  have h1 := S.property.2.1
  have h2 : (2 : Fin 3) ∉ S.val := by
    intro h
    apply S.property.2.2
    ext i
    fin_cases i <;> simp_all
  ext i
  fin_cases i <;> simp [S.property.1, S.property.2.1, h2]

/-- Its original represented local dimension is exactly one. -/
theorem outerHornCFaceDim_zero (S : outerHornCFaceIndex 0) : outerHornCFaceDim S = 1 := by
  rw [outerHornCFaceDim, outerHornCFaceIndex_zero]
  decide

/-- The original degree-two C is the same original edge01. -/
@[simp]
theorem outerHornC_two : outerHornC.{u} 2 = stdSimplex.face {0, 1} := by
  rw [← outerHornCFace_iSup 0]
  apply le_antisymm
  · apply iSup_le
    intro S
    rw [outerHornCFaceIndex_zero]
  · exact le_iSup (fun S : outerHornCFaceIndex 0 => stdSimplex.face.{u} S.val)
      (outerHornCFaceMin 0)

/-- The original degree-two U is also precisely that edge01. -/
@[simp]
theorem outerHornCU_zero : outerHornCU.{u} 0 = stdSimplex.face {0, 1} := by
  rw [outerHornCU, outerHorn_image_cofaceZero, outerHornC_two]
  exact le_antisymm (sup_le inf_le_left le_rfl) le_sup_right

/-- Every original face descent retains all original simplex operators. -/
theorem outerHornCFaceDesc_operator (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S)
    {d e : SimplexCategoryᵒᵖ} (α : d ⟶ e) :
    (outerHornC (m + 2) : SSet.{u}).map α ≫ (outerHornCFaceDesc m f hf).app e =
      (outerHornCFaceDesc m f hf).app d ≫ X.map α :=
  (outerHornCFaceDesc m f hf).naturality α

/-- The same original finite-face cocone under the actual inner-discrete embedding. -/
def innerOuterHornCFaceCocone (m : ℕ) :
    Cocone (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete) :=
  simplicialSpaceDiscrete.mapCocone (outerHornCFaceCocone m)

/-- The mapped original finite-face cocone is genuinely colimiting in both degrees. -/
def innerOuterHornCFaceColimit (m : ℕ) : IsColimit (innerOuterHornCFaceCocone.{u} m) := by
  apply evaluationJointlyReflectsColimits
  intro d
  apply evaluationJointlyReflectsColimits
  intro e
  change IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj d).mapCocone
    (outerHornCFaceCocone.{u} m))
  exact isColimitOfPreserves _ (outerHornCFaceColimit m)

/-- Every compatible original embedded family has its actual whole-object descent. -/
def innerOuterHornCFaceDesc (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S) :
    simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u}) ⟶ X :=
  (innerOuterHornCFaceColimit m).desc
    { pt := X
      ι :=
        { app := f
          naturality := fun {S T} g => by
            change (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S
            exact hf g } }

/-- Every original embedded face has its prescribed strict factor. -/
@[reassoc (attr := simp)]
theorem innerOuterHornCFaceDesc_fac (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) :
    dsimp% simplicialSpaceDiscrete.map (Subcomplex.homOfLE (outerHornCFace_le_C S)) ≫
      innerOuterHornCFaceDesc m f hf = f S :=
  (innerOuterHornCFaceColimit m).fac _ S

/-- Every original embedded face factor determines the whole descended map uniquely. -/
theorem innerOuterHornCFaceDesc_unique (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (l : simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u}) ⟶ X)
    (hl : ∀ S, simplicialSpaceDiscrete.map (Subcomplex.homOfLE (outerHornCFace_le_C S)) ≫ l = f S) :
    l = innerOuterHornCFaceDesc m f hf := by
  apply (innerOuterHornCFaceColimit m).hom_ext
  intro S
  exact (hl S).trans (innerOuterHornCFaceDesc_fac m f hf S).symm

/-- The original embedded face factor holds at every original bidegree and value. -/
theorem innerOuterHornCFaceDesc_bidegree (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) (d e : SimplexCategoryᵒᵖ)
    (q : (((outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S).obj d).obj e) :
    ((innerOuterHornCFaceDesc m f hf).app d).app e
      (((simplicialSpaceDiscrete.map (Subcomplex.homOfLE (outerHornCFace_le_C S))).app d).app e q) =
        ((f S).app d).app e q := by
  exact congrArg (fun k => (k.app d).app e q) (innerOuterHornCFaceDesc_fac m f hf S)

/-- Every original face factor retains the prescribed value in every original degree. -/
theorem outerHornCFaceDesc_app (m : ℕ) {X : SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m, (outerHornCFaceDiagram.{u} m).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m).map g ≫ f T = f S)
    (S : outerHornCFaceIndex m) (d : SimplexCategoryᵒᵖ)
    (q : (outerHornCFaceDiagram.{u} m).obj S |>.obj d) :
    (outerHornCFaceDesc m f hf).app d
      ((Subcomplex.homOfLE (outerHornCFace_le_C S)).app d q) = (f S).app d q :=
  congrArg (fun k => k.app d q) (outerHornCFaceDesc_fac m f hf S)

/-- The embedded original descent retains every outer operator on its original values. -/
theorem innerOuterHornCFaceDesc_outer (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    {d d' : SimplexCategoryᵒᵖ} (α : d ⟶ d') (e : SimplexCategoryᵒᵖ)
    (q : (simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u})).obj d |>.obj e) :
    ((innerOuterHornCFaceDesc m f hf).app d').app e
        (((simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u})).map α).app e q) =
      (X.map α).app e (((innerOuterHornCFaceDesc m f hf).app d).app e q) :=
  congrArg (fun k => k.app e q) ((innerOuterHornCFaceDesc m f hf).naturality α)

/-- The same embedded descent retains every original inner operator. -/
theorem innerOuterHornCFaceDesc_inner (m : ℕ) {X : SimplicialObject SSet.{u}}
    (f : ∀ S : outerHornCFaceIndex m,
      (outerHornCFaceDiagram.{u} m ⋙ simplicialSpaceDiscrete).obj S ⟶ X)
    (hf : ∀ {S T : outerHornCFaceIndex m} (g : S ⟶ T),
      (outerHornCFaceDiagram m ⋙ simplicialSpaceDiscrete).map g ≫ f T = f S)
    (d : SimplexCategoryᵒᵖ) {e e' : SimplexCategoryᵒᵖ} (α : e ⟶ e')
    (q : (simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u})).obj d |>.obj e) :
    ((innerOuterHornCFaceDesc m f hf).app d).app e'
        (((simplicialSpaceDiscrete.obj (outerHornC (m + 2) : SSet.{u})).obj d).map α q) =
      (X.obj d).map α (((innerOuterHornCFaceDesc m f hf).app d).app e q) :=
  ((innerOuterHornCFaceDesc m f hf).app d).naturality_apply α q

end SSet.Rezk
