/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# The original initial-edge and tail-face cover

The literal two interval blocks meet at vertex one. Their mapping
restriction at a Reedy-fibrant Segal target is a trivial Kan fibration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Rezk

/-- The original cover by the initial edge and the remaining full face. -/
def initialIntervalCover (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  match n with
  | 0 => ⊤
  | n + 1 => SSet.stdSimplex.face {(0 : Fin (n + 2))}ᶜ ⊔
    SSet.stdSimplex.face {(0 : Fin (n + 2)), (1 : Fin (n + 2))}

/-- The original tail coface into the two-interval cover. -/
def initialCoverTail (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ (initialIntervalCover (n + 2) : SSet.{u}) :=
  (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (n + 3))).hom ≫
    Subcomplex.homOfLE (by dsimp [initialIntervalCover]; exact le_sup_left)

private theorem edgeMap_apply {n d : ℕ} (i : Fin n)
    (a : (Δ[1] : SSet.{u}) _⦋d⦌) (j : Fin (d + 1)) :
    (((SSet.stdSimplex.map (SimplexCategory.mkOfSucc i)).app (op ⦋d⦌) a) j).val =
      i.val + (a j).val := by
  change ((SimplexCategory.mkOfSucc i).toOrderHom (a j)).val = _
  generalize a j = x
  fin_cases x <;> rfl

private theorem shift_edge (n : ℕ) (i : Fin n) :
    SSet.stdSimplex.map (SimplexCategory.mkOfSucc i) ≫
      SSet.stdSimplex.δ (0 : Fin (n + 2)) =
    SSet.stdSimplex.map (SimplexCategory.mkOfSucc i.succ) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2))) = _
  rw [← SSet.stdSimplex.map_comp]
  congr 1
  ext j
  fin_cases j <;> rfl

private theorem tailImage_le_spine (n : ℕ) :
    (spineSubcomplex.{u} n).image (SSet.stdSimplex.δ (0 : Fin (n + 2))) ≤
      spineSubcomplex (n + 1) := by
  rw [spineSubcomplex, Subcomplex.image_iSup]
  apply iSup_le
  intro i
  rw [← Subcomplex.range_comp]
  rw [shift_edge]
  exact le_iSup (fun i : Fin (n + 1) =>
    Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i))) i.succ

private theorem initialEdge_eq_range (n : ℕ) :
    SSet.stdSimplex.face.{u} {(0 : Fin (n + 2)), (1 : Fin (n + 2))} =
    Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1)))) := by
  ext d a
  induction d using Opposite.rec with | _ d =>
    induction d using SimplexCategory.rec with | _ d =>
      rw [SSet.stdSimplex.mem_face_iff]
      constructor
      · intro ha
        let f : Fin (d + 1) →o Fin 2 :=
          ⟨fun j => ⟨(a j).val, by have := ha j; simp only [Finset.mem_insert,
            Finset.mem_singleton] at this; rcases this with h | h <;> simp [h]⟩,
            fun i j h => SSet.stdSimplex.monotone_apply a h⟩
        refine ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk f), ?_⟩
        apply SSet.stdSimplex.ext
        intro j
        apply Fin.ext
        rw [edgeMap_apply]
        change 0 + (a j).val = (a j).val
        exact Nat.zero_add _
      · rintro ⟨b, rfl⟩ j
        have e := edgeMap_apply (0 : Fin (n + 1)) b j
        have hi := (b j).isLt
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h : (b j).val = 0
        · left
          apply Fin.ext
          simpa [h] using e
        · right
          have h1 : (b j).val = 1 := by omega
          apply Fin.ext
          simpa [h1] using e

private theorem initialEdge_le_spine (n : ℕ) :
    SSet.stdSimplex.face.{u} {(0 : Fin (n + 2)), (1 : Fin (n + 2))} ≤
      spineSubcomplex (n + 1) := by
  rw [initialEdge_eq_range]
  exact le_iSup (fun i : Fin (n + 1) => Subcomplex.range
    (SSet.stdSimplex.map (SimplexCategory.mkOfSucc i))) (0 : Fin (n + 1))

/-- The shifted smaller spine and initial edge form the original full spine. -/
theorem spine_eq_shifted_sup_initialEdge (n : ℕ) :
    spineSubcomplex.{u} (n + 1) =
      (spineSubcomplex n).image (SSet.stdSimplex.δ (0 : Fin (n + 2))) ⊔
        SSet.stdSimplex.face {(0 : Fin (n + 2)), (1 : Fin (n + 2))} := by
  apply le_antisymm
  · rw [spineSubcomplex]
    apply iSup_le
    intro i
    rcases i.eq_zero_or_eq_succ with h | ⟨j, rfl⟩
    · subst i
      rw [← initialEdge_eq_range]
      exact le_sup_right
    · have h := Subcomplex.image_monotone (SSet.stdSimplex.δ (0 : Fin (n + 2)))
        (le_iSup (fun j : Fin n => Subcomplex.range
          (SSet.stdSimplex.map (SimplexCategory.mkOfSucc j))) j)
      dsimp only at h
      rw [← Subcomplex.range_comp, shift_edge] at h
      exact h.trans le_sup_left
  · exact sup_le (tailImage_le_spine n) (initialEdge_le_spine n)

private theorem shiftedSpine_le_tailFace (n : ℕ) :
    (spineSubcomplex.{u} n).image (SSet.stdSimplex.δ (0 : Fin (n + 2))) ≤
      SSet.stdSimplex.face {(0 : Fin (n + 2))}ᶜ := by
  simpa only [SSet.stdSimplex.range_δ] using
    (spineSubcomplex.{u} n).image_le_range (SSet.stdSimplex.δ (0 : Fin (n + 2)))

/-- The literal interval cover is the original spine together with the tail face. -/
theorem initialIntervalCover_eq_spine_sup_tail (n : ℕ) :
    initialIntervalCover.{u} (n + 1) =
      spineSubcomplex (n + 1) ⊔ SSet.stdSimplex.face {(0 : Fin (n + 2))}ᶜ := by
  rw [spine_eq_shifted_sup_initialEdge]
  dsimp only [initialIntervalCover]
  apply le_antisymm
  · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)
  · exact sup_le (sup_le ((shiftedSpine_le_tailFace n).trans le_sup_left) le_sup_right)
      le_sup_left

private theorem initialEdge_inf_tail (n : ℕ) :
    SSet.stdSimplex.face.{u} {(0 : Fin (n + 2)), (1 : Fin (n + 2))} ⊓
        SSet.stdSimplex.face {(0 : Fin (n + 2))}ᶜ =
      SSet.stdSimplex.face {(1 : Fin (n + 2))} := by
  ext d a
  induction d using Opposite.rec with | _ d =>
    induction d using SimplexCategory.rec with | _ d =>
      change (a ∈ (SSet.stdSimplex.face {(0 : Fin (n + 2)), (1 : Fin (n + 2))}).obj _ ∧
        a ∈ (SSet.stdSimplex.face {(0 : Fin (n + 2))}ᶜ).obj _) ↔
        a ∈ (SSet.stdSimplex.face {(1 : Fin (n + 2))}).obj _
      rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff,
        SSet.stdSimplex.mem_face_iff]
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl]
      constructor
      · rintro ⟨h, hn⟩ j
        exact (h j).resolve_left (hn j)
      · intro h
        refine ⟨fun j => Or.inr (h j), fun j => ?_⟩
        rw [h j]
        intro e
        have := congrArg Fin.val e
        simp at this

private theorem vertexOne_le_shiftedSpine (n : ℕ) :
    SSet.stdSimplex.face.{u} {(1 : Fin (n + 3))} ≤
      (spineSubcomplex (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3))) := by
  have h0 : SSet.stdSimplex.face.{u} {(0 : Fin (n + 2))} ≤ spineSubcomplex (n + 1) := by
    exact (SSet.stdSimplex.face_le_face_iff _ _).mpr (by simp) |>.trans
      (initialEdge_le_spine n)
  have h := Subcomplex.image_monotone (SSet.stdSimplex.δ (0 : Fin (n + 3))) h0
  have e : (SSet.stdSimplex.face.{u} {(0 : Fin (n + 2))}).image
      (SSet.stdSimplex.δ (0 : Fin (n + 3))) = SSet.stdSimplex.face {(1 : Fin (n + 3))} := by
    ext d a
    induction d using Opposite.rec with | _ d =>
      induction d using SimplexCategory.rec with | _ d =>
        constructor
        · rintro ⟨b, hb, rfl⟩
          rw [SSet.stdSimplex.mem_face_iff] at hb ⊢
          intro j
          have hj : b j = 0 := by simpa using hb j
          change (Fin.succ (b j)) ∈ {(1 : Fin (n + 3))}
          simp [hj]
        · intro ha
          rw [SSet.stdSimplex.mem_face_iff] at ha
          let b : (Δ[n + 1] : SSet.{u}) _⦋d⦌ :=
            SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋d⦌ ⦋n + 1⦌ 0)
          refine ⟨b, ?_, ?_⟩
          · rw [SSet.stdSimplex.mem_face_iff]
            intro j
            change (0 : Fin (n + 2)) ∈ {(0 : Fin (n + 2))}
            simp
          · apply SSet.stdSimplex.ext
            intro j
            have hj : a j = 1 := by simpa using ha j
            change (0 : Fin (n + 2)).succ = a j
            exact hj.symm
  dsimp only at h
  rw [e] at h
  exact h

/-- The original spine/tail intersection is the actual shifted smaller spine. -/
theorem spine_inf_tail_eq_shifted (n : ℕ) :
    spineSubcomplex.{u} (n + 2) ⊓ SSet.stdSimplex.face {(0 : Fin (n + 3))}ᶜ =
      (spineSubcomplex (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3))) := by
  rw [spine_eq_shifted_sup_initialEdge]
  let A := (spineSubcomplex.{u} (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3)))
  let E := SSet.stdSimplex.face.{u} {(0 : Fin (n + 3)), (1 : Fin (n + 3))}
  let F := SSet.stdSimplex.face.{u} {(0 : Fin (n + 3))}ᶜ
  change (A ⊔ E) ⊓ F = A
  have dist : (A ⊔ E) ⊓ F = A ⊓ F ⊔ E ⊓ F := by
    ext d a
    change ((a ∈ A.obj d ∨ a ∈ E.obj d) ∧ a ∈ F.obj d) ↔
      (a ∈ A.obj d ∧ a ∈ F.obj d) ∨ (a ∈ E.obj d ∧ a ∈ F.obj d)
    tauto
  rw [dist, inf_eq_left.mpr (shiftedSpine_le_tailFace (n + 1))]
  have eq : E ⊓ F = SSet.stdSimplex.face.{u} {(1 : Fin (n + 3))} := initialEdge_inf_tail (n + 1)
  rw [eq]
  exact sup_eq_left.mpr (vertexOne_le_shiftedSpine n)

private def shiftedSpineIso (n : ℕ) :
    (spineSubcomplex.{u} (n + 1) : SSet.{u}) ≅
      ((spineSubcomplex (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3))) : SSet.{u}) := by
  let f := (spineSubcomplex.{u} (n + 1)).toImage (SSet.stdSimplex.δ (0 : Fin (n + 3)))
  let : Mono (SSet.stdSimplex.δ (0 : Fin (n + 3)) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2]) := by
    rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι (0 : Fin (n + 3))]
    infer_instance
  let : Mono f := mono_of_mono_fac
    ((spineSubcomplex (n + 1)).toImage_ι (SSet.stdSimplex.δ (0 : Fin (n + 3))))
  let : IsIso f := isIso_of_mono_of_epi f
  exact asIso f

private theorem shiftedSpineIso_ι (n : ℕ) :
    (shiftedSpineIso.{u} n).hom ≫
      ((spineSubcomplex (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3)))).ι =
        (spineSubcomplex (n + 1)).ι ≫ SSet.stdSimplex.δ (0 : Fin (n + 3)) := rfl

/-- The original shifted smaller spine maps into the full original spine. -/
def initialCoverShiftedSpine (n : ℕ) :
    (spineSubcomplex.{u} (n + 1) : SSet.{u}) ⟶ (spineSubcomplex (n + 2) : SSet.{u}) :=
  (spineSubcomplex.{u} (n + 1)).toImage (SSet.stdSimplex.δ (0 : Fin (n + 3))) ≫
    Subcomplex.homOfLE (tailImage_le_spine (n + 1))

/-- Its ambient equation uses the same original zero coface. -/
@[reassoc (attr := simp)] theorem initialCoverShiftedSpine_ι (n : ℕ) :
    initialCoverShiftedSpine.{u} n ≫ (spineSubcomplex (n + 2)).ι =
      (spineSubcomplex (n + 1)).ι ≫ SSet.stdSimplex.δ (0 : Fin (n + 3)) := by
  simp only [initialCoverShiftedSpine, Category.assoc, Subcomplex.homOfLE_ι,
    Subcomplex.toImage_ι]

/-- The original spine inclusion in the two-interval cover. -/
def initialCoverSpine (n : ℕ) :
    (spineSubcomplex.{u} (n + 2) : SSet.{u}) ⟶ (initialIntervalCover (n + 2) : SSet.{u}) :=
  Subcomplex.homOfLE (by rw [initialIntervalCover_eq_spine_sup_tail]; exact le_sup_left)

/-- The original spine inclusion retains its ambient map. -/
@[reassoc (attr := simp)] theorem initialCoverSpine_ι (n : ℕ) :
    initialCoverSpine.{u} n ≫ (initialIntervalCover (n + 2)).ι = (spineSubcomplex (n + 2)).ι := rfl

/-- The original tail inclusion retains its ambient zero coface. -/
@[reassoc (attr := simp)] theorem initialCoverTail_ι (n : ℕ) :
    initialCoverTail.{u} n ≫ (initialIntervalCover (n + 2)).ι =
      SSet.stdSimplex.δ (0 : Fin (n + 3)) := by
  simp only [initialCoverTail, Category.assoc, Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι]

/-- The original shifted-spine square is the literal interval-cover pushout. -/
theorem initialIntervalCover_isPushout (n : ℕ) :
    IsPushout (spineSubcomplex.{u} (n + 1)).ι (initialCoverShiftedSpine n)
      (initialCoverTail n) (initialCoverSpine n) := by
  let A := spineSubcomplex.{u} (n + 2)
  let F := SSet.stdSimplex.face.{u} {(0 : Fin (n + 3))}ᶜ
  let D := (spineSubcomplex (n + 1)).image (SSet.stdSimplex.δ (0 : Fin (n + 3)))
  have square : Subcomplex.BicartSq D F A (initialIntervalCover (n + 2)) :=
    { sup_eq := (sup_comm F A).trans (initialIntervalCover_eq_spine_sup_tail (n + 1)).symm
      inf_eq := by rw [inf_comm]; exact spine_inf_tail_eq_shifted n }
  have sq := square.isPushout
  apply sq.of_iso' (shiftedSpineIso n)
    (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (n + 3))) (Iso.refl _) (Iso.refl _)
  · apply (cancel_mono F.ι).mp
    change (shiftedSpineIso n).hom ≫ Subcomplex.homOfLE square.le₁₂ ≫ F.ι =
      (spineSubcomplex (n + 1)).ι ≫
          (SSet.stdSimplex.faceSingletonComplIso (0 : Fin (n + 3))).hom ≫ F.ι
    dsimp only [F]
    rw [Subcomplex.homOfLE_ι, SSet.stdSimplex.faceSingletonComplIso_hom_ι]
    exact shiftedSpineIso_ι n
  · apply (cancel_mono A.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rfl
  · rfl
  · rfl

end SSet.Rezk

namespace SimplicialSpace

private theorem discrete_preservesPushouts :
    PreservesColimitsOfShape WalkingSpan SSet.simplicialSpaceDiscrete.{u} :=
  ⟨fun {K} => ⟨fun c {hc} => ⟨by
    apply evaluationJointlyReflectsColimits _ (fun k => ?_)
    change IsColimit
      ((((evaluation _ _).obj k ⋙ SimplicialObject.const (Type u)).mapCocone c))
    exact isColimitOfPreserves _ hc⟩⟩⟩

private theorem inner_flip_preservesPullbacks (W : SimplicialSpace.{u}) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj W) := by
  let : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      (innerTensorBifunctor.flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (innerTensor K)
    let : (innerTensor K).IsLeftAdjoint :=
      (innerTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact innerTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan W

/-- The original two-interval union gives the actual mapping pullback. -/
theorem initialIntervalMapping_isPullback (W : SimplicialSpace.{u}) (n : ℕ) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.Rezk.initialCoverSpine.{u} n).op)
      ((discreteSourceMapping W).map (SSet.Rezk.initialCoverTail.{u} n).op)
      ((discreteSourceMapping W).map (SSet.Rezk.initialCoverShiftedSpine.{u} n).op)
      ((discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} (n + 1)).ι.op) := by
  let := discrete_preservesPushouts.{u}
  let := inner_flip_preservesPullbacks W
  have sq := ((SSet.Rezk.initialIntervalCover_isPushout.{u} n).map
    SSet.simplicialSpaceDiscrete).map ofSimplicialObject
  exact sq.op.map (innerHomFunctor.flip.obj W)

private theorem sourceRestriction_fibration {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (W : SimplicialSpace.{u}) :
    letI : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    HomotopicalAlgebra.IsFibrant W → HomotopicalAlgebra.Fibration
      ((discreteSourceMapping W).map i.op) := by
  intro hW
  let : HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro m
    rw [NatTrans.mono_iff_mono_app]
    intro j
    change Mono (i.app m)
    have hi : Mono i := inferInstance
    rw [NatTrans.mono_iff_mono_app] at hi
    exact hi m
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have hcof : HomotopicalAlgebra.cofibrations SimplicialSpace.{u} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp
      ((ReedyModel.cofibration_iff f).mpr inferInstance)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (ReedyModel.inner_precomp_fibration f W hcof hW)

private theorem spineRestriction_trivialFibration (W : SimplicialSpace.{u})
    (n : ℕ) (hW : segalSpaces W) :
    HomotopicalAlgebra.trivialFibrations SSet.{u}
      ((discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} (n + 1)).ι.op) := by
  cases n with
  | zero =>
    have htop : SSet.Rezk.spineSubcomplex.{u} 1 = ⊤ := by
      rw [SSet.Rezk.spineSubcomplex]
      have e : (SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin 1)) :
          (Δ[1] : SSet.{u}) ⟶ Δ[1]) = 𝟙 _ := by
        rw [← SSet.stdSimplex.map_id]
        congr 1
        ext j
        fin_cases j <;> rfl
      rw [iSup_unique]
      change SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin 1))) = ⊤
      rw [e]
      exact SSet.Subcomplex.range_eq_top _
    have hiso : IsIso (SSet.Rezk.spineSubcomplex.{u} 1).ι := by
      rw [htop]
      exact inferInstanceAs (IsIso (SSet.Subcomplex.topIso (Δ[1] : SSet.{u})).hom)
    exact (HomotopicalAlgebra.mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
  | succ n =>
    have h := rawSegalComparison_trivialFibration W (n + 2) (by omega) hW
    let r := (discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} (n + 2)).ι.op
    let e : Arrow.mk r ≅ Arrow.mk (rawSegalComparison W (n + 2)) :=
      Arrow.isoMk (discreteYonedaIso W (n + 2)) (Iso.refl _) (by
        change (discreteYonedaIso W (n + 2)).hom ≫
          ((discreteYonedaIso W (n + 2)).inv ≫ r) = r ≫ 𝟙 _
        simp only [Iso.hom_inv_id_assoc, Category.comp_id])
    exact ((HomotopicalAlgebra.trivialFibrations SSet.{u}).arrow_mk_iso_iff e).mpr h

private theorem coverSpineRestriction_trivialFibration (W : SimplicialSpace.{u})
    (n : ℕ) (hW : segalSpaces W) :
    HomotopicalAlgebra.trivialFibrations SSet.{u}
      ((discreteSourceMapping W).map (SSet.Rezk.initialCoverSpine.{u} n).op) :=
  (HomotopicalAlgebra.trivialFibrations SSet.{u}).of_isPullback
    (initialIntervalMapping_isPullback W n).flip
    (spineRestriction_trivialFibration W n hW)

/-- The original two-interval cover restriction is a genuine Kan trivial fibration. -/
theorem initialIntervalCover_trivialFibration (W : SimplicialSpace.{u})
    (n : ℕ) (hW : segalSpaces W) :
    HomotopicalAlgebra.trivialFibrations SSet.{u}
      ((discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover.{u} n).ι.op) := by
  cases n with
  | zero =>
    change HomotopicalAlgebra.trivialFibrations SSet.{u}
      ((discreteSourceMapping W).map (SSet.Subcomplex.ι (⊤ : (Δ[0] : SSet.{u}).Subcomplex)).op)
    have : IsIso (SSet.Subcomplex.ι (⊤ : (Δ[0] : SSet.{u}).Subcomplex)) :=
      inferInstanceAs (IsIso (SSet.Subcomplex.topIso (Δ[0] : SSet.{u})).hom)
    exact (HomotopicalAlgebra.mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
  | succ n =>
    cases n with
    | zero =>
      have htop : SSet.Rezk.initialIntervalCover.{u} 1 = ⊤ := by
        dsimp only [SSet.Rezk.initialIntervalCover]
        have e : ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) = Finset.univ := by decide
        rw [e, SSet.stdSimplex.face_univ, sup_top_eq]
      have : IsIso (SSet.Rezk.initialIntervalCover.{u} 1).ι := by
        rw [htop]
        exact inferInstanceAs (IsIso (SSet.Subcomplex.topIso (Δ[1] : SSet.{u})).hom)
      exact (HomotopicalAlgebra.mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩
    | succ n =>
      let r := (discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover.{u} (n + 2)).ι.op
      let q := (discreteSourceMapping W).map (SSet.Rezk.initialCoverSpine.{u} n).op
      let : HomotopicalAlgebra.Fibration r := sourceRestriction_fibration _ W hW.1
      have hq : HomotopicalAlgebra.trivialFibrations SSet.{u} q :=
        coverSpineRestriction_trivialFibration W n hW
      have hcomp : r ≫ q =
          (discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} (n + 2)).ι.op := by
        rw [← (discreteSourceMapping W).map_comp, ← op_comp, SSet.Rezk.initialCoverSpine_ι]
      have hwq : SSet.realizationWeakEquivalences q := hq.2
      have hwcomp : SSet.realizationWeakEquivalences (r ≫ q) := by
        rw [hcomp]
        exact (spineRestriction_trivialFibration W (n + 1) hW).2
      have hwr : SSet.realizationWeakEquivalences r :=
        SSet.realizationWeakEquivalences.of_postcomp r q hwq hwcomp
      exact ⟨HomotopicalAlgebra.Fibration.mem, hwr⟩

/-- Every original target map preserves the literal interval restriction square. -/
theorem initialIntervalCover_naturality {W V : SimplicialSpace.{u}}
    (t : W ⟶ V) (n : ℕ) :
    (discreteSourceMappingMap t).app (op (Δ[n] : SSet.{u})) ≫
        (discreteSourceMapping V).map (SSet.Rezk.initialIntervalCover.{u} n).ι.op =
      (discreteSourceMapping W).map (SSet.Rezk.initialIntervalCover.{u} n).ι.op ≫
        (discreteSourceMappingMap t).app
          (op (SSet.Rezk.initialIntervalCover.{u} n : SSet.{u})) :=
  ((discreteSourceMappingMap t).naturality (SSet.Rezk.initialIntervalCover.{u} n).ι.op).symm

/-- The selected mapping pullback retains the original interval restriction maps. -/
def initialIntervalMappingIso (W : SimplicialSpace.{u}) (n : ℕ) :
    (discreteSourceMapping W).obj
        (op (SSet.Rezk.initialIntervalCover.{u} (n + 2) : SSet.{u})) ≅
      pullback
        ((discreteSourceMapping W).map (SSet.Rezk.initialCoverShiftedSpine.{u} n).op)
        ((discreteSourceMapping W).map (SSet.Rezk.spineSubcomplex.{u} (n + 1)).ι.op) :=
  (initialIntervalMapping_isPullback W n).isoPullback

/-- The comparison's first projection is the original spine restriction. -/
@[reassoc (attr := simp)] theorem initialIntervalMappingIso_fst (W : SimplicialSpace.{u}) (n : ℕ) :
    (initialIntervalMappingIso W n).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map (SSet.Rezk.initialCoverSpine.{u} n).op :=
  (initialIntervalMapping_isPullback W n).isoPullback_hom_fst

/-- The comparison's second projection is the original tail restriction. -/
@[reassoc (attr := simp)] theorem initialIntervalMappingIso_snd (W : SimplicialSpace.{u}) (n : ℕ) :
    (initialIntervalMappingIso W n).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map (SSet.Rezk.initialCoverTail.{u} n).op :=
  (initialIntervalMapping_isPullback W n).isoPullback_hom_snd

/-- Its inverse preserves the original first restriction. -/
@[reassoc (attr := simp)] theorem initialIntervalMappingIso_inv_fst
    (W : SimplicialSpace.{u}) (n : ℕ) :
    (initialIntervalMappingIso W n).inv ≫
        (discreteSourceMapping W).map (SSet.Rezk.initialCoverSpine.{u} n).op =
      pullback.fst _ _ := by
  rw [← initialIntervalMappingIso_fst, Iso.inv_hom_id_assoc]

/-- Its inverse preserves the original second restriction. -/
@[reassoc (attr := simp)] theorem initialIntervalMappingIso_inv_snd
    (W : SimplicialSpace.{u}) (n : ℕ) :
    (initialIntervalMappingIso W n).inv ≫
        (discreteSourceMapping W).map (SSet.Rezk.initialCoverTail.{u} n).op =
      pullback.snd _ _ := by
  rw [← initialIntervalMappingIso_snd, Iso.inv_hom_id_assoc]

end SimplicialSpace
