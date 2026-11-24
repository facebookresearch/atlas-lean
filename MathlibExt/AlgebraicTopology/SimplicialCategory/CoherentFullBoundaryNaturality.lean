/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryHomGlue
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxReadback

/-!
# Exact original full-boundary Hom naturality and simplex readback

All original positive and negative faces follow the same enriched
map. Restricting a genuine original enriched simplex to its full
boundary recovers its entire outer Hom map on that same face union.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomNaturality
open SimplicialEnrichment HornBoxFaces

variable {C D : Carrier.{u}} {n : ℕ}
  (F : C ⟶ D) (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- Every original full-boundary vertex follows the literal object map. -/
theorem object_map (t : Fin (n+3)) :
    BoundaryFaces.object (f ≫ coherentNerveFunctor.map F) t = F.obj (BoundaryFaces.object f t) := rfl

/-- Every whole original boundary face follows the same strict enriched functor. -/
theorem faceFunctor_map (j : Fin (n+3)) :
    BoundaryFaces.faceFunctor (f ≫ coherentNerveFunctor.map F) j =
      BoundaryFaces.faceFunctor f j ≫ F := rfl

/-- The actual full negative face retains its complete original Hom map under postcomposition. -/
theorem negativeMap_postcompose (k : Interior.{u} n) :
    BoundaryHomFaces.negativeMap f k ≫
        F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
      BoundaryHomFaces.negativeMap (f ≫ coherentNerveFunctor.map F) k := by
  have h := HornMapNaturality.retargetMap_postcompose
    (BoundaryFaces.faceFunctor f (HornBoxFaces.vertex k)) F
    (.mk (ULift.up (0 : Fin (n+2)))) (.mk (ULift.up (Fin.last (n+1))))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (source_zero k)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (target_last k)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => (negativeChart k).inv ≫ q) h)

/-- The full positive composition face retains the same original enriched composition after the map. -/
theorem positiveMap_postcompose (k : Interior.{u} n) :
    BoundaryHomFaces.positiveMap f k ≫
        F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
      BoundaryHomFaces.positiveMap (f ≫ coherentNerveFunctor.map F) k := by
  let i := BoundaryHomFaces.canonicalIndex (n := n)
  have h := HornMapNaturality.positiveMap_postcompose F (BoundaryFaces.horn f i)
    (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
    (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) k
  change HornBoxFaces.positiveMap (BoundaryFaces.horn f i)
      (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
      (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) k ≫
        F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
    HornBoxFaces.positiveMap (BoundaryFaces.horn (f ≫ coherentNerveFunctor.map F) i)
      (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
      (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) k at h
  simp only [BoundaryHomFaces.positiveMap_horn] at h
  change BoundaryHomFaces.positiveMap f k ≫
      F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
    BoundaryHomFaces.positiveMap (f ≫ coherentNerveFunctor.map F) k at h
  exact h

/-- The same entire full-boundary colimit map follows the literal enriched map. -/
theorem map_postcompose :
    BoundaryHomGlue.map f ≫
        F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2))) =
      BoundaryHomGlue.map (f ≫ coherentNerveFunctor.map F) := by
  apply Multicofork.IsColimit.hom_ext (BoundaryHomGlue.diagram.{u} (n := n)).isColimit
  intro x
  change BoundaryHomGlue.inclusion x ≫
      (BoundaryHomGlue.map f ≫ F.map (BoundaryFaces.object f 0)
        (BoundaryFaces.object f (Fin.last (n+2)))) =
    BoundaryHomGlue.inclusion x ≫ BoundaryHomGlue.map (f ≫ coherentNerveFunctor.map F)
  rcases x with k | k
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ F.map (BoundaryFaces.object f 0)
        (BoundaryFaces.object f (Fin.last (n+2)))) (BoundaryHomGlue.map_face f (.inl k))).trans
        ((positiveMap_postcompose F f k).trans
          (BoundaryHomGlue.map_face (f ≫ coherentNerveFunctor.map F) (.inl k)).symm))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ F.map (BoundaryFaces.object f 0)
        (BoundaryFaces.object f (Fin.last (n+2)))) (BoundaryHomGlue.map_face f (.inr k))).trans
        ((negativeMap_postcompose F f k).trans
          (BoundaryHomGlue.map_face (f ≫ coherentNerveFunctor.map F) (.inr k)).symm))

/-- The original full-boundary restriction of a supplied genuine simplex. -/
def fromSimplex (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) :
    (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
  (SSet.boundary.{u} (n+2)).ι ≫ SSet.yonedaEquiv.symm σ

/-- Restricting a genuine original simplex recovers its same full enriched face. -/
theorem fromSimplex_face (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) (j : Fin (n+3)) :
    BoundaryFaces.faceFunctor (fromSimplex σ) j = coherentSimplexMap (SimplexCategory.δ j) ≫ σ := by
  classical
  let i : Fin (n+3) := if j = 0 then ⟨1, by omega⟩ else 0
  have hji : j ≠ i := by
    dsimp [i]
    split_ifs with h
    · subst j
      intro h01
      have hv := congrArg Fin.val h01
      change 0 = 1 at hv
      omega
    · exact h
  exact (BoundaryFaces.horn_face (fromSimplex σ) i j hji).symm.trans
    (HornFromSimplex.face_readback σ i j hji)

/-- Every original vertex of the complete restricted boundary is the SAME original simplex vertex. -/
theorem fromSimplex_object (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) (t : Fin (n+3)) :
    BoundaryFaces.object (fromSimplex σ) t = σ.obj (.mk (ULift.up t)) :=
  HornFromSimplex.object_readback σ 1 t

/-- The actual original full negative face of a restricted simplex is its SAME entire outer Hom restriction. -/
theorem fromSimplex_negative (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) (k : Interior.{u} n) :
    BoundaryHomFaces.negativeMap (fromSimplex σ) k =
      (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι ≫
        σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))) := by
  let G := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let a : coherentSimplex.{u} ⦋n+1⦌ := .mk (ULift.up 0)
  let b : coherentSimplex.{u} ⦋n+1⦌ := .mk (ULift.up (Fin.last (n+1)))
  let x : coherentSimplex.{u} ⦋n+2⦌ := .mk (ULift.up 0)
  let y : coherentSimplex.{u} ⦋n+2⦌ := .mk (ULift.up (Fin.last (n+2)))
  have hx : G.obj a = x := congrArg SimplicialThickening.mk (ULift.ext (source_zero k))
  have hy : G.obj b = y := congrArg SimplicialThickening.mk (ULift.ext (target_last k))
  let E := negativeChart k
  let I := (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι
  have hE : E.hom ≫ I = HornHomFaces.retargetMap G a b hx hy := HornNegativeMaps.chart_operator k
  have hI : E.inv ≫ HornHomFaces.retargetMap G a b hx hy = I :=
    (congrArg (fun q => E.inv ≫ q) hE.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ I) E.inv_hom_id).trans (Category.id_comp I)))
  have hEq := HornHomFaces.retargetMap_eq (fromSimplex_face σ (HornBoxFaces.vertex k)) a b
    ((BoundaryFaces.faceFunctor_obj (fromSimplex σ) (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object (fromSimplex σ)) (source_zero k)))
    ((BoundaryFaces.faceFunctor_obj (fromSimplex σ) (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object (fromSimplex σ)) (target_last k)))
    (congrArg σ.obj hx) (congrArg σ.obj hy)
  have hPost := HornMapNaturality.retargetMap_postcompose G σ a b hx hy
  change E.inv ≫ _ = I ≫ σ.map x y
  exact (congrArg (fun q => E.inv ≫ q) hEq).trans
    ((congrArg (fun q => E.inv ≫ q) hPost.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ σ.map x y) hI)))

/-- The actual original full positive face of a restricted simplex is its same complete outer Hom restriction. -/
theorem fromSimplex_positive (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) (k : Interior.{u} n) :
    BoundaryHomFaces.positiveMap (fromSimplex σ) k =
      (CompositionFace.positive (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι ≫
        σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))) := by
  let i := BoundaryHomFaces.canonicalIndex (n := n)
  change HornBoxFaces.positiveMap (HornFromSimplex.horn σ i)
      (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
      (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) k =
    (CompositionFace.positive (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι ≫
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2))))
  exact HornBoxReadback.positiveMap σ i
    (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
    (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) k

/-- The SAME original outer Hom is read back on the entire full boundary union. -/
theorem fromSimplex_map (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C) :
    BoundaryHomGlue.map (fromSimplex σ) =
      (BoundaryHomGlue.boundary.{u} (n := n)).ι ≫
        σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))) := by
  apply Multicofork.IsColimit.hom_ext (BoundaryHomGlue.diagram.{u} (n := n)).isColimit
  intro x
  change BoundaryHomGlue.inclusion x ≫ BoundaryHomGlue.map (fromSimplex σ) =
    BoundaryHomGlue.inclusion x ≫ ((BoundaryHomGlue.boundary.{u} (n := n)).ι ≫
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))))
  rcases x with k | k
  · have hι : BoundaryHomGlue.inclusion (.inl k) ≫
        (BoundaryHomGlue.boundary.{u} (n := n)).ι =
      (CompositionFace.positive (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι := rfl
    exact (BoundaryHomGlue.map_face (fromSimplex σ) (.inl k)).trans
      ((fromSimplex_positive σ k).trans
        ((congrArg (fun q => q ≫ σ.map (.mk (ULift.up 0))
          (.mk (ULift.up (Fin.last (n+2))))) hι.symm).trans (Category.assoc _ _ _)))
  · have hι : BoundaryHomGlue.inclusion (.inr k) ≫
        (BoundaryHomGlue.boundary.{u} (n := n)).ι =
      (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))).ι := rfl
    exact (BoundaryHomGlue.map_face (fromSimplex σ) (.inr k)).trans
      ((fromSimplex_negative σ k).trans
        ((congrArg (fun q => q ≫ σ.map (.mk (ULift.up 0))
          (.mk (ULift.up (Fin.last (n+2))))) hι.symm).trans (Category.assoc _ _ _)))

end CategoryTheory.CoherentRealization.BoundaryHomNaturality
