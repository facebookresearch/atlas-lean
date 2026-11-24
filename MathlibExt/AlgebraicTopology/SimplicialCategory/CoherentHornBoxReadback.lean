/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFromSimplex
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeMaps

/-!
# Exact target-simplex and strict-map readback of a coherent Hom box

The original supplied-face colimit map agrees with the restriction of
an actual enriched simplex on the entire box. Postcomposition follows
the same actual strict map. These are the whole target equations used
in a relative horn lifting square, with the original vertices retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornBoxReadback
open SimplicialEnrichment HornBoxFaces

variable {C : Carrier.{u}} {n : ℕ} (σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ C)
  (i : Fin (n + 3))

/-- The whole extracted outside Hom of a restricted actual simplex reads exactly the original simplex Hom map. -/
theorem outside_faceMap (j : Fin (n + 3)) (hj : j ≠ i)
    (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    {a b : Fin (n + 3)} (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) :
    HornOutsideIntervals.faceMap (HornFromSimplex.horn σ i) j hj a' b' h ha hb =
      σ.map (.mk (ULift.up a)) (.mk (ULift.up b)) := by
  subst a
  subst b
  let E := IntervalFaceCover.outsideIso j a' b' h
  let G := coherentSimplexMap (SimplexCategory.δ j)
  let M := σ.map (G.obj (.mk a')) (G.obj (.mk b'))
  have hE : E.hom = G.map (.mk a') (.mk b') := IntervalFaceCover.outsideIso_operator j a' b' h
  change (𝟙 _ ≫ E.inv ≫ ((G.map (.mk a') (.mk b') ≫ M) ≫ 𝟙 _) ≫ 𝟙 _) = M
  simp only [Category.id_comp]
  exact (congrArg (fun f => E.inv ≫ (f ≫ M)) hE.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ M) E.inv_hom_id).trans (Category.id_comp _)))

/-- Every nonexceptional ordered Hom reads back the actual original target-simplex map. -/
theorem outside_homMap (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    HornOutsideIntervals.homMap (HornFromSimplex.horn σ i) hi₀ hiₙ a b hab h =
      σ.map (.mk (ULift.up a)) (.mk (ULift.up b)) := by
  classical
  unfold HornOutsideIntervals.homMap
  split_ifs with ha
  · exact outside_faceMap σ i _ _ _ _ _ _ _
  · exact outside_faceMap σ i _ _ _ _ _ _ _

/-- The actual whole positive box face is the restriction of the prescribed original simplex. -/
theorem positiveMap (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b : Interior.{u} n) :
    HornBoxFaces.positiveMap (HornFromSimplex.horn σ i) hi₀ hiₙ b =
      (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) b.val
        (ULift.up (Fin.last (n + 2)))).ι ≫
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) := by
  let a : coherentSimplex.{u} ⦋n + 2⦌ := .mk (ULift.up 0)
  let c : coherentSimplex.{u} ⦋n + 2⦌ := .mk (ULift.up (Fin.last (n + 2)))
  let m : coherentSimplex.{u} ⦋n + 2⦌ := .mk b.val
  let E := CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val
    (ULift.up (Fin.last (n + 2)))
  have hL : HornBoxFaces.leftMap (HornFromSimplex.horn σ i) hi₀ hiₙ b = σ.map a m :=
    outside_homMap σ i hi₀ hiₙ 0 (HornBoxFaces.vertex b) (Fin.zero_le _) (Or.inr (vertex_ne_last b))
  have hR : HornBoxFaces.rightMap (HornFromSimplex.horn σ i) hi₀ hiₙ b = σ.map m c :=
    outside_homMap σ i hi₀ hiₙ (HornBoxFaces.vertex b) (Fin.last (n + 2)) (Fin.le_last _) (Or.inl (vertex_ne_zero b))
  let I := (CompositionFace.positive (ULift.up.{u} (0 : Fin (n + 3))) b.val
    (ULift.up (Fin.last (n + 2)))).ι
  have hE : E.hom ≫ I = eComp SSet.{u} a m c :=
    CompositionFace.positiveIso_composition (ULift.up.{u} (0 : Fin (n + 3))) b.val
      (ULift.up (Fin.last (n + 2)))
  have hI : E.inv ≫ eComp SSet.{u} a m c = I :=
    (congrArg (fun f => E.inv ≫ f) hE.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ I) E.inv_hom_id).trans (Category.id_comp I)))
  change E.inv ≫
    (HornBoxFaces.leftMap (HornFromSimplex.horn σ i) hi₀ hiₙ b ⊗ₘ
      HornBoxFaces.rightMap (HornFromSimplex.horn σ i) hi₀ hiₙ b) ≫
      eComp SSet.{u} (σ.obj a) (σ.obj m) (σ.obj c) = I ≫ σ.map a c
  have hLR := congrArg₂ (fun L R => L ⊗ₘ R) hL hR
  exact (congrArg (fun f => E.inv ≫ f ≫ eComp SSet.{u} (σ.obj a) (σ.obj m) (σ.obj c)) hLR).trans
    ((congrArg (fun f => E.inv ≫ f) (σ.map_comp a m c).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ σ.map a c) hI)))

/-- The actual whole retained negative box face is the restriction of the prescribed original simplex. -/
theorem negativeMap (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    HornBoxFaces.negativeMap (HornFromSimplex.horn σ i) k hk =
      (HomBoxDecomposition.negative (ULift.up.{u} (0 : Fin (n + 3))) k.val
        (ULift.up (Fin.last (n + 2)))).ι ≫
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) := by
  let G := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let a : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up 0)
  let b : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up (Fin.last (n + 1)))
  let x : coherentSimplex.{u} ⦋n + 2⦌ := .mk (ULift.up 0)
  let y : coherentSimplex.{u} ⦋n + 2⦌ := .mk (ULift.up (Fin.last (n + 2)))
  have hx : G.obj a = x := congrArg SimplicialThickening.mk (ULift.ext (source_zero k))
  have hy : G.obj b = y := congrArg SimplicialThickening.mk (ULift.ext (target_last k))
  let E := HornBoxFaces.negativeChart k
  let I := (HomBoxDecomposition.negative (ULift.up.{u} (0 : Fin (n + 3))) k.val
    (ULift.up (Fin.last (n + 2)))).ι
  have hE : E.hom ≫ I = HornHomFaces.retargetMap G a b hx hy := HornNegativeMaps.chart_operator k
  have hI : E.inv ≫ HornHomFaces.retargetMap G a b hx hy = I :=
    (congrArg (fun f => E.inv ≫ f) hE.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ I) E.inv_hom_id).trans (Category.id_comp I)))
  have hPost := HornMapNaturality.retargetMap_postcompose G σ a b hx hy
  change E.inv ≫ HornHomFaces.retargetMap (G ≫ σ) a b (congrArg σ.obj hx) (congrArg σ.obj hy) =
    I ≫ σ.map x y
  exact (congrArg (fun f => E.inv ≫ f) hPost.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ σ.map x y) hI))

/-- Every entire box-face map is the restriction of the prescribed simplex's original outer Hom map. -/
theorem maps (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (k : Index.{u} i) :
    HornBoxFaces.maps (HornFromSimplex.horn σ i) hi₀ hiₙ k = (face i k).ι ≫
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) := by
  rcases k with b | k
  · exact positiveMap σ i hi₀ hiₙ b
  · exact negativeMap σ i k.val k.property

/-- The whole actual Hom-box map reads back the entire original target-simplex restriction. -/
theorem boxMap (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) :
    HornBoxGlue.boxMap hi₀ hiₙ (HornFromSimplex.horn σ i) =
      (HornBoxGlue.box i hi₀ hiₙ).ι ≫ σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) := by
  refine Multicofork.IsColimit.hom_ext (HornBoxGlue.diagram i hi₀ hiₙ).isColimit (fun k => ?_)
  change HornBoxGlue.inclusion i hi₀ hiₙ k ≫ HornBoxGlue.boxMap hi₀ hiₙ (HornFromSimplex.horn σ i) =
    HornBoxGlue.inclusion i hi₀ hiₙ k ≫
      ((HornBoxGlue.box i hi₀ hiₙ).ι ≫ σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))))
  have hI : HornBoxGlue.inclusion i hi₀ hiₙ k ≫ (HornBoxGlue.box i hi₀ hiₙ).ι = (face i k).ι := rfl
  exact (HornBoxGlue.boxMap_face hi₀ hiₙ (HornFromSimplex.horn σ i) k).trans
    ((maps σ i hi₀ hiₙ k).trans
      ((congrArg (fun f => f ≫ σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))) hI.symm).trans
        (Category.assoc _ _ _)))

variable {D : Carrier.{u}} (F : C ⟶ D)
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The entire original Hom-box colimit map follows the actual enriched functor. -/
theorem boxMap_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) :
    HornBoxGlue.boxMap hi₀ hiₙ f ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) =
      HornBoxGlue.boxMap hi₀ hiₙ (f ≫ coherentNerveFunctor.map F) := by
  refine Multicofork.IsColimit.hom_ext (HornBoxGlue.diagram i hi₀ hiₙ).isColimit (fun k => ?_)
  change HornBoxGlue.inclusion i hi₀ hiₙ k ≫
      (HornBoxGlue.boxMap hi₀ hiₙ f ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))) =
    HornBoxGlue.inclusion i hi₀ hiₙ k ≫ HornBoxGlue.boxMap hi₀ hiₙ (f ≫ coherentNerveFunctor.map F)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f' => f' ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))))
      (HornBoxGlue.boxMap_face hi₀ hiₙ f k)).trans
      ((HornMapNaturality.maps_postcompose F f hi₀ hiₙ k).trans
        (HornBoxGlue.boxMap_face hi₀ hiₙ (f ≫ coherentNerveFunctor.map F) k).symm))

end CategoryTheory.CoherentRealization.HornBoxReadback
