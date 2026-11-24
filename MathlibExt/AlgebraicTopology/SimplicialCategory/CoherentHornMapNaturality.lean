/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxGlue

/-!
# Whole strict-map naturality of original coherent horn Hom data

The supplied original horn, all original endpoint labels and every
positive/negative box map follow the actual enriched functor. These
equations retain the entire target maps needed for relative lifting,
without a Kan or enriched-model hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornMapNaturality
open SimplicialEnrichment

/-- Retargeting an original Hom map commutes with actual enriched postcomposition. -/
theorem retargetMap_postcompose {A C D : Carrier.{u}} (G : A ⟶ C) (F : C ⟶ D)
    (a b : A) {x y : C} (hx : G.obj a = x) (hy : G.obj b = y) :
    HornHomFaces.retargetMap G a b hx hy ≫ F.map x y =
      HornHomFaces.retargetMap (G ≫ F) a b (congrArg F.obj hx) (congrArg F.obj hy) := by
  have h := enriched_map_reindex F hx hy
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => G.map a b ≫ t) h).trans (Category.assoc _ _ _).symm)

variable {C D : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (F : C ⟶ D) (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- Every individual original horn vertex follows the same enriched object map. -/
theorem object_map (t : Fin (n + 3)) :
    HornFaces.object (f ≫ coherentNerveFunctor.map F) t = F.obj (HornFaces.object f t) := rfl

/-- Every entire supplied original face functor follows the same enriched postcomposition. -/
theorem faceFunctor_map (j : Fin (n + 3)) (hj : j ≠ i) :
    HornFaces.faceFunctor (f ≫ coherentNerveFunctor.map F) j hj =
      HornFaces.faceFunctor f j hj ≫ F := rfl

/-- The whole original face Hom map follows the same actual enriched map at its original endpoints. -/
theorem faceMap_postcompose (j : Fin (n + 3)) (hj : j ≠ i)
    (a b : coherentSimplex.{u} ⦋n + 1⦌) :
    HornHomFaces.faceMap f j hj a b ≫
        F.map (HornFaces.object f (j.succAbove a.as.down)) (HornFaces.object f (j.succAbove b.as.down)) =
      HornHomFaces.faceMap (f ≫ coherentNerveFunctor.map F) j hj a b :=
  retargetMap_postcompose (HornFaces.faceFunctor f j hj) F a b
    (HornFaces.faceFunctor_obj f j hj a) (HornFaces.faceFunctor_obj f j hj b)

/-- Outside-face Hom extraction follows the same strict map with both original interval endpoints retained. -/
theorem outside_faceMap_postcompose (j : Fin (n + 3)) (hj : j ≠ i)
    (a' b' : ULift.{u} (Fin (n + 2)))
    (h : (ULift.up j : ULift.{u} (Fin (n + 3))) < (OrdinalFace.embedding j) a' ∨
      (OrdinalFace.embedding j) b' < ULift.up j)
    {a b : Fin (n + 3)} (ha : j.succAbove a'.down = a) (hb : j.succAbove b'.down = b) :
    HornOutsideIntervals.faceMap f j hj a' b' h ha hb ≫ F.map (HornFaces.object f a) (HornFaces.object f b) =
      HornOutsideIntervals.faceMap (f ≫ coherentNerveFunctor.map F) j hj a' b' h ha hb := by
  subst a
  subst b
  change (𝟙 _ ≫ (IntervalFaceCover.outsideIso j a' b' h).inv ≫
      HornHomFaces.faceMap f j hj (.mk a') (.mk b') ≫ 𝟙 _) ≫ F.map _ _ =
    𝟙 _ ≫ (IntervalFaceCover.outsideIso j a' b' h).inv ≫
      HornHomFaces.faceMap (f ≫ coherentNerveFunctor.map F) j hj (.mk a') (.mk b') ≫ 𝟙 _
  simp only [Category.id_comp]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g => (IntervalFaceCover.outsideIso j a' b' h).inv ≫ g)
      (faceMap_postcompose F f j hj (.mk a') (.mk b')))

/-- Each whole nonexceptional ordered Hom follows actual enriched postcomposition. -/
theorem outside_homMap_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    HornOutsideIntervals.homMap f hi₀ hiₙ a b hab h ≫ F.map (HornFaces.object f a) (HornFaces.object f b) =
      HornOutsideIntervals.homMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ a b hab h := by
  classical
  unfold HornOutsideIntervals.homMap
  split_ifs with ha
  · exact outside_faceMap_postcompose F f _ _ _ _ _ _ _
  · exact outside_faceMap_postcompose F f _ _ _ _ _ _ _

/-- The whole supplied left short Hom follows the same original enriched map. -/
theorem leftMap_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b : HornBoxFaces.Interior.{u} n) :
    HornBoxFaces.leftMap f hi₀ hiₙ b ≫ F.map (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex b)) =
      HornBoxFaces.leftMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ b :=
  outside_homMap_postcompose F f hi₀ hiₙ 0 (HornBoxFaces.vertex b) (Fin.zero_le _)
    (Or.inr (HornBoxFaces.vertex_ne_last b))

/-- The whole supplied right short Hom follows the same original enriched map. -/
theorem rightMap_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b : HornBoxFaces.Interior.{u} n) :
    HornBoxFaces.rightMap f hi₀ hiₙ b ≫ F.map (HornFaces.object f (HornBoxFaces.vertex b)) (HornFaces.object
      f (Fin.last (n + 2))) =
      HornBoxFaces.rightMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ b :=
  outside_homMap_postcompose F f hi₀ hiₙ (HornBoxFaces.vertex b) (Fin.last (n + 2)) (Fin.le_last _)
    (Or.inl (HornBoxFaces.vertex_ne_zero b))

/-- Every retained negative face follows the whole original enriched map, including its endpoint transports. -/
theorem negativeMap_postcompose (k : HornBoxFaces.Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    HornBoxFaces.negativeMap f k hk ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) =
      HornBoxFaces.negativeMap (f ≫ coherentNerveFunctor.map F) k hk := by
  have h := retargetMap_postcompose (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk) F
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
      (congrArg (HornFaces.object f) (HornBoxFaces.source_zero k)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans
      (congrArg (HornFaces.object f) (HornBoxFaces.target_last k)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g => (HornBoxFaces.negativeChart k).inv ≫ g) h)

/-- Every whole positive composition face follows the same enriched functor's actual composition law. -/
theorem positiveMap_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b : HornBoxFaces.Interior.{u} n) :
    HornBoxFaces.positiveMap f hi₀ hiₙ b ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) =
      HornBoxFaces.positiveMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ b := by
  let x := HornFaces.object f 0
  let y := HornFaces.object f (HornBoxFaces.vertex b)
  let z := HornFaces.object f (Fin.last (n + 2))
  let L := HornBoxFaces.leftMap f hi₀ hiₙ b
  let R := HornBoxFaces.rightMap f hi₀ hiₙ b
  let L' := HornBoxFaces.leftMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ b
  let R' := HornBoxFaces.rightMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ b
  let E := CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val
    (ULift.up (Fin.last (n + 2)))
  have hL : L ≫ F.map x y = L' := leftMap_postcompose F f hi₀ hiₙ b
  have hR : R ≫ F.map y z = R' := rightMap_postcompose F f hi₀ hiₙ b
  have hComp := F.map_comp x y z
  have hLR : (L ⊗ₘ R) ≫ (F.map x y ⊗ₘ F.map y z) = L' ⊗ₘ R' :=
    (tensorHom_comp_tensorHom L R (F.map x y) (F.map y z)).trans
      (congrArg₂ (fun L R => L ⊗ₘ R) hL hR)
  change (E.inv ≫ (L ⊗ₘ R) ≫ eComp SSet.{u} x y z) ≫ F.map x z =
    E.inv ≫ (L' ⊗ₘ R') ≫ eComp SSet.{u} (F.obj x) (F.obj y) (F.obj z)
  have hM : ((L ⊗ₘ R) ≫ eComp SSet.{u} x y z) ≫ F.map x z =
      (L' ⊗ₘ R') ≫ eComp SSet.{u} (F.obj x) (F.obj y) (F.obj z) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f' => (L ⊗ₘ R) ≫ f') hComp).trans
        ((Category.assoc (L ⊗ₘ R) (F.map x y ⊗ₘ F.map y z)
          (eComp SSet.{u} (F.obj x) (F.obj y) (F.obj z))).symm.trans
          (congrArg (fun f' => f' ≫ eComp SSet.{u} (F.obj x) (F.obj y) (F.obj z)) hLR)))
  exact (Category.assoc E.inv ((L ⊗ₘ R) ≫ eComp SSet.{u} x y z) (F.map x z)).trans
    (congrArg (fun f' => E.inv ≫ f') hM)

/-- The entire family used in the original Hom-box colimit follows the same actual strict map. -/
theorem maps_postcompose (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (k : HornBoxFaces.Index.{u} i) :
    HornBoxFaces.maps f hi₀ hiₙ k ≫ F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) =
      HornBoxFaces.maps (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ k := by
  rcases k with b | k
  · exact positiveMap_postcompose F f hi₀ hiₙ b
  · exact negativeMap_postcompose F f k.val k.property

end CategoryTheory.CoherentRealization.HornMapNaturality
