/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOrderedMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxGlue
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaceOrderedRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedSingletonHomUnits

/-!
# Canonical enriched horn assembly from an actual Hom-box extension

An actual whole extension of the constructed original box map determines
an enriched simplex with every supplied face and every original vertex.
No Kan target is required by this assembly. The relative lifting theorem
constructs the extension from a genuine scalar fibration, rather than
assuming an enriched-filler or model-comparison outcome.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornAssembly
open SimplicialEnrichment HornBoxFaces HornHomFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
  (g : outerHom.{u} n ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))))
  (hg : (HornBoxGlue.box i hi₀ hiₙ).ι ≫ g = HornBoxGlue.boxMap hi₀ hiₙ f)

include hg in
/-- Each original positive or retained negative face reads exactly the actual supplied-horn face map. -/
private theorem face_map (x : Index.{u} i) : (face i x).ι ≫ g = maps f hi₀ hiₙ x := by
  have hI : HornBoxGlue.inclusion i hi₀ hiₙ x ≫ (HornBoxGlue.box i hi₀ hiₙ).ι = (face i x).ι :=
    SSet.Subcomplex.homOfLE_ι ((le_iSup (face i) x).trans (cover i hi₀ hiₙ).le)
  exact (congrArg (fun k => k ≫ g) hI).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => HornBoxGlue.inclusion i hi₀ hiₙ x ≫ g) (hg)).trans
        (HornBoxGlue.boxMap_face hi₀ hiₙ f x)))

include hg in
/-- Composition through every original interior vertex is the actual composition of its two supplied short Hom maps. -/
private theorem positive_comp (b : Interior.{u} n) :
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last (n + 2))) ≫ g =
      (leftMap f hi₀ hiₙ b ⊗ₘ rightMap f hi₀ hiₙ b) ≫
        eComp SSet.{u} (HornFaces.object f 0) (HornFaces.object f (HornBoxFaces.vertex b))
          (HornFaces.object f (Fin.last (n + 2))) :=
  (congrArg (fun k => k ≫ g)
    (CompositionFace.positiveIso_composition (ULift.up.{u} (0 : Fin (n + 3))) b.val (ULift.up.{u} (Fin.last
      (n + 2))))).symm.trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 3))) b.val
          (ULift.up.{u} (Fin.last (n + 2)))).hom ≫ g) (face_map f hi₀ hiₙ g hg (.inl b))).trans
            (positiveMap_readback f hi₀ hiₙ b)))

include hg in
/-- Every retained original negative face reads its actual whole supplied face Hom map at the same two outer
  vertices. -/
private theorem negative_readback (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (source_zero k)) (ULift.ext (target_last k))) ≫ g =
      HornHomFaces.retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (source_zero k)))
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f)
          (target_last k))) :=
  (congrArg (fun k => k ≫ g) (HornNegativeMaps.chart_operator k)).symm.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun g => (negativeChart k).hom ≫ g) (face_map f hi₀ hiₙ g hg (.inr ⟨k, hk⟩))).trans
        (HornBoxFaces.negativeMap_readback f k hk)))


/-- The actual whole map on every original coherent Hom, including the outer extension and empty reverse intervals. -/
private def homMap (a b : Fin (n + 3)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := by
  classical
  by_cases h : a = 0 ∧ b = Fin.last (n + 2)
  · obtain ⟨rfl, rfl⟩ := h
    exact g
  · by_cases hab : a ≤ b
    · exact HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab (by
        by_cases ha : a = 0
        · exact Or.inr (fun hb => h ⟨ha, hb⟩)
        · exact Or.inl ha)
    · exact HomUnitsAndEmpty.emptyMap (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n + 3))) ≤ ULift.up b from hab) _

/-- The actual outer pair reads exactly the supplied whole outer-Hom extension. -/
private theorem homMap_outer : homMap f hi₀ hiₙ g 0 (Fin.last (n + 2)) = g := by
  classical
  simp only [homMap, and_self, dite_eq_left True.intro]

/-- Every other ordered pair reads exactly its actual supplied endpoint-face Hom map. -/
private theorem homMap_ordered (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    homMap f hi₀ hiₙ g a b = HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab h := by
  classical
  have hN : ¬(a = 0 ∧ b = Fin.last (n + 2)) := by
    rintro ⟨ha, hb⟩
    exact h.elim (fun h => h ha) (fun h => h hb)
  simp only [homMap, dite_eq_right hN, dite_eq_left hab]

/-- The actual original Hom maps preserve the enriched identity at every individual original vertex. -/
private theorem homMap_id (a : Fin (n + 3)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫ homMap f hi₀ hiₙ g a a = eId SSet.{u}
      (HornFaces.object f a) := by
  classical
  have h : a ≠ 0 ∨ a ≠ Fin.last (n + 2) := by
    by_cases ha : a = 0
    · right
      intro hb
      have h' := congrArg Fin.val (ha.symm.trans hb)
      change 0 = n + 2 at h'
      omega
    · exact Or.inl ha
  rw [homMap_ordered f hi₀ hiₙ g a a le_rfl h]
  exact HornOrderedMaps.map_id f hi₀ hiₙ a h

include hg in
/-- All whole original Hom maps preserve enriched composition, including empty factors, the outer interval
  and both actual endpoint-unit cases. -/
private theorem homMap_comp (a b c : Fin (n + 3)) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) (SimplicialThickening.mk (ULift.up.{u} b))
        (SimplicialThickening.mk (ULift.up.{u} c)) ≫ homMap f hi₀ hiₙ g a c =
      (homMap f hi₀ hiₙ g a b ⊗ₘ homMap f hi₀ hiₙ g b c) ≫
        eComp SSet.{u} (HornFaces.object f a) (HornFaces.object f b) (HornFaces.object f c) := by
  classical
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · by_cases hN : a = 0 ∧ c = Fin.last (n + 2)
      · obtain ⟨rfl, rfl⟩ := hN
        by_cases hb₀ : b = 0
        · subst b
          exact @SingletonHomUnits.left_comp (coherentSimplex.{u} ⦋n + 2⦌) C
            (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
            (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
            (HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (0 : Fin (n + 3))))
            (homMap f hi₀ hiₙ g 0 0) (homMap f hi₀ hiₙ g 0 (Fin.last (n + 2))) (homMap_id f hi₀ hiₙ g 0)
        · by_cases hbₙ : b = Fin.last (n + 2)
          · subst b
            exact @SingletonHomUnits.right_comp (coherentSimplex.{u} ⦋n + 2⦌) C
              (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
              (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
              (HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (Fin.last (n + 2))))
              (homMap f hi₀ hiₙ g (Fin.last (n + 2)) (Fin.last (n + 2)))
              (homMap f hi₀ hiₙ g 0 (Fin.last (n + 2))) (homMap_id f hi₀ hiₙ g (Fin.last (n + 2)))
          · let bI : Interior.{u} n := ⟨ULift.up b, Fin.pos_iff_ne_zero.mpr hb₀, Fin.lt_last_iff_ne_last.mpr hbₙ⟩
            rw [homMap_outer f hi₀ hiₙ g, homMap_ordered f hi₀ hiₙ g 0 b (Fin.zero_le _) (Or.inr hbₙ),
              homMap_ordered f hi₀ hiₙ g b (Fin.last (n + 2)) (Fin.le_last _) (Or.inl hb₀)]
            exact positive_comp f hi₀ hiₙ g hg bI
      · have hac : a ≠ 0 ∨ c ≠ Fin.last (n + 2) := by
          by_cases ha : a = 0
          · exact Or.inr (fun hc => hN ⟨ha, hc⟩)
          · exact Or.inl ha
        have hab' : a ≠ 0 ∨ b ≠ Fin.last (n + 2) := by
          by_cases ha : a = 0
          · right
            intro hb
            exact hN ⟨ha, le_antisymm (Fin.le_last _) (hb ▸ hbc)⟩
          · exact Or.inl ha
        have hbc' : b ≠ 0 ∨ c ≠ Fin.last (n + 2) := by
          by_cases hc : c = Fin.last (n + 2)
          · left
            intro hb
            exact hN ⟨le_antisymm (hb ▸ hab) (Fin.zero_le _), hc⟩
          · exact Or.inr hc
        rw [homMap_ordered f hi₀ hiₙ g a c (hab.trans hbc) hac,
          homMap_ordered f hi₀ hiₙ g a b hab hab', homMap_ordered f hi₀ hiₙ g b c hbc hbc']
        exact HornOrderedMaps.map_comp f hi₀ hiₙ a b c hab hbc hac hab' hbc'
    · apply SSet.hom_ext
      intro q
      apply ConcreteCategory.hom_ext
      rintro ⟨p₀, p₁⟩
      exact False.elim (hbc (show b ≤ c from HomUnitsAndEmpty.source_order (a := ULift.up.{u} b) (b :=
        ULift.up.{u} c) p₁))
  · apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    rintro ⟨p₀, p₁⟩
    exact False.elim (hab (show a ≤ b from HomUnitsAndEmpty.source_order (a := ULift.up.{u} a) (b :=
      ULift.up.{u} b) p₀))

/-- The actual enriched simplex assembled from the proved whole Hom maps, preserving every individual
  original vertex. -/
def simplex (hg : (HornBoxGlue.box i hi₀ hiₙ).ι ≫ g = HornBoxGlue.boxMap hi₀ hiₙ f) : coherentSimplex.{u} ⦋n
    + 2⦌ ⟶ C where
  obj a := HornFaces.object f a.as.down
  map a b := homMap f hi₀ hiₙ g a.as.down b.as.down
  map_id a := homMap_id f hi₀ hiₙ g a.as.down
  map_comp a b c := homMap_comp f hi₀ hiₙ g hg a.as.down b.as.down c.as.down

/-- The assembled enriched simplex has exactly the supplied original vertex at every original label. -/
theorem simplex_obj (a : Fin (n + 3)) : (simplex f hi₀ hiₙ g hg).obj (.mk (ULift.up a)) = HornFaces.object f a := rfl



include hg in
private theorem outer_restriction (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1)))) ≫
      homMap f hi₀ hiₙ g ((HornBoxFaces.vertex k).succAbove 0)
        ((HornBoxFaces.vertex k).succAbove (Fin.last (n + 1))) =
      HornHomFaces.faceMap f (HornBoxFaces.vertex k) hk
        (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1)))) := by
  let E := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let F := HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk
  let a := (HornBoxFaces.vertex k).succAbove (0 : Fin (n + 2))
  let b := (HornBoxFaces.vertex k).succAbove (Fin.last (n + 1))
  let X := nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))
  let Z := HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))
  let S : X ⟶ outerHom.{u} n := eqToHom (congrArg₂ (fun a b : Fin (n + 3) => nerve
    (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)))
    (source_zero k) (target_last k))
  let T : (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) ⟶ Z := eqToHom (congrArg₂ (fun x y : C =>
    x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k)))
  let M : X ⟶ (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := homMap f hi₀ hiₙ g a b
  let N : outerHom.{u} n ⟶ Z := homMap f hi₀ hiₙ g 0 (Fin.last (n + 2))
  let e : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} (Fin.last (n + 1)))) ⟶ X :=
    E.map (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
  let R : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} (Fin.last (n +
    1)))) ⟶ (HornFaces.object f a ⟶[SSet.{u}] HornFaces.object f b) := HornHomFaces.faceMap f (HornBoxFaces.vertex k) hk
    (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
  have hN : M ≫ T = S ≫ N :=
    eqToHom_naturality
      (f := fun p : Fin (n + 3) × Fin (n + 3) => nerve (SimplicialThickening.Path (ULift.up.{u} p.1)
        (ULift.up.{u} p.2)))
      (g := fun p : Fin (n + 3) × Fin (n + 3) => HornFaces.object f p.1 ⟶[SSet.{u}] HornFaces.object f p.2)
      (fun p => homMap f hi₀ hiₙ g p.1 p.2)
      (show (a, b) = ((0 : Fin (n + 3)), Fin.last (n + 2)) from Prod.ext (source_zero k) (target_last k))
  apply (cancel_mono T).mp
  let Q := retargetMap F (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (source_zero k)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _).trans (congrArg (HornFaces.object f) (target_last k)))
  have hO : e ≫ S ≫ N = Q :=
    (congrArg (fun g : outerHom.{u} n ⟶ Z => e ≫ S ≫ g) (homMap_outer f hi₀ hiₙ g)).trans
      (negative_readback f hi₀ hiₙ g hg k hk)
  have hL : (e ≫ M) ≫ T = Q :=
    (Category.assoc e M T).trans ((congrArg (fun g : X ⟶ Z => e ≫ g) hN).trans hO)
  have hR : R ≫ T = Q :=
    HomRetargetAlgebra.target_trans F (.mk (ULift.up.{u} (0 : Fin (n + 2)))) (.mk (ULift.up.{u} (Fin.last (n + 1))))
      (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk _) (HornFaces.faceFunctor_obj f
        (HornBoxFaces.vertex k) hk _)
      (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k))
  exact hL.trans hR.symm

include hg in
/-- Every original supplied face reads back its entire actual Hom map in the assembled simplex, including
  reverse intervals and the outer pair. -/
private theorem hom_restriction (k : Fin (n + 3)) (hk : k ≠ i) (a b : Fin (n + 2)) :
    (coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
      homMap f hi₀ hiₙ g (k.succAbove a) (k.succAbove b) =
      HornHomFaces.faceMap f k hk (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) := by
  classical
  by_cases hab : a ≤ b
  · by_cases hN : k.succAbove a = 0 ∧ k.succAbove b = Fin.last (n + 2)
    · have hk₀ : k ≠ 0 := by
        intro h
        subst k
        have h' : (0 : Fin (n + 3)).succAbove a ≠ 0 := by rw [Fin.succAbove_zero]; exact Fin.succ_ne_zero a
        exact h' hN.1
      have hkₙ : k ≠ Fin.last (n + 2) := by
        intro h
        subst k
        have h' : (Fin.last (n + 2)).succAbove b ≠ Fin.last (n + 2) := by
          rw [Fin.succAbove_last]; exact ne_of_lt (Fin.castSucc_lt_last b)
        exact h' hN.2
      have ha : a = 0 := (Fin.succAboveOrderEmb k).injective (hN.1.trans (Fin.succAbove_ne_zero_zero hk₀).symm)
      have hb : b = Fin.last (n + 1) := (Fin.succAboveOrderEmb k).injective (hN.2.trans
        (Fin.succAbove_ne_last_last hkₙ).symm)
      subst a
      subst b
      let kI : Interior.{u} n := ⟨ULift.up k, Fin.pos_iff_ne_zero.mpr hk₀, Fin.lt_last_iff_ne_last.mpr hkₙ⟩
      exact outer_restriction f hi₀ hiₙ g hg kI hk
    · have h : k.succAbove a ≠ 0 ∨ k.succAbove b ≠ Fin.last (n + 2) := by
        by_cases ha : k.succAbove a = 0
        · exact Or.inr (fun hb => hN ⟨ha, hb⟩)
        · exact Or.inl ha
      rw [homMap_ordered f hi₀ hiₙ g (k.succAbove a) (k.succAbove b) ((Fin.succAboveOrderEmb k).monotone hab) h]
      exact HornFaceOrderedRestriction.restriction f hi₀ hiₙ k hk a b hab h
  · exact HomUnitsAndEmpty.empty_hom_ext
      (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n + 2))) ≤ ULift.up b from hab) _ _

/-- The actual assembled enriched simplex restricts to every supplied original coherent face as a whole
  enriched functor. -/
theorem simplex_face (k : Fin (n + 3)) (hk : k ≠ i) :
    coherentSimplexMap (SimplexCategory.δ k) ≫ simplex f hi₀ hiₙ g hg = HornFaces.faceFunctor f k hk := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := coherentSimplexMap (SimplexCategory.δ k) ≫ simplex f hi₀ hiₙ g hg)
    (G := HornFaces.faceFunctor f k hk) (fun a => (HornFaces.faceFunctor_obj f k hk a).symm) ?_
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  let T := eqToIso (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (HornFaces.faceFunctor_obj f k hk (.mk (ULift.up.{u} a)))
    (HornFaces.faceFunctor_obj f k hk (.mk (ULift.up.{u} b))))
  change ((coherentSimplexMap (SimplexCategory.δ k)).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b)) ≫
    homMap f hi₀ hiₙ g (k.succAbove a) (k.succAbove b)) ≫ T.inv =
      (HornFaces.faceFunctor f k hk).map (.mk (ULift.up.{u} a)) (.mk (ULift.up.{u} b))
  exact (Iso.comp_inv_eq T).mpr (hom_restriction f hi₀ hiₙ g hg k hk a b)

/-- The canonical assembled simplex has precisely the supplied whole outer Hom extension. -/
theorem simplex_outer_map :
    (simplex f hi₀ hiₙ g hg).map (.mk (ULift.up (0 : Fin (n + 3))))
      (.mk (ULift.up (Fin.last (n + 2)))) = g := homMap_outer f hi₀ hiₙ g

/-- Every other ordered Hom is precisely the original supplied-face Hom map. -/
theorem simplex_ordered_map (a b : Fin (n + 3)) (hab : a ≤ b)
    (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    (simplex f hi₀ hiₙ g hg).map (.mk (ULift.up a)) (.mk (ULift.up b)) =
      HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab h := homMap_ordered f hi₀ hiₙ g a b hab h

end CategoryTheory.CoherentRealization.HornAssembly
