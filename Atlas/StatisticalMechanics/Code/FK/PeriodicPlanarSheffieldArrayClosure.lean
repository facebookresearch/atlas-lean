/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly










open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

@[simp] theorem horizontalShift_zero_vector : horizontalShift 0 = 0 := by
  funext i
  fin_cases i <;> simp

@[simp] theorem verticalShift_zero_vector : verticalShift 0 = 0 := by
  funext i
  fin_cases i <;> simp

omit [Countable V] in



theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_union_source
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (S T side : Set V) :
    E.rectSideConnectionEvent a b c d (S ∪ T) side =
      E.rectSideConnectionEvent a b c d S side ∪
        E.rectSideConnectionEvent a b c d T side := by
  ext omega
  constructor
  · rintro ⟨x, hx, hxInfinite, y, hy, hxy⟩
    rcases hx with hxS | hxT
    · exact Or.inl ⟨x, hxS, hxInfinite, y, hy, hxy⟩
    · exact Or.inr ⟨x, hxT, hxInfinite, y, hy, hxy⟩
  · rintro (hS | hT)
    · obtain ⟨x, hx, hxInfinite, y, hy, hxy⟩ := hS
      exact ⟨x, Or.inl hx, hxInfinite, y, hy, hxy⟩
    · obtain ⟨x, hx, hxInfinite, y, hy, hxy⟩ := hT
      exact ⟨x, Or.inr hx, hxInfinite, y, hy, hxy⟩

omit [Countable V] in


theorem PeriodicGraph.fourShiftTemplate_add
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop t : Site 2) :
    P.fourShiftTemplate S (zLeft + t) (zRight + t)
        (zBottom + t) (zTop + t) =
      (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift t) := by
  ext x
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
      (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩))
    · exact ⟨P.shift zLeft u, Or.inl (Or.inl ⟨u, hu, rfl⟩),
        (P.shift_add zLeft t u).symm⟩
    · exact ⟨P.shift zRight u, Or.inl (Or.inr ⟨u, hu, rfl⟩),
        (P.shift_add zRight t u).symm⟩
    · exact ⟨P.shift zBottom u, Or.inr (Or.inl ⟨u, hu, rfl⟩),
        (P.shift_add zBottom t u).symm⟩
    · exact ⟨P.shift zTop u, Or.inr (Or.inr ⟨u, hu, rfl⟩),
        (P.shift_add zTop t u).symm⟩
  · rintro ⟨y, ((⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) |
        (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)), rfl⟩
    · exact Or.inl (Or.inl ⟨u, hu, by
        exact P.shift_add zLeft t u⟩)
    · exact Or.inl (Or.inr ⟨u, hu, by
        exact P.shift_add zRight t u⟩)
    · exact Or.inr (Or.inl ⟨u, hu, by
        exact P.shift_add zBottom t u⟩)
    · exact Or.inr (Or.inr ⟨u, hu, by
        exact P.shift_add zTop t u⟩)

omit [Countable V] in
theorem PeriodicGraph.fourShiftTemplate_add_image
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop t w : Site 2) :
    (P.fourShiftTemplate S (zLeft + t) (zRight + t)
        (zBottom + t) (zTop + t)).image (P.shift w) =
      (P.fourShiftTemplate S zLeft zRight zBottom zTop).image
        (P.shift (t + w)) := by
  rw [P.fourShiftTemplate_add, Finset.image_image]
  congr 1
  funext x
  exact (P.shift_add t w x).symm



theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_rectangle
    (E : PeriodicPlaneEmbedding P)
    {a b c d a' b' c' d' : Real} (L R : Finset V)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    E.rectanglePairMergeErrorUnion a' b' c' d' L R ⊆
      E.rectanglePairMergeErrorUnion a b c d L R := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hinfinite, hnotLarge⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  simp only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
    Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨x, hxL, y, hyR, hinfinite, ?_⟩
  intro hsmall
  exact hnotLarge (P.connectedWithinSet_mono_region
    (E.rectVertices_mono ha hb hc hd) x y hsmall)



theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' c' d' : Real} (L R : Finset V)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectanglePairMergeErrorUnion a' b' c' d' L R) ≤
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) :=
  measureReal_mono
    (E.rectanglePairMergeErrorUnion_mono_rectangle L R ha hb hc hd)



theorem PeriodicPlaneEmbedding.rectBottomConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hb : b ≤ b') (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c d' (template : Set V)
        (E.rectBottomBoundaryVertices a' b' c d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectBottomConnectionEvent_mono_otherBounds
    (component : Set V) ha hb hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))



theorem PeriodicPlaneEmbedding.rectTopConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' b' c' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b' c' d (template : Set V)
        (E.rectTopBoundaryVertices a' b' c' d)) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectTopConnectionEvent_mono_otherBounds
    (component : Set V) ha hb hc).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))



theorem PeriodicPlaneEmbedding.rectLeftConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d b' c' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (hb : b ≤ b') (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b' c' d' (template : Set V)
        (E.rectLeftBoundaryVertices a b' c' d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectLeftConnectionEvent_mono_otherBounds
    (component : Set V) hb hc hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))



theorem PeriodicPlaneEmbedding.rectRightConnection_component_le_template_of_enlarge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d a' c' d' : Real} (component template : Finset V)
    (hcomponent : component ⊆ template)
    (ha : a' ≤ a) (hc : c' ≤ c) (hd : d ≤ d') :
    mu.real (E.rectSideConnectionEvent a b c d (component : Set V)
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a' b c' d' (template : Set V)
        (E.rectRightBoundaryVertices a' b c' d')) := by
  apply measureReal_mono (h₂ := measure_ne_top mu _)
  exact (E.rectRightConnectionEvent_mono_otherBounds
    (component : Set V) ha hc hd).trans
      (E.rectSideConnectionEvent_mono_source (by exact_mod_cast hcomponent))





theorem PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (aBottom bBottom dBottom aTop bTop cTop : Real)
    (aMerge bMerge cMerge dMerge : Real)
    (hBottomA : a ≤ aBottom) (hBottomB : bBottom ≤ b)
    (hBottomD : dBottom ≤ d)
    (hTopA : a ≤ aTop) (hTopB : bTop ≤ b) (hTopC : c ≤ cTop)
    (hMergeA : a ≤ aMerge) (hMergeB : bMerge ≤ b)
    (hMergeC : c ≤ cMerge) (hMergeD : dMerge ≤ d) :
    mu.real (E.rectSideConnectionEvent
        aBottom bBottom c dBottom (L : Set V)
        (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) *
      mu.real (E.rectSideConnectionEvent
        aTop bTop cTop d (R : Set V)
        (E.rectTopBoundaryVertices aTop bTop cTop d)) -
      mu.real (E.rectanglePairMergeErrorUnion
        aMerge bMerge cMerge dMerge L R) ≤
        mu.real (E.verticalCrossingEvent a b c d) := by
  have hBottom : mu.real (E.rectSideConnectionEvent
      aBottom bBottom c dBottom (L : Set V)
      (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectBottomConnectionEvent_mono_otherBounds
        (L : Set V) hBottomA hBottomB hBottomD)
  have hTop : mu.real (E.rectSideConnectionEvent
      aTop bTop cTop d (R : Set V)
      (E.rectTopBoundaryVertices aTop bTop cTop d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectTopConnectionEvent_mono_otherBounds
        (R : Set V) hTopA hTopB hTopC)
  have hMerge :=
    E.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
      mu L R hMergeA hMergeB hMergeC hMergeD
  have hProduct :
      mu.real (E.rectSideConnectionEvent
          aBottom bBottom c dBottom (L : Set V)
          (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)) *
        mu.real (E.rectSideConnectionEvent
          aTop bTop cTop d (R : Set V)
          (E.rectTopBoundaryVertices aTop bTop cTop d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectBottomBoundaryVertices a b c d)) *
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectTopBoundaryVertices a b c d)) :=
    mul_le_mul hBottom hTop measureReal_nonneg measureReal_nonneg
  calc
    _ ≤ mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectBottomBoundaryVertices a b c d)) *
          mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
            (E.rectTopBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) := by
      linarith
    _ ≤ mu.real (E.verticalCrossingEvent a b c d) :=
      E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG a b c d L R


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (bLeft cLeft dLeft aRight cRight dRight : Real)
    (aMerge bMerge cMerge dMerge : Real)
    (hLeftB : bLeft ≤ b) (hLeftC : c ≤ cLeft) (hLeftD : dLeft ≤ d)
    (hRightA : a ≤ aRight) (hRightC : c ≤ cRight)
    (hRightD : dRight ≤ d)
    (hMergeA : a ≤ aMerge) (hMergeB : bMerge ≤ b)
    (hMergeC : c ≤ cMerge) (hMergeD : dMerge ≤ d) :
    mu.real (E.rectSideConnectionEvent
        a bLeft cLeft dLeft (L : Set V)
        (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) *
      mu.real (E.rectSideConnectionEvent
        aRight b cRight dRight (R : Set V)
        (E.rectRightBoundaryVertices aRight b cRight dRight)) -
      mu.real (E.rectanglePairMergeErrorUnion
        aMerge bMerge cMerge dMerge L R) ≤
        mu.real (E.horizontalCrossingEvent a b c d) := by
  have hLeft : mu.real (E.rectSideConnectionEvent
      a bLeft cLeft dLeft (L : Set V)
      (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectLeftConnectionEvent_mono_otherBounds
        (L : Set V) hLeftB hLeftC hLeftD)
  have hRight : mu.real (E.rectSideConnectionEvent
      aRight b cRight dRight (R : Set V)
      (E.rectRightBoundaryVertices aRight b cRight dRight)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) :=
    measureReal_mono (h₂ := measure_ne_top mu _)
      (E.rectRightConnectionEvent_mono_otherBounds
        (R : Set V) hRightA hRightC hRightD)
  have hMerge :=
    E.rectanglePairMergeErrorUnion_measureReal_mono_rectangle
      mu L R hMergeA hMergeB hMergeC hMergeD
  have hProduct :
      mu.real (E.rectSideConnectionEvent
          a bLeft cLeft dLeft (L : Set V)
          (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)) *
        mu.real (E.rectSideConnectionEvent
          aRight b cRight dRight (R : Set V)
          (E.rectRightBoundaryVertices aRight b cRight dRight)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectLeftBoundaryVertices a b c d)) *
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
          (E.rectRightBoundaryVertices a b c d)) :=
    mul_le_mul hLeft hRight measureReal_nonneg measureReal_nonneg
  calc
    _ ≤ mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
            (E.rectLeftBoundaryVertices a b c d)) *
          mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
            (E.rectRightBoundaryVertices a b c d)) -
          mu.real (E.rectanglePairMergeErrorUnion a b c d L R) := by
      linarith
    _ ≤ mu.real (E.horizontalCrossingEvent a b c d) :=
      E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG a b c d L R




theorem PeriodicPlaneEmbedding.verticalCrossing_ge_carriedComponents_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d a' b' : Real) (bottom top : Finset V) (radius : Nat)
    (ha : a' ≤ a) (hb : b ≤ b')
    (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices a' b' c d) :
    mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V)
        (E.rectBottomBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (top : Set V)
        (E.rectTopBoundaryVertices a b c d)) -
      mu.real (P.pairMergeErrorUnion bottom top radius) ≤
        mu.real (E.verticalCrossingEvent a' b' c d) := by
  have hrectangle := E.verticalCrossing_ge_carriedComponents mu hFKG
    a' b' c d bottom top a b d a b c a' b' c d
    ha hb le_rfl ha hb le_rfl le_rfl le_rfl le_rfl le_rfl
  have hmerge := E.rectanglePairMergeErrorUnion_measureReal_le
    mu a' b' c d bottom top radius hbox
  linarith




theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_carriedComponents_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d c' d' : Real) (left right : Finset V) (radius : Nat)
    (hc : c' ≤ c) (hd : d ≤ d')
    (hbox : (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices a b c' d') :
    mu.real (E.rectSideConnectionEvent a b c d (left : Set V)
        (E.rectLeftBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (right : Set V)
        (E.rectRightBoundaryVertices a b c d)) -
      mu.real (P.pairMergeErrorUnion left right radius) ≤
        mu.real (E.horizontalCrossingEvent a b c' d') := by
  have hrectangle := E.horizontalCrossing_ge_carriedComponents mu hFKG
    a b c' d' left right b c d a c d a b c' d'
    le_rfl hc hd le_rfl hc hd le_rfl le_rfl le_rfl le_rfl
  have hmerge := E.rectanglePairMergeErrorUnion_measureReal_le
    mu a b c' d' left right radius hbox
  linarith


theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d a' b' : Nat → Real)
    (bottom top : Nat → Finset V) (radius : Nat → Nat)
    (ha : ∀ n, a' n ≤ a n) (hb : ∀ n, b n ≤ b' n)
    (hbox : ∀ n,
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (a' n) (b' n) (c n) (d n))
    (hbottom : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (bottom n : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (htop : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (top n : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (P.pairMergeErrorUnion (bottom n) (top n) (radius n)))
      atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n)))
      atTop (nhds 1) := by
  have hlower (n : Nat) :=
    E.verticalCrossing_ge_carriedComponents_of_connector mu hFKG
      (a n) (b n) (c n) (d n) (a' n) (b' n)
      (bottom n) (top n) (radius n) (ha n) (hb n) (hbox n)
  have hlimit := hbottom.mul htop |>.sub hmerge
  have hlimit' : Tendsto (fun n ↦
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (bottom n : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) *
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (top n : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) -
        mu.real (P.pairMergeErrorUnion (bottom n) (top n) (radius n)))
      atTop (nhds 1) := by
    convert hlimit using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlimit' tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)


theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_carriedComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d c' d' : Nat → Real)
    (left right : Nat → Finset V) (radius : Nat → Nat)
    (hc : ∀ n, c' n ≤ c n) (hd : ∀ n, d n ≤ d' n)
    (hbox : ∀ n,
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
        E.rectVertices (a n) (b n) (c' n) (d' n))
    (hleft : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (left n : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hright : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (right n : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (P.pairMergeErrorUnion (left n) (right n) (radius n)))
      atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n)))
      atTop (nhds 1) := by
  have hlower (n : Nat) :=
    E.horizontalCrossing_ge_carriedComponents_of_connector mu hFKG
      (a n) (b n) (c n) (d n) (c' n) (d' n)
      (left n) (right n) (radius n) (hc n) (hd n) (hbox n)
  have hlimit := hleft.mul hright |>.sub hmerge
  have hlimit' : Tendsto (fun n ↦
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (left n : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) *
        mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          (right n : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) -
        mu.real (P.pairMergeErrorUnion (left n) (right n) (radius n)))
      atTop (nhds 1) := by
    convert hlimit using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlimit' tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)




structure PeriodicPlaneEmbedding.CarriedCrossNestedArray
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  a : Nat → Real
  b : Nat → Real
  c : Nat → Real
  d : Nat → Real
  aWide : Nat → Real
  bWide : Nat → Real
  cTall : Nat → Real
  dTall : Nat → Real
  bottom : Nat → Finset V
  top : Nat → Finset V
  left : Nat → Finset V
  right : Nat → Finset V
  verticalRadius : Nat → Nat
  horizontalRadius : Nat → Nat
  wideLeft : ∀ n, aWide n ≤ a n
  wideRight : ∀ n, b n ≤ bWide n
  tallBottom : ∀ n, cTall n ≤ c n
  tallTop : ∀ n, d n ≤ dTall n
  verticalConnector : ∀ n,
    (P.orbitBox (P.bufferedRadius (verticalRadius n)) : Set V) ⊆
      E.rectVertices (aWide n) (bWide n) (c n) (d n)
  horizontalConnector : ∀ n,
    (P.orbitBox (P.bufferedRadius (horizontalRadius n)) : Set V) ⊆
      E.rectVertices (a n) (b n) (cTall n) (dTall n)
  bottomLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (bottom n : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  topLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (top n : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  leftLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (left n : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  rightLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (right n : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  verticalMergeLimit : Tendsto (fun n ↦ mu.real
    (P.pairMergeErrorUnion (bottom n) (top n) (verticalRadius n)))
    atTop (nhds 0)
  horizontalMergeLimit : Tendsto (fun n ↦ mu.real
    (P.pairMergeErrorUnion (left n) (right n) (horizontalRadius n)))
    atTop (nhds 0)

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.verticalCrossingLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent
      (data.aWide n) (data.bWide n) (data.c n) (data.d n)))
      atTop (nhds 1) :=
  E.verticalCrossing_tendsto_one_of_carriedComponents mu hFKG
    data.a data.b data.c data.d data.aWide data.bWide
    data.bottom data.top data.verticalRadius data.wideLeft data.wideRight
    data.verticalConnector data.bottomLimit data.topLimit
    data.verticalMergeLimit

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.horizontalCrossingLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent
      (data.a n) (data.b n) (data.cTall n) (data.dTall n)))
      atTop (nhds 1) :=
  E.horizontalCrossing_tendsto_one_of_carriedComponents mu hFKG
    data.a data.b data.c data.d data.cTall data.dTall
    data.left data.right data.horizontalRadius data.tallBottom data.tallTop
    data.horizontalConnector data.leftLimit data.rightLimit
    data.horizontalMergeLimit

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.crossingMaxLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ max
      (mu.real (E.horizontalCrossingEvent
        (data.a n) (data.b n) (data.cTall n) (data.dTall n)))
      (mu.real (E.verticalCrossingEvent
        (data.aWide n) (data.bWide n) (data.c n) (data.d n))))
      atTop (nhds 1) := by
  simpa only [max_self] using
    (data.horizontalCrossingLimit E mu hFKG).max
      (data.verticalCrossingLimit E mu hFKG)



def PeriodicGraph.fourBoundaryComponentTemplate
    (P : PeriodicGraph V)
    (bottom top left right : Finset V) : Finset V :=
  (bottom ∪ top) ∪ (left ∪ right)

omit [Countable V] in
theorem PeriodicGraph.bottom_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    bottom ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.top_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    top ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.left_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    left ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]

omit [Countable V] in
theorem PeriodicGraph.right_subset_fourBoundaryComponentTemplate
    (P : PeriodicGraph V) (bottom top left right : Finset V) :
    right ⊆ P.fourBoundaryComponentTemplate bottom top left right := by
  intro x hx
  simp [PeriodicGraph.fourBoundaryComponentTemplate, hx]




theorem PeriodicPlaneEmbedding.exists_sharedBoundaryComponentTemplate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (p a b c d : Real)
    (bottom top left right : Finset V)
    (aBottom bBottom dBottom aTop bTop cTop : Real)
    (bLeft cLeft dLeft aRight cRight dRight : Real)
    (hBottomSource : (bottom : Set V) ⊆
      E.rectVertices aBottom bBottom c dBottom)
    (hTopSource : (top : Set V) ⊆
      E.rectVertices aTop bTop cTop d)
    (hLeftSource : (left : Set V) ⊆
      E.rectVertices a bLeft cLeft dLeft)
    (hRightSource : (right : Set V) ⊆
      E.rectVertices aRight b cRight dRight)
    (hBottomScore : p < mu.real (E.rectSideConnectionEvent
      aBottom bBottom c dBottom (bottom : Set V)
      (E.rectBottomBoundaryVertices aBottom bBottom c dBottom)))
    (hTopScore : p < mu.real (E.rectSideConnectionEvent
      aTop bTop cTop d (top : Set V)
      (E.rectTopBoundaryVertices aTop bTop cTop d)))
    (hLeftScore : p < mu.real (E.rectSideConnectionEvent
      a bLeft cLeft dLeft (left : Set V)
      (E.rectLeftBoundaryVertices a bLeft cLeft dLeft)))
    (hRightScore : p < mu.real (E.rectSideConnectionEvent
      aRight b cRight dRight (right : Set V)
      (E.rectRightBoundaryVertices aRight b cRight dRight)))
    (hBottomA : a ≤ aBottom) (hBottomB : bBottom ≤ b)
    (hBottomD : dBottom ≤ d)
    (hTopA : a ≤ aTop) (hTopB : bTop ≤ b) (hTopC : c ≤ cTop)
    (hLeftB : bLeft ≤ b) (hLeftC : c ≤ cLeft) (hLeftD : dLeft ≤ d)
    (hRightA : a ≤ aRight) (hRightC : c ≤ cRight)
    (hRightD : dRight ≤ d) :
    let template := P.fourBoundaryComponentTemplate bottom top left right
    (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  dsimp only
  let template := P.fourBoundaryComponentTemplate bottom top left right
  have hBottomCommon : (bottom : Set V) ⊆ E.rectVertices a b c d :=
    hBottomSource.trans (E.rectVertices_mono hBottomA hBottomB le_rfl hBottomD)
  have hTopCommon : (top : Set V) ⊆ E.rectVertices a b c d :=
    hTopSource.trans (E.rectVertices_mono hTopA hTopB hTopC le_rfl)
  have hLeftCommon : (left : Set V) ⊆ E.rectVertices a b c d :=
    hLeftSource.trans (E.rectVertices_mono le_rfl hLeftB hLeftC hLeftD)
  have hRightCommon : (right : Set V) ⊆ E.rectVertices a b c d :=
    hRightSource.trans (E.rectVertices_mono hRightA le_rfl hRightC hRightD)
  have htemplate : (template : Set V) ⊆ E.rectVertices a b c d := by
    intro x hx
    simp only [template, PeriodicGraph.fourBoundaryComponentTemplate,
      Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact hBottomCommon hx
    · exact hTopCommon hx
    · exact hLeftCommon hx
    · exact hRightCommon hx
  have hBottom := E.rectBottomConnection_component_le_template_of_enlarge
    (c := c) mu bottom template (P.bottom_subset_fourBoundaryComponentTemplate
      bottom top left right) hBottomA hBottomB hBottomD
  have hTop := E.rectTopConnection_component_le_template_of_enlarge
    (d := d) mu top template (P.top_subset_fourBoundaryComponentTemplate
      bottom top left right) hTopA hTopB hTopC
  have hLeft := E.rectLeftConnection_component_le_template_of_enlarge
    (a := a) mu left template (P.left_subset_fourBoundaryComponentTemplate
      bottom top left right) hLeftB hLeftC hLeftD
  have hRight := E.rectRightConnection_component_le_template_of_enlarge
    (b := b) mu right template (P.right_subset_fourBoundaryComponentTemplate
      bottom top left right) hRightA hRightC hRightD
  exact ⟨htemplate, hBottomScore.trans_le hBottom,
    hTopScore.trans_le hTop, hLeftScore.trans_le hLeft,
    hRightScore.trans_le hRight⟩





theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_endpointSources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b0 - a0)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b0 - a0)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d0 - c0)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d0 - c0)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b1 - a1)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b1 - a1)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d1 - c1)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d1 - c1) :
    ∃ bottomSource topSource leftSource rightSource : Finset V,
      (bottomSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧
      p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0
        (bottomSource : Set V) (E.rectBottomBoundaryVertices a0 b0 c0 d0)) ∧
      (topSource : Set V) ⊆ E.rectVertices a0 b0 c0 d0 ∧
      p < mu.real (E.rectSideConnectionEvent a0 b0 c0 d0
        (topSource : Set V) (E.rectTopBoundaryVertices a0 b0 c0 d0)) ∧
      (leftSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧
      p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1
        (leftSource : Set V) (E.rectLeftBoundaryVertices a1 b1 c1 d1)) ∧
      (rightSource : Set V) ⊆ E.rectVertices a1 b1 c1 d1 ∧
      p < mu.real (E.rectSideConnectionEvent a1 b1 c1 d1
        (rightSource : Set V) (E.rectRightBoundaryVertices a1 b1 c1 d1)) := by
  let verticalSeed := family.seed E verticalMargin
  let horizontalSeed := family.seed E horizontalMargin
  let zBottom : Site 2 :=
    horizontalShift (a0 + family.radiusBottom verticalMargin) + verticalShift c0
  let zTop : Site 2 :=
    horizontalShift (a0 + family.radiusTop verticalMargin) + verticalShift d0
  let zLeft : Site 2 :=
    horizontalShift a1 + verticalShift (c1 + family.radiusLeft horizontalMargin)
  let zRight : Site 2 :=
    horizontalShift b1 + verticalShift (c1 + family.radiusRight horizontalMargin)
  let bottomSource : Finset V :=
    (S.image (P.shift (family.baseBottom + verticalShift 0))).image
      (P.shift zBottom)
  let topSource : Finset V :=
    (S.image (P.shift (family.baseTop + verticalShift 0))).image
      (P.shift zTop)
  let leftSource : Finset V :=
    (S.image (P.shift (family.baseLeft + horizontalShift 0))).image
      (P.shift zLeft)
  let rightSource : Finset V :=
    (S.image (P.shift (family.baseRight + horizontalShift 0))).image
      (P.shift zRight)
  have hbottom := verticalSeed.bottom_translate_to_rect E mu hTI
    (0 : Fin (verticalMargin + 1)) zBottom (a0 : Real) (b0 : Real) (d0 : Real)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, add_zero]
      change (family.radiusBottom verticalMargin : Real) +
          ((a0 : Real) + family.radiusBottom verticalMargin) ≤ (b0 : Real)
      have hw : a0 + (family.radiusBottom verticalMargin : Int) +
          family.radiusBottom verticalMargin ≤ b0 := by omega
      have hwR : (a0 : Real) + family.radiusBottom verticalMargin +
          family.radiusBottom verticalMargin ≤ b0 := by exact_mod_cast hw
      linarith)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom]
      simp only [horizontalShift_one_apply, Int.cast_zero, add_zero,
        Int.cast_natCast, Pi.add_apply, verticalShift_one_apply,
        Int.cast_add, zero_add]
      have hh : (c0 : Real) + family.radiusBottom verticalMargin ≤ d0 := by
        exact_mod_cast (by omega : c0 +
          (family.radiusBottom verticalMargin : Int) ≤ d0)
      simpa [add_comm] using hh)
  have htop := verticalSeed.top_translate_to_rect E mu hTI
    (0 : Fin (verticalMargin + 1)) zTop (a0 : Real) (b0 : Real) (c0 : Real)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, add_zero]
      have hw : a0 + (family.radiusTop verticalMargin : Int) +
          family.radiusTop verticalMargin ≤ b0 := by omega
      have hwR : (a0 : Real) + family.radiusTop verticalMargin +
          family.radiusTop verticalMargin ≤ b0 := by exact_mod_cast hw
      linarith)
    (by
      dsimp only [verticalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : (c0 : Real) ≤ d0 - family.radiusTop verticalMargin := by
        exact_mod_cast (by omega : c0 ≤ d0 -
          (family.radiusTop verticalMargin : Int))
      linarith)
  have hleft := horizontalSeed.left_translate_to_rect E mu hTI
    (0 : Fin (horizontalMargin + 1)) zLeft (b1 : Real) (c1 : Real) (d1 : Real)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_zero, add_zero]
      have hw : (a1 : Real) + family.radiusLeft horizontalMargin ≤ b1 := by
        exact_mod_cast (by omega : a1 +
          (family.radiusLeft horizontalMargin : Int) ≤ b1)
      linarith)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : c1 + (family.radiusLeft horizontalMargin : Int) +
          family.radiusLeft horizontalMargin ≤ d1 := by omega
      have hhR : (c1 : Real) + family.radiusLeft horizontalMargin +
          family.radiusLeft horizontalMargin ≤ d1 := by exact_mod_cast hh
      linarith)
  have hright := horizontalSeed.right_translate_to_rect E mu hTI
    (0 : Fin (horizontalMargin + 1)) zRight (a1 : Real) (c1 : Real) (d1 : Real)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp only [Pi.add_apply, horizontalShift_zero_apply,
        verticalShift_zero_apply, Int.cast_add, Int.cast_zero, add_zero]
      have hw : (a1 : Real) ≤ b1 - family.radiusRight horizontalMargin := by
        exact_mod_cast (by omega : a1 ≤ b1 -
          (family.radiusRight horizontalMargin : Int))
      linarith)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp)
    (by
      dsimp only [horizontalSeed,
        PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight]
      simp only [Pi.add_apply, horizontalShift_one_apply,
        verticalShift_one_apply, Int.cast_add, Int.cast_natCast,
        Int.cast_zero, zero_add]
      have hh : c1 + (family.radiusRight horizontalMargin : Int) +
          family.radiusRight horizontalMargin ≤ d1 := by omega
      have hhR : (c1 : Real) + family.radiusRight horizontalMargin +
          family.radiusRight horizontalMargin ≤ d1 := by exact_mod_cast hh
      linarith)
  refine ⟨bottomSource, topSource, leftSource, rightSource, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [bottomSource, topSource, leftSource, rightSource,
      Finset.coe_image] at ⊢
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom] using hbottom.1
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zBottom] using hbottom.2
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop] using htop.1
  · simpa [verticalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zTop] using htop.2
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft] using hleft.1
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zLeft] using hleft.2
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight] using hright.1
  · simpa [horizontalSeed,
      PeriodicPlaneEmbedding.NormalBoundaryBandFamily.seed, zRight] using hright.2




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointTemplate
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat) (a b c d : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
    ∃ bottom top left right : Finset V,
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  obtain ⟨bottom, top, left, right, hbottomSource, hbottomScore,
      htopSource, htopScore, hleftSource, hleftScore,
      hrightSource, hrightScore⟩ :=
    family.exists_endpointSources E mu hTI verticalMargin horizontalMargin
      a b c d a b c d hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  refine ⟨bottom, top, left, right, ?_⟩
  exact E.exists_sharedBoundaryComponentTemplate mu p a b c d
    bottom top left right a b d a b c b c d a c d
    hbottomSource htopSource hleftSource hrightSource
    hbottomScore htopScore hleftScore hrightScore
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_sharedEndpointComponents
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalMargin horizontalMargin : Nat) (a b c d : Int)
    (hbottomWidth : 2 * (family.radiusBottom verticalMargin : Int) ≤ b - a)
    (htopWidth : 2 * (family.radiusTop verticalMargin : Int) ≤ b - a)
    (hbottomHeight : (family.radiusBottom verticalMargin : Int) ≤ d - c)
    (htopHeight : (family.radiusTop verticalMargin : Int) ≤ d - c)
    (hleftWidth : (family.radiusLeft horizontalMargin : Int) ≤ b - a)
    (hrightWidth : (family.radiusRight horizontalMargin : Int) ≤ b - a)
    (hleftHeight : 2 * (family.radiusLeft horizontalMargin : Int) ≤ d - c)
    (hrightHeight : 2 * (family.radiusRight horizontalMargin : Int) ≤ d - c) :
    ∃ bottom top left right : Finset V,
      (bottom : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (bottom : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      (top : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (top : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      (left : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (left : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      (right : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (right : Set V)
        (E.rectRightBoundaryVertices a b c d)) ∧
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices a b c d ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectTopBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ∧
      p < mu.real (E.rectSideConnectionEvent a b c d (template : Set V)
        (E.rectRightBoundaryVertices a b c d)) := by
  obtain ⟨bottom, top, left, right, hbottomSource, hbottomScore,
      htopSource, htopScore, hleftSource, hleftScore,
      hrightSource, hrightScore⟩ :=
    family.exists_endpointSources E mu hTI verticalMargin horizontalMargin
      a b c d a b c d hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  have hshared := E.exists_sharedBoundaryComponentTemplate mu p a b c d
    bottom top left right a b d a b c b c d a c d
    hbottomSource htopSource hleftSource hrightSource
    hbottomScore htopScore hleftScore hrightScore
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
  exact ⟨bottom, top, left, right,
    hbottomSource, hbottomScore, htopSource, htopScore,
    hleftSource, hleftScore, hrightSource, hrightScore, hshared⟩





theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.commonBoundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (horizontalMargin verticalMargin width height : Nat)
    (hleftBottom : (family.radiusLeft horizontalMargin : Int) +
      family.baseLeft 1 ≤ family.baseBottom 1 + verticalMargin)
    (hrightBottom : (family.radiusRight horizontalMargin : Int) +
      family.baseRight 1 ≤ family.baseBottom 1 + verticalMargin)
    (hleftTop : (family.radiusLeft horizontalMargin : Int) +
      family.baseTop 1 ≤ family.baseLeft 1 + verticalMargin)
    (hrightTop : (family.radiusRight horizontalMargin : Int) +
      family.baseTop 1 ≤ family.baseRight 1 + verticalMargin)
    (hbottomLeft : (family.radiusBottom verticalMargin : Int) +
      family.baseBottom 0 ≤ family.baseLeft 0 + horizontalMargin)
    (htopLeft : (family.radiusTop verticalMargin : Int) +
      family.baseTop 0 ≤ family.baseLeft 0 + horizontalMargin)
    (hbottomRight : (family.radiusBottom verticalMargin : Int) +
      family.baseRight 0 ≤ family.baseBottom 0 + horizontalMargin)
    (htopRight : (family.radiusTop verticalMargin : Int) +
      family.baseRight 0 ≤ family.baseTop 0 + horizontalMargin) :
    let gridBase : Site 2 := fun i ↦ if i = 0 then
      family.baseLeft 0 + horizontalMargin
    else family.baseBottom 1 + verticalMargin
    let b : Int := gridBase 0 + width -
      (family.baseRight 0 - horizontalMargin)
    let d : Int := gridBase 1 + height -
      (family.baseTop 1 - verticalMargin)
    ((family.radiusLeft horizontalMargin : Int) ≤ b) →
    ((family.radiusRight horizontalMargin : Int) ≤ b) →
    ((family.radiusBottom verticalMargin : Int) ≤ d) →
    ((family.radiusTop verticalMargin : Int) ≤ d) →
    (0 : Real) ≤ b ∧ (0 : Real) ≤ d ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (i, (0 : Fin (height + 1)))) '' (S : Set V))
        (E.rectBottomBoundaryVertices 0 b 0 d))) ∧
    (∀ i : Fin (width + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (i, Fin.last height)) '' (S : Set V))
        (E.rectTopBoundaryVertices 0 b 0 d))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          ((0 : Fin (width + 1)), j)) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 b 0 d))) ∧
    (∀ j : Fin (height + 1), p < mu.real
      (E.rectSideConnectionEvent 0 b 0 d
        (P.shift (gridBase + preferenceGridSite
          (Fin.last width, j)) '' (S : Set V))
        (E.rectRightBoundaryVertices 0 b 0 d))) := by
  dsimp only
  intro hbLeft hbRight hdBottom hdTop
  let gridBase : Site 2 := fun i ↦ if i = 0 then
    family.baseLeft 0 + horizontalMargin
  else family.baseBottom 1 + verticalMargin
  let b : Int := gridBase 0 + width -
    (family.baseRight 0 - horizontalMargin)
  let d : Int := gridBase 1 + height -
    (family.baseTop 1 - verticalMargin)
  have hmixed := family.mixedBoundaryScores E mu hTI
    horizontalMargin verticalMargin width height hleftBottom hrightBottom
    hbLeft hbRight hdBottom hdTop
  let bottomLower : Int := gridBase 0 - family.baseBottom 0 -
    family.radiusBottom verticalMargin
  let topLower : Int := gridBase 0 - family.baseTop 0 -
    family.radiusTop verticalMargin
  let bottomUpper : Int := gridBase 0 + width - family.baseBottom 0 +
    family.radiusBottom verticalMargin
  let topUpper : Int := gridBase 0 + width - family.baseTop 0 +
    family.radiusTop verticalMargin
  let leftUpper : Int := gridBase 1 + height - family.baseLeft 1 +
    family.radiusLeft horizontalMargin
  let rightUpper : Int := gridBase 1 + height - family.baseRight 1 +
    family.radiusRight horizontalMargin
  have hbottomLower : 0 ≤ bottomLower := by
    dsimp only [bottomLower, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have htopLower : 0 ≤ topLower := by
    dsimp only [topLower, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have hbottomUpper : bottomUpper ≤ b := by
    dsimp only [bottomUpper, b, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have htopUpper : topUpper ≤ b := by
    dsimp only [topUpper, b, gridBase]
    simp only [if_pos, Fin.isValue]
    omega
  have hleftUpper : leftUpper ≤ d := by
    dsimp only [leftUpper, d, gridBase]
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  have hrightUpper : rightUpper ≤ d := by
    dsimp only [rightUpper, d, gridBase]
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    omega
  have ha : min 0 (min bottomLower topLower) = 0 := by
    simp [min_eq_left, hbottomLower, htopLower]
  have hb : max b (max bottomUpper topUpper) = b := by
    simp [max_eq_left, hbottomUpper, htopUpper]
  have hd : max d (max leftUpper rightUpper) = d := by
    simp [max_eq_left, hleftUpper, hrightUpper]
  have hb0 : (0 : Real) ≤ b := by
    have hr : (0 : Int) ≤ family.radiusLeft horizontalMargin := by omega
    exact_mod_cast hr.trans hbLeft
  have hd0 : (0 : Real) ≤ d := by
    have hr : (0 : Int) ≤ family.radiusBottom verticalMargin := by omega
    exact_mod_cast hr.trans hdBottom
  dsimp only [gridBase, b, d, bottomLower, topLower, bottomUpper,
    topUpper, leftUpper, rightUpper] at ha hb hd
  rw [ha, hb, hd] at hmixed
  refine ⟨hb0, hd0, ?_, ?_, ?_, ?_⟩
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.2.1
  · simpa only [gridBase, b, d, Int.cast_zero] using hmixed.2.2.2.2



theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.bottomBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : v.2.val ≤ margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let j : Fin (margin + 1) := ⟨v.2.val, by omega⟩
  let t : Site 2 := verticalShift j.val
  have hle := E.rectBottomConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.1
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite
            (v.1, (0 : Fin (height + 1))))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext k
    fin_cases k <;> simp [t, j, preferenceGridSite]
  rw [htarget] at hle
  have hscore := (data.bottom j).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zBottom + t)) : Set V)
      (E.rectBottomBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle



theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.topBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : height ≤ v.2.val + margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let k : Fin (margin + 1) := ⟨height - v.2.val, by omega⟩
  let t : Site 2 := verticalShift (-(k.val : Int))
  have hle := E.rectTopConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.1
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite (v.1, Fin.last height))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, k, preferenceGridSite] <;> omega
  rw [htarget] at hle
  have hscore := (data.top k).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zTop + t)) : Set V)
      (E.rectTopBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle



theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.leftBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : v.1.val ≤ margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let i : Fin (margin + 1) := ⟨v.1.val, by omega⟩
  let t : Site 2 := horizontalShift i.val
  have hle := E.rectLeftConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.2
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite
            ((0 : Fin (width + 1)), v.2))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, i, preferenceGridSite]
  rw [htarget] at hle
  have hscore := (data.left i).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zLeft + t)) : Set V)
      (E.rectLeftBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle



theorem PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.rightBandScore
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {margin M : Nat} {p : Real}
    (data : E.CommonSquareNormalBoundaryBandData mu S margin M p)
    (width height : Nat) (v : PreferenceGridVertex width height)
    (hv : width ≤ v.1.val + margin) :
    p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M + width : Real)
      (-(M : Real)) (M + height : Real)
      ((P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
        (P.shift (preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real))) := by
  let k : Fin (margin + 1) := ⟨width - v.1.val, by omega⟩
  let t : Site 2 := horizontalShift (-(k.val : Int))
  have hle := E.rectRightConnection_fourShiftTemplate_le mu hTI
    M width height S (data.zLeft + t) (data.zRight + t)
      (data.zBottom + t) (data.zTop + t) v.2
  have htarget :
      (P.fourShiftTemplate S (data.zLeft + t) (data.zRight + t)
          (data.zBottom + t) (data.zTop + t)).image
          (P.shift (preferenceGridSite (Fin.last width, v.2))) =
        (P.fourShiftTemplate S data.zLeft data.zRight data.zBottom data.zTop).image
          (P.shift (preferenceGridSite v)) := by
    rw [P.fourShiftTemplate_add_image]
    congr 2
    apply congrArg P.shift
    funext q
    fin_cases q <;> simp [t, k, preferenceGridSite] <;> omega
  rw [htarget] at hle
  have hscore := (data.right k).2
  have hscore' : p < mu.real (E.rectSideConnectionEvent
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift (data.zRight + t)) : Set V)
      (E.rectRightBoundaryVertices (-(M : Real)) (M : Real)
        (-(M : Real)) (M : Real))) := by
    simpa only [Finset.coe_image, t] using hscore
  exact hscore'.trans_le hle





theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_commonBoundaryBandScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (squareRequirement margin width height : Nat) :
    ∃ M, ∃ data : E.CommonSquareNormalBoundaryBandData mu S margin M p,
      squareRequirement ≤ M ∧
      (let template := P.fourShiftTemplate S data.zLeft data.zRight
        data.zBottom data.zTop
      (∀ v : PreferenceGridVertex width height,
        (template.image (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)) ∧
      (∀ v : PreferenceGridVertex width height, v.2.val ≤ margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height,
        height ≤ v.2.val + margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height, v.1.val ≤ margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real)))) ∧
      (∀ v : PreferenceGridVertex width height,
        width ≤ v.1.val + margin →
        p < mu.real (E.rectSideConnectionEvent
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real)
          (template.image (P.shift (preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (-(M : Real)) (M + width : Real)
            (-(M : Real)) (M + height : Real))))) := by
  let seed := family.seed E margin
  let M := max squareRequirement (max (max seed.radiusLeft seed.radiusRight)
    (max seed.radiusBottom seed.radiusTop))
  have hrequirement : squareRequirement ≤ M := Nat.le_max_left _ _
  have hleft : seed.radiusLeft ≤ M :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _)).trans
      (Nat.le_max_right _ _)
  have hright : seed.radiusRight ≤ M :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _)).trans
      (Nat.le_max_right _ _)
  have hbottom : seed.radiusBottom ≤ M :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)
  have htop : seed.radiusTop ≤ M :=
    ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)
  let data := seed.toCommonSquare E mu hTI M hleft hright hbottom htop
  refine ⟨M, data, hrequirement, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    apply E.fourShiftTemplate_preferenceGrid_subset_rect
      M width height S data.zLeft data.zRight data.zBottom data.zTop
    · simpa [Finset.coe_image, horizontalShift] using
        (data.left (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, horizontalShift] using
        (data.right (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, verticalShift] using
        (data.bottom (0 : Fin (margin + 1))).1
    · simpa [Finset.coe_image, verticalShift] using
        (data.top (0 : Fin (margin + 1))).1
  · intro v hv
    exact data.bottomBandScore E mu hTI width height v hv
  · intro v hv
    exact data.topBandScore E mu hTI width height v hv
  · intro v hv
    exact data.leftBandScore E mu hTI width height v hv
  · intro v hv
    exact data.rightBandScore E mu hTI width height v hv



def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.fullVerticalRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (h : Nat) : Nat :=
  max
    (max
      (((family.radiusLeft h : Int) + family.baseLeft 1 -
        family.baseBottom 1).toNat)
      (((family.radiusRight h : Int) + family.baseRight 1 -
        family.baseBottom 1).toNat))
    (max
      (((family.radiusLeft h : Int) + family.baseTop 1 -
        family.baseLeft 1).toNat)
      (((family.radiusRight h : Int) + family.baseTop 1 -
        family.baseRight 1).toNat))



def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.fullHorizontalRequirement
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (v : Nat) : Nat :=
  max
    (max
      (((family.radiusBottom v : Int) + family.baseBottom 0 -
        family.baseLeft 0).toNat)
      (((family.radiusTop v : Int) + family.baseTop 0 -
        family.baseLeft 0).toNat))
    (max
      (((family.radiusBottom v : Int) + family.baseRight 0 -
        family.baseBottom 0).toNat)
      (((family.radiusTop v : Int) + family.baseRight 0 -
        family.baseTop 0).toNat))

private theorem int_le_nat_of_toNat_le_array {x : Int} {n : Nat}
    (h : x.toNat ≤ n) : x ≤ n := by
  by_cases hx : 0 ≤ x
  · have h' : (x.toNat : Int) ≤ (n : Int) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hx] at h'
  · omega




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences
      family.fullVerticalRequirement family.fullHorizontalRequirement
  refine ⟨horizontal, vertical, hh, hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hhv n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hhv n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hhv n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hhv n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hvh n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hvh n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hvh n)
    have hle' := (Nat.le_max_left _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hvh n)
    have hle' := (Nat.le_max_right _ _).trans hle
    have := int_le_nat_of_toNat_le_array hle'
    omega




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins_with_requirements
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
      (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) := by
  let verticalStep : Nat → Nat := fun h ↦
    max (family.horizontalRadiusRequirement E h) (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦
    max (family.verticalRadiusRequirement E v) (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  refine ⟨horizontal, vertical, hh, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (Nat.le_max_right _ _).trans (hhv n)
  · intro n
    exact (Nat.le_max_right _ _).trans (hvh n)
  · intro n
    have hreq : family.horizontalRadiusRequirement E (horizontal n) ≤
        vertical n := (Nat.le_max_left _ _).trans (hhv n)
    have hle : (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_left _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.horizontalRadiusRequirement E (horizontal n) ≤
        vertical n := (Nat.le_max_left _ _).trans (hhv n)
    have hle : (((family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 - family.baseBottom 1).toNat) ≤ vertical n :=
      (Nat.le_max_right _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.verticalRadiusRequirement E (vertical n) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
    have hle : (((family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega
  · intro n
    have hreq : family.verticalRadiusRequirement E (vertical n) ≤
        horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
    have hle : (((family.radiusTop (vertical n) : Int) +
        family.baseTop 0 - family.baseLeft 0).toNat) ≤
        horizontal (n + 1) := (Nat.le_max_right _ _).trans hreq
    have := int_le_nat_of_toNat_le_array hle
    omega




theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_requirements
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
      (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  let verticalStep : Nat → Nat := fun h ↦
    max (family.fullVerticalRequirement E h) (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦
    max (family.fullHorizontalRequirement E v) (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  have hV (n : Nat) : family.fullVerticalRequirement E (horizontal n) ≤
      vertical n := (Nat.le_max_left _ _).trans (hhv n)
  have hH (n : Nat) : family.fullHorizontalRequirement E (vertical n) ≤
      horizontal (n + 1) := (Nat.le_max_left _ _).trans (hvh n)
  refine ⟨horizontal, vertical, hh, hv,
    fun n ↦ (Nat.le_max_right _ _).trans (hhv n),
    fun n ↦ (Nat.le_max_right _ _).trans (hvh n),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left
      (max
        (((family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 -
          family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) + family.baseRight 1 -
          family.baseBottom 1).toNat)) _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hV n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_left _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_left _ _).trans hle)
    omega
  · intro n
    have hle := (Nat.le_max_right _ _).trans (hH n)
    have := int_le_nat_of_toNat_le_array ((Nat.le_max_right _ _).trans hle)
    omega



noncomputable def PeriodicPlaneEmbedding.connectorMarginRequirement
    (E : PeriodicPlaneEmbedding P) (radius : Nat) : Nat :=
  Nat.ceil (max
    (E.orbitBoxCoordinateBound (P.bufferedRadius radius) 0)
    (E.orbitBoxCoordinateBound (P.bufferedRadius radius) 1))

theorem PeriodicPlaneEmbedding.orbitBoxCoordinateBound_le_connectorMarginRequirement
    (E : PeriodicPlaneEmbedding P) (radius : Nat) (i : Fin 2) :
    E.orbitBoxCoordinateBound (P.bufferedRadius radius) i ≤
      E.connectorMarginRequirement radius := by
  rw [PeriodicPlaneEmbedding.connectorMarginRequirement]
  apply le_trans _ (Nat.le_ceil _)
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem PeriodicPlaneEmbedding.orbitBox_subset_connectorMarginSquare
    (E : PeriodicPlaneEmbedding P) (radius : Nat) :
    (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆
      E.rectVertices (-(E.connectorMarginRequirement radius : Real))
        (E.connectorMarginRequirement radius)
        (-(E.connectorMarginRequirement radius : Real))
        (E.connectorMarginRequirement radius) := by
  intro v hv
  have hv0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
  have hv1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
  have h0 := E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 0
  have h1 := E.orbitBoxCoordinateBound_le_connectorMarginRequirement radius 1
  rw [abs_le] at hv0 hv1
  exact ⟨by linarith [hv0.1, h0], hv0.2.trans h0,
    by linarith [hv1.1, h1], hv1.2.trans h1⟩



theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_fullAlternatingMargins_with_connector
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p) (radius : Nat) :
    ∃ horizontal vertical : Nat → Nat,
      Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
      (∀ n, E.connectorMarginRequirement radius ≤ vertical n) ∧
      (∀ n, E.connectorMarginRequirement radius ≤ horizontal (n + 1)) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
      (∀ n, (family.radiusLeft (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
      (∀ n, (family.radiusRight (horizontal n) : Int) +
        family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusBottom (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
      (∀ n, (family.radiusTop (vertical n) : Int) +
        family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1)) := by
  simpa only using family.exists_fullAlternatingMargins_with_requirements E
    (fun _ ↦ E.connectorMarginRequirement radius)
    (fun _ ↦ E.connectorMarginRequirement radius)


def PeriodicPlaneEmbedding.NormalBoundaryBandFamily.AlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) : Prop :=
  ∃ horizontal vertical : Nat → Nat,
    Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧
    (∀ n, verticalRequirement (horizontal n) ≤ vertical n) ∧
    (∀ n, horizontalRequirement (vertical n) ≤ horizontal (n + 1)) ∧
    (∀ n, (family.radiusLeft (horizontal n) : Int) +
      family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧
    (∀ n, (family.radiusRight (horizontal n) : Int) +
      family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧
    (∀ n, (family.radiusLeft (horizontal n) : Int) +
      family.baseTop 1 ≤ family.baseLeft 1 + vertical n) ∧
    (∀ n, (family.radiusRight (horizontal n) : Int) +
      family.baseTop 1 ≤ family.baseRight 1 + vertical n) ∧
    (∀ n, (family.radiusBottom (vertical n) : Int) +
      family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusTop (vertical n) : Int) +
      family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusBottom (vertical n) : Int) +
      family.baseRight 0 ≤ family.baseBottom 0 + horizontal (n + 1)) ∧
    (∀ n, (family.radiusTop (vertical n) : Int) +
      family.baseRight 0 ≤ family.baseTop 0 + horizontal (n + 1))

theorem PeriodicPlaneEmbedding.NormalBoundaryBandFamily.alignedMarginSchedule
    (E : PeriodicPlaneEmbedding P)
    {mu : Measure (ConfigSpace (Sym2 V))} {S : Finset V} {p : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    family.AlignedMarginSchedule E verticalRequirement horizontalRequirement :=
  family.exists_fullAlternatingMargins_with_requirements E
    verticalRequirement horizontalRequirement



theorem PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      Tendsto p atTop (nhds 1) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h ↦ h.1
  let delta : Nat → Real := fun m ↦ 1 / (m + 1 : Real)
  let p : Nat → Real := fun m ↦
    (mu.real (P.orbitBoxHitsInfinite m)) ^ 2 - delta m
  have hfamily (m : Nat) : Nonempty
      (E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)) := by
    simpa only [p, delta, PeriodicGraph.setHitsInfinite_orbitBox] using
      E.exists_orbitBox_normalBoundaryBandFamily
        mu hFKG hTI hunique m (by positivity : 0 < delta m)
  let family : ∀ m,
      E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m) :=
    fun m ↦ Classical.choice (hfamily m)
  refine ⟨p, family, ?_⟩
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hdelta : Tendsto delta atTop (nhds 0) := by
    simpa only [delta] using tendsto_one_div_add_atTop_nhds_zero_nat
  convert (hhit.pow 2).sub hdelta using 1 <;> norm_num [p]





theorem PeriodicPlaneEmbedding.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (radius : Nat → Nat) :
    ∃ (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      Tendsto p atTop (nhds 1) ∧
      ∀ m, (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  obtain ⟨p, family, hp⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies mu hFKG hTI hunique
  refine ⟨p, family, hp, ?_⟩
  intro m
  exact (family m).alignedMarginSchedule E
    (fun _ ↦ E.connectorMarginRequirement (radius m))
    (fun _ ↦ E.connectorMarginRequirement (radius m))



def PeriodicPlaneEmbedding.UniformBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (radius : Nat → Nat) : Prop :=
  ∀ (width height margin : Nat → Nat)
    (base : Nat → Site 2) (a b c d p : Nat → Real),
    (∀ n, 2 * margin n < width n) →
    (∀ n, 2 * margin n < height n) →
    (∀ n, p n ≤ 1) → Tendsto p atTop (nhds 1) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      margin n ≤ v.1.val → v.1.val + margin n < width n →
      margin n ≤ v.2.val → v.2.val + margin n < height n →
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      v.2.val ≤ margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      height n ≤ v.2.val + margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      v.1.val ≤ margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      width n ≤ v.1.val + margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
    Tendsto (fun n ↦ max
      (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
      atTop (nhds 1)


def PeriodicPlaneEmbedding.UniformTemplateBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (template : Nat → Finset V)
    (radius : Nat → Nat) : Prop :=
  ∀ (width height margin : Nat → Nat)
    (base : Nat → Site 2) (a b c d p : Nat → Real),
    (∀ n, 2 * margin n < width n) →
    (∀ n, 2 * margin n < height n) →
    (∀ n, p n ≤ 1) → Tendsto p atTop (nhds 1) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      margin n ≤ v.1.val → v.1.val + margin n < width n →
      margin n ≤ v.2.val → v.2.val + margin n < height n →
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
          E.rectVertices (a n) (b n) (c n) (d n)) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      v.2.val ≤ margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      height n ≤ v.2.val + margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      v.1.val ≤ margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
    (∀ n (v : PreferenceGridVertex (width n) (height n)),
      width n ≤ v.1.val + margin n → p n ≤ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
    Tendsto (fun n ↦ max
      (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
      atTop (nhds 1)



theorem PeriodicPlaneEmbedding.exists_uniformTemplateBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n ↦
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius, E.UniformTemplateBoundaryBandCrossingRadius
      mu template radius := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat → Real := fun n ↦ 1 - p n
  let bottom : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v ↦
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v ↦
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n ↦ (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal
    a b c d epsilon bottom top left right hepsilon
  · exact fun n ↦ sub_nonneg.mpr (hp n)
  · exact hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hheightSep n) hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hwidthSep n) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h ↦ hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h ↦ htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h ↦ hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h ↦ hright n v h) (le_refl _) hv



theorem PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_cofinalConnectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ (radius : Nat → Nat) (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      E.UniformBoundaryBandCrossingRadius mu radius ∧
      Tendsto p atTop (nhds 1) ∧
      ∀ m, (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
      mu hFKG hTI hunique
  obtain ⟨p, family, hp, hschedule⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
      mu hFKG hTI hunique radius
  exact ⟨radius, p, family, hradius, hp, hschedule⟩



theorem PeriodicPlaneEmbedding.exists_alignedActiveSide_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) := by
  have hev : ∀ᶠ m in atTop, 1 - epsilon < p m :=
    (tendsto_order.1 hp).1 (1 - epsilon) (by linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hev
  let m := max cutoff threshold
  refine ⟨m, Nat.le_max_left _ _, hthreshold m (Nat.le_max_right _ _), ?_⟩
  exact (family m).alignedMarginSchedule E
    (verticalRequirement m) (horizontalRequirement m)



theorem PeriodicPlaneEmbedding.exists_uniformRadius_alignedActiveSide_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1)) (radius : Nat → Nat)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  exact E.exists_alignedActiveSide_choice mu S p family hp
    (fun m _ ↦ E.connectorMarginRequirement (radius m))
    (fun m _ ↦ E.connectorMarginRequirement (radius m))
    cutoff hepsilon




theorem PeriodicGraph.exists_commonBoundaryPairMergeRadius
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (bottom top left right : Finset V) (cutoff : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius, cutoff ≤ radius ∧
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon ∧
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon := by
  have hvertical : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique bottom top)).2 epsilon hepsilon
  have hhorizontal : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique left right)).2 epsilon hepsilon
  obtain ⟨verticalCutoff, hverticalCutoff⟩ := eventually_atTop.1 hvertical
  obtain ⟨horizontalCutoff, hhorizontalCutoff⟩ :=
    eventually_atTop.1 hhorizontal
  let radius := max cutoff (max verticalCutoff horizontalCutoff)
  refine ⟨radius, Nat.le_max_left _ _, ?_, ?_⟩
  · exact hverticalCutoff radius
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  · exact hhorizontalCutoff radius
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))




theorem PeriodicPlaneEmbedding.exists_alignedSharedLevel_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scaleCutoff : Nat) (connectorRadius : Nat → Nat) {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    ∃ m extent : Nat, ∃ bottom top left right : Finset V,
      scaleCutoff ≤ m ∧
      1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) ∧
      (P.orbitBox (P.bufferedRadius (connectorRadius m)) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent ∧
      (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (bottom : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (top : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (left : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (right : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) := by
  obtain ⟨m, hm, hpm, hschedule⟩ := E.exists_alignedActiveSide_choice
    mu S p family hp verticalRequirement horizontalRequirement
      scaleCutoff hepsilon
  have hschedule' := hschedule
  obtain ⟨horizontal, vertical, _hh, _hv, _hvr, _hhr,
      _hLB, _hRB, _hLT, _hRT, _hBL, _hTL, _hBR, _hTR⟩ := hschedule
  let horizontalMargin := horizontal 0
  let verticalMargin := vertical 0
  obtain ⟨coordinateCutoff, hcoordinateCutoff⟩ := exists_nat_ge
    (max
      (E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 0)
      (E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 1))
  let extent := coordinateCutoff +
    2 * (family m).radiusBottom verticalMargin +
    2 * (family m).radiusTop verticalMargin +
    2 * (family m).radiusLeft horizontalMargin +
    2 * (family m).radiusRight horizontalMargin + 1
  have hcoordinateCutoffExtent : coordinateCutoff ≤ extent := by
    dsimp only [extent]
    omega
  have hcoordinateZero :
      E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 0 ≤
        (extent : Real) :=
    (le_max_left _ _).trans <| hcoordinateCutoff.trans <| by
      exact_mod_cast hcoordinateCutoffExtent
  have hcoordinateOne :
      E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 1 ≤
        (extent : Real) :=
    (le_max_right _ _).trans <| hcoordinateCutoff.trans <| by
      exact_mod_cast hcoordinateCutoffExtent
  have hconnector :
      (P.orbitBox (P.bufferedRadius (connectorRadius m)) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent := by
    intro v hv
    have hv0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
    have hv1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
    rw [abs_le] at hv0 hv1
    exact ⟨by linarith [hv0.1, hcoordinateZero],
      hv0.2.trans hcoordinateZero,
      by linarith [hv1.1, hcoordinateOne],
      hv1.2.trans hcoordinateOne⟩
  have hbottomWidth :
      2 * ((family m).radiusBottom verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have htopWidth :
      2 * ((family m).radiusTop verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hbottomHeight :
      ((family m).radiusBottom verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have htopHeight :
      ((family m).radiusTop verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hleftWidth :
      ((family m).radiusLeft horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hrightWidth :
      ((family m).radiusRight horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hleftHeight :
      2 * ((family m).radiusLeft horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hrightHeight :
      2 * ((family m).radiusRight horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  obtain ⟨bottom, top, left, right,
      hbottomSource, hbottomScore, htopSource, htopScore,
      hleftSource, hleftScore, hrightSource, hrightScore, hshared⟩ :=
    (family m).exists_sharedEndpointComponents E mu hTI
      verticalMargin horizontalMargin (-(extent : Int)) extent
        (-(extent : Int)) extent
      hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  refine ⟨m, extent, bottom, top, left, right,
    hm, hpm, hschedule', hconnector, ?_⟩
  simpa only [Int.cast_neg, Int.cast_natCast] using
    And.intro hbottomSource <| And.intro hbottomScore <|
    And.intro htopSource <| And.intro htopScore <|
    And.intro hleftSource <| And.intro hleftScore <|
    And.intro hrightSource <| And.intro hrightScore hshared





theorem PeriodicPlaneEmbedding.exists_alignedSharedLevel_with_nextConnector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scaleCutoff connectorRadius : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    ∃ m extent : Nat, ∃ bottom top left right : Finset V,
      ∃ nextConnector : Nat,
      scaleCutoff ≤ m ∧ connectorRadius ≤ nextConnector ∧
      1 - scoreEpsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) ∧
      (P.orbitBox (P.bufferedRadius connectorRadius) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent ∧
      (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (bottom : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (top : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (left : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (right : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (let template :=
        P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent))) ∧
      mu.real (P.pairMergeErrorUnion bottom top nextConnector) <
        mergeEpsilon ∧
      mu.real (P.pairMergeErrorUnion left right nextConnector) <
        mergeEpsilon := by
  obtain ⟨m, extent, bottom, top, left, right,
      hm, hpm, hschedule, hconnector,
      hbottomSource, hbottomComponent, htopSource, htopComponent,
      hleftSource, hleftComponent, hrightSource, hrightComponent,
      htemplate, hbottom, htop, hleftScore, hrightScore⟩ :=
    E.exists_alignedSharedLevel_choice mu hTI S p family hp
      verticalRequirement horizontalRequirement scaleCutoff
      (fun _ ↦ connectorRadius)
      hscoreEpsilon
  obtain ⟨nextConnector, hnextConnector, hverticalMerge,
      hhorizontalMerge⟩ :=
    P.exists_commonBoundaryPairMergeRadius mu hunique
      bottom top left right connectorRadius hmergeEpsilon
  exact ⟨m, extent, bottom, top, left, right, nextConnector,
    hm, hnextConnector, hpm, hschedule, hconnector,
    hbottomSource, hbottomComponent, htopSource, htopComponent,
    hleftSource, hleftComponent, hrightSource, hrightComponent,
    (by
      dsimp only
      exact ⟨htemplate, hbottom, htop, hleftScore, hrightScore⟩),
    hverticalMerge, hhorizontalMerge⟩


structure PeriodicPlaneEmbedding.AlignedSharedLevelStep
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (previousScale previousConnector : Nat)
    (scoreEpsilon mergeEpsilon : Real) where
  scale : Nat
  extent : Nat
  bottom : Finset V
  top : Finset V
  left : Finset V
  right : Finset V
  nextConnector : Nat
  scale_ge : previousScale ≤ scale
  connector_mono : previousConnector ≤ nextConnector
  threshold_gt : 1 - scoreEpsilon < p scale
  schedule : (family scale).AlignedMarginSchedule E
    (verticalRequirement scale) (horizontalRequirement scale)
  connector_subset :
    (P.orbitBox (P.bufferedRadius previousConnector) : Set V) ⊆
      E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottom_subset : (bottom : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottomComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (bottom : Set V) (E.rectBottomBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  top_subset : (top : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  topComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (top : Set V) (E.rectTopBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  left_subset : (left : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  leftComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (left : Set V) (E.rectLeftBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  right_subset : (right : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  rightComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (right : Set V) (E.rectRightBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  template_subset :
    (P.fourBoundaryComponentTemplate bottom top left right : Set V) ⊆
      E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottomScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectBottomBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  topScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectTopBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  leftScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectLeftBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  rightScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectRightBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  verticalMerge :
    mu.real (P.pairMergeErrorUnion bottom top nextConnector) < mergeEpsilon
  horizontalMerge :
    mu.real (P.pairMergeErrorUnion left right nextConnector) < mergeEpsilon

theorem PeriodicPlaneEmbedding.nonempty_alignedSharedLevelStep
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (previousScale previousConnector : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    Nonempty (E.AlignedSharedLevelStep mu S p family
      verticalRequirement horizontalRequirement previousScale
      previousConnector scoreEpsilon mergeEpsilon) := by
  obtain ⟨scale, extent, bottom, top, left, right, nextConnector,
      hscale, hconnectorMono, hthreshold, hschedule, hconnector,
      hbottomSource, hbottomComponent, htopSource, htopComponent,
      hleftSource, hleftComponent, hrightSource, hrightComponent,
      htemplateData,
      hvertical, hhorizontal⟩ :=
    E.exists_alignedSharedLevel_with_nextConnector mu hTI hunique
      S p family hp verticalRequirement horizontalRequirement
      previousScale previousConnector hscoreEpsilon hmergeEpsilon
  dsimp only at htemplateData
  rcases htemplateData with
    ⟨htemplate, hbottom, htop, hleftScore, hrightScore⟩
  exact ⟨{
    scale := scale
    extent := extent
    bottom := bottom
    top := top
    left := left
    right := right
    nextConnector := nextConnector
    scale_ge := hscale
    connector_mono := hconnectorMono
    threshold_gt := hthreshold
    schedule := hschedule
    connector_subset := hconnector
    bottom_subset := hbottomSource
    bottomComponentScore := hbottomComponent
    top_subset := htopSource
    topComponentScore := htopComponent
    left_subset := hleftSource
    leftComponentScore := hleftComponent
    right_subset := hrightSource
    rightComponentScore := hrightComponent
    template_subset := htemplate
    bottomScore := hbottom
    topScore := htop
    leftScore := hleftScore
    rightScore := hrightScore
    verticalMerge := hvertical
    horizontalMerge := hhorizontal }⟩




theorem PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scoreEpsilon mergeEpsilon : Nat → Real)
    (hscoreEpsilon : ∀ n, 0 < scoreEpsilon n)
    (hmergeEpsilon : ∀ n, 0 < mergeEpsilon n) :
    ∃ state : Nat → Nat × Nat,
      ∃ steps : ∀ n, E.AlignedSharedLevelStep mu S p family
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n),
      state 0 = (0, 0) ∧
      ∀ n, state (n + 1) = ((steps n).scale + 1,
        (steps n).nextConnector) := by
  let chooseStep (n : Nat) (state : Nat × Nat) :
      E.AlignedSharedLevelStep mu S p family
        verticalRequirement horizontalRequirement
        state.1 state.2 (scoreEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_alignedSharedLevelStep
      mu hTI hunique S p family hp verticalRequirement horizontalRequirement
      state.1 state.2 (hscoreEpsilon n) (hmergeEpsilon n))
  let state : Nat → Nat × Nat := fun n ↦
    Nat.rec (0, 0) (fun n previous ↦
      let step := chooseStep n previous
      (step.scale + 1, step.nextConnector)) n
  let steps : ∀ n, E.AlignedSharedLevelStep mu S p family
      verticalRequirement horizontalRequirement
      (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n) :=
    fun n ↦ chooseStep n (state n)
  refine ⟨state, steps, rfl, ?_⟩
  intro n
  simp only [state, steps, Nat.rec_add_one]





theorem uniform_cofinal_diagonal_below_growing_cutoff
    (f : Nat → Nat → Real)
    (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
    (hle : ∀ k n, f k n ≤ 1) (cutoff : Nat → Nat) :
    ∃ index : Nat → Nat,
      (∀ n, max n (cutoff n) ≤ index n) ∧
      ∀ k : Nat → Nat, (∀ n, k n < n + 1) →
        Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
  let defect : Nat → Nat → Real := fun k n ↦ 1 - f k n
  have hdefect (k : Nat) : Tendsto (defect k) atTop (nhds 0) := by
    simpa [defect] using
      (tendsto_const_nhds (x := (1 : Real))).sub (hf k)
  have hrow (n : Nat) : Tendsto
      (fun m ↦ ∑ k ∈ Finset.range (n + 1), defect k m)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range (n + 1))
      (fun k _hk ↦ hdefect k)
  have hepsilon (n : Nat) : 0 < (1 : Real) / (n + 1) := by positivity
  choose threshold hthreshold using fun n ↦
    (Metric.tendsto_atTop.1 (hrow n))
      ((1 : Real) / (n + 1)) (hepsilon n)
  let index : Nat → Nat := fun n ↦
    max (max n (cutoff n)) (threshold n)
  have hindex (n : Nat) : max n (cutoff n) ≤ index n :=
    Nat.le_max_left _ _
  have hdist (n : Nat) :
      dist (∑ k ∈ Finset.range (n + 1), defect k (index n)) 0 <
        (1 : Real) / (n + 1) :=
    hthreshold n (index n) (Nat.le_max_right _ _)
  have hsum : Tendsto
      (fun n ↦ ∑ k ∈ Finset.range (n + 1), defect k (index n))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero (fun _ ↦ abs_nonneg _) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.dist_eq, sub_zero] using le_of_lt (hdist n)
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hnonneg (n : Nat) : 0 ≤ defect (k n) (index n) :=
    sub_nonneg.mpr (hle (k n) (index n))
  have hupper (n : Nat) : defect (k n) (index n) ≤
      ∑ j ∈ Finset.range (n + 1), defect j (index n) := by
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j ↦ defect j (index n))
      (fun j _hj ↦ sub_nonneg.mpr (hle j (index n)))
      (Finset.mem_range.mpr (hk n))
  have hzero : Tendsto (fun n ↦ defect (k n) (index n))
      atTop (nhds 0) := squeeze_zero hnonneg hupper hsum
  have hone := (tendsto_const_nhds (x := (1 : Real))).sub hzero
  simpa [defect] using hone





theorem exists_cofinalIndex_uniform_tendsto_one_below_diagonal
    (f : Nat → Nat → Real)
    (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
    (hle : ∀ k n, f k n ≤ 1) :
    ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧
      ∀ k : Nat → Nat, (∀ n, k n < n + 1) →
        Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
  let defect : Nat → Nat → Real := fun k n ↦ 1 - f k n
  have hdefect (k : Nat) : Tendsto (defect k) atTop (nhds 0) := by
    simpa [defect] using
      (tendsto_const_nhds (x := (1 : Real))).sub (hf k)
  obtain ⟨index, hindex, hsum⟩ :=
    exists_cofinalIndex_finsetSum_tendsto_zero defect hdefect
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hnonneg (n : Nat) : 0 ≤ defect (k n) (index n) := by
    exact sub_nonneg.mpr (hle (k n) (index n))
  have hupper (n : Nat) : defect (k n) (index n) ≤
      ∑ j ∈ Finset.range (n + 1), defect j (index n) := by
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j ↦ defect j (index n))
      (fun j _hj ↦ sub_nonneg.mpr (hle j (index n)))
      (Finset.mem_range.mpr (hk n))
  have hzero : Tendsto (fun n ↦ defect (k n) (index n))
      atTop (nhds 0) := squeeze_zero hnonneg hupper hsum
  have hone := (tendsto_const_nhds (x := (1 : Real))).sub hzero
  simpa [defect] using hone



theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_boundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d : Nat → Real) (bottomSource topSource : Nat → Finset V)
    (hbottom : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (bottomSource n : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (htop : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (topSource n : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        (bottomSource n) (topSource n))) atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1) := by
  let A : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (bottomSource n : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let H : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (topSource n : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let M : Nat → Real := fun n ↦ mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (bottomSource n) (topSource n))
  let C : Nat → Real := fun n ↦ mu.real
    (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  have hlower (n : Nat) : A n * H n - M n ≤ C n := by
    simpa only [A, H, M, C] using
      E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG (a n) (b n) (c n) (d n)
          (bottomSource n) (topSource n)
  have hbound : Tendsto (fun n ↦ A n * H n - M n)
      atTop (nhds 1) := by
    convert hbottom.mul htop |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hbound tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)



theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d : Nat → Real) (leftSource rightSource : Nat → Finset V)
    (hleft : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (leftSource n : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hright : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (rightSource n : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        (leftSource n) (rightSource n))) atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1) := by
  let A : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (leftSource n : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let H : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (rightSource n : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let M : Nat → Real := fun n ↦ mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (leftSource n) (rightSource n))
  let C : Nat → Real := fun n ↦ mu.real
    (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  have hlower (n : Nat) : A n * H n - M n ≤ C n := by
    simpa only [A, H, M, C] using
      E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG (a n) (b n) (c n) (d n)
          (leftSource n) (rightSource n)
  have hbound : Tendsto (fun n ↦ A n * H n - M n)
      atTop (nhds 1) := by
    convert hleft.mul hright |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hbound tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)



theorem PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_translated_rect
    (E : PeriodicPlaneEmbedding P) (R M width height : Nat) (z : Site 2)
    (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) ≤ M)
    (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) ≤ M) :
    ∀ v : PreferenceGridVertex width height,
      P.shift (preferenceGridSite v + z) '' (P.orbitBox R : Set V) ⊆
        E.rectVertices (-(M : Real) + z 0) (M + width + z 0 : Real)
          (-(M : Real) + z 1) (M + height + z 1 : Real) := by
  intro v _ hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  rw [P.shift_add]
  apply (E.shift_mem_rectVertices z (-(M : Real)) (M + width : Real)
    (-(M : Real)) (M + height : Real) _).2
  exact E.preferenceGrid_orbitBox_subset_rect_of_coordinateBound
    R M width height hx hy v ⟨u, hu, rfl⟩

set_option linter.unusedVariables false in





theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2)
    (hleft : ∀ n,
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hright : ∀ n,
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hbottom : ∀ n,
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (htop : ∀ n,
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hleftLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n - pad n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n + pad n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n - pad n : Real)
              (-(M n : Real)) (M n + height n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n + pad n : Real)
              (-(M n : Real)) (M n + height n : Real)) →
      Tendsto (fun n ↦ max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  let template : Nat → Finset V := fun n ↦
    P.fourShiftTemplate (P.orbitBox n) (zLeft n) (zRight n)
      (zBottom n) (zTop n)
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h ↦ h.1
  have htemplateHit : Tendsto (fun n ↦
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template] using
      P.fourShiftTemplate_hitsInfinite_tendsto_one mu hTI hexists
        zLeft zRight zBottom zTop
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit pad hpad
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight
    hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
  let bottom : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
      (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let top : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
      (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let left : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
      (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let right : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
      (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let p : Nat → Real := fun n ↦
    min (min (bottom n) (top n)) (min (left n) (right n))
  have hp : Tendsto p atTop (nhds 1) := by
    simpa only [p, bottom, top, left, right, min_self] using
      (hbottomLimit.min htopLimit).min (hleftLimit.min hrightLimit)
  apply hcross width height hwidth hheight (fun _ ↦ 0)
    (fun n ↦ -(M n : Real)) (fun n ↦ M n + width n)
    (fun n ↦ -(M n : Real)) (fun n ↦ M n + height n) p hp
  · intro n
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans measureReal_le_one)
  · intro n v
    simpa only [template, zero_add] using
      E.fourShiftTemplate_preferenceGrid_subset_rect
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n)
        (hleft n) (hright n) (hbottom n) (htop n) v
  · simpa only [zero_add] using hconnectorV0
  · simpa only [zero_add] using hconnectorV1
  · simpa only [zero_add] using hconnectorH0
  · simpa only [zero_add] using hconnectorH1
  · intro n i
    have hside := E.rectBottomConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) i
    exact ((min_le_left _ _).trans (min_le_left _ _)).trans
      (by simpa only [bottom, template, zero_add] using hside)
  · intro n i
    have hside := E.rectTopConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) i
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans
      (by simpa only [top, template, zero_add] using hside)
  · intro n j
    have hside := E.rectLeftConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) j
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (by simpa only [left, template, zero_add] using hside)
  · intro n j
    have hside := E.rectRightConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) j
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans
      (by simpa only [right, template, zero_add] using hside)



theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2)
    (hleft : ∀ n,
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hright : ∀ n,
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hbottom : ∀ n,
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (htop : ∀ n,
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hleftLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) →
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) →
      Tendsto (fun n ↦ max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector
      mu hFKG hTI hunique M zLeft zRight zBottom zTop
      hleft hright hbottom htop hleftLimit hrightLimit
      hbottomLimit htopLimit pad hpad
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight hx hy
  apply hcross width height hwidth hheight
  · intro n v
    simpa only [verticalShift_zero_apply, verticalShift_one_apply,
      Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using
      E.preferenceGrid_orbitBox_subset_translated_rect
        (P.bufferedRadius (radius n)) (M n) (width n) (height n)
        (verticalShift (-(pad n))) (hx n) (hy n) v
  · intro n v
    have hbase := E.preferenceGrid_orbitBox_subset_translated_rect
      (P.bufferedRadius (radius n)) (M n) (width n) (height n)
      (verticalShift (-(pad n))) (hx n) (hy n) v
    have hbase' :
        P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n - pad n : Real) := by
      simpa only [verticalShift_zero_apply, verticalShift_one_apply,
        Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using hbase
    apply hbase'.trans
    apply E.rectVertices_mono le_rfl le_rfl le_rfl
    have hp : (0 : Real) ≤ pad n := by exact_mod_cast hpad n
    linarith
  · intro n v
    simpa only [horizontalShift_zero_apply, horizontalShift_one_apply,
      Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using
      E.preferenceGrid_orbitBox_subset_translated_rect
        (P.bufferedRadius (radius n)) (M n) (width n) (height n)
        (horizontalShift (-(pad n))) (hx n) (hy n) v
  · intro n v
    have hbase := E.preferenceGrid_orbitBox_subset_translated_rect
      (P.bufferedRadius (radius n)) (M n) (width n) (height n)
      (horizontalShift (-(pad n))) (hx n) (hy n) v
    have hbase' :
        P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n - pad n : Real)
              (-(M n : Real)) (M n + height n : Real) := by
      simpa only [horizontalShift_zero_apply, horizontalShift_one_apply,
        Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using hbase
    apply hbase'.trans
    apply E.rectVertices_mono le_rfl
    · have hp : (0 : Real) ≤ pad n := by exact_mod_cast hpad n
      linarith
    · exact le_rfl
    · exact le_rfl

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}




theorem adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    (horizontal vertical dualVertical dualHorizontal : Nat → Nat → Real)
    (K : Nat → Nat)
    (hhorizontal_nonneg : ∀ n k, 0 ≤ horizontal n k)
    (hvertical_nonneg : ∀ n k, 0 ≤ vertical n k)
    (hhorizontal_le_one : ∀ n k, horizontal n k ≤ 1)
    (hvertical_le_one : ∀ n k, vertical n k ≤ 1)
    (hvertical_start : Tendsto (fun n ↦ vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto
      (fun n ↦ horizontal n (K n + 1)) atTop (nhds 1))
    (hmatchHorizontal : ∀ n k,
      horizontal n k + dualVertical n k ≤ 1)
    (hmatchVertical : ∀ n k,
      vertical n k + dualHorizontal n k ≤ 1)
    (hprimalLimits : ∀ k : Nat → Nat,
      (∀ n, k n < K n + 1) → Tendsto (fun n ↦ max
        (horizontal n (k n)) (vertical n (k n + 1)))
        atTop (nhds 1))
    (hdualLimits : ∀ k : Nat → Nat,
      (∀ n, k n ≤ K n + 1) → Tendsto (fun n ↦ max
        (dualVertical n (k n)) (dualHorizontal n (k n)))
        atTop (nhds 1)) : False := by
  apply adjacent_height_array_contradiction_of_endpoint_and_uniform_limits
    horizontal vertical K hhorizontal_nonneg hvertical_nonneg
    hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end
  intro k hk
  have hkBound : ∀ n, k n ≤ K n + 1 := fun n ↦ (hk n).le
  have hkNextBound : ∀ n, k n + 1 ≤ K n + 1 := by
    intro n
    exact Nat.succ_le_of_lt (hk n)
  refine ⟨hprimalLimits k hk, ?_, ?_⟩
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n ↦ horizontal n (k n))
      (fun n ↦ vertical n (k n))
      (fun n ↦ dualVertical n (k n))
      (fun n ↦ dualHorizontal n (k n))
      (fun n ↦ hhorizontal_nonneg n (k n))
      (fun n ↦ hvertical_nonneg n (k n))
      (fun n ↦ hmatchHorizontal n (k n))
      (fun n ↦ hmatchVertical n (k n))
      (hdualLimits k hkBound)
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n ↦ horizontal n (k n + 1))
      (fun n ↦ vertical n (k n + 1))
      (fun n ↦ dualVertical n (k n + 1))
      (fun n ↦ dualHorizontal n (k n + 1))
      (fun n ↦ hhorizontal_nonneg n (k n + 1))
      (fun n ↦ hvertical_nonneg n (k n + 1))
      (fun n ↦ hmatchHorizontal n (k n + 1))
      (fun n ↦ hmatchVertical n (k n + 1))
      (hdualLimits (fun n ↦ k n + 1) hkNextBound)


theorem PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_bounded_max_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (a b c d : Nat → Nat → Real) (K : Nat → Nat)
    (hspanX : ∀ n k, a n k + 5 * B < b n k - 5 * B)
    (hspanY : ∀ n k, c n k + 5 * B < d n k - 5 * B)
    (hverticalStart : Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a n (K n + 1)) (b n (K n + 1))
        (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B)))
      atTop (nhds 1))
    (hprimal : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
      Tendsto (fun n ↦ max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B)
          (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1))
    (hdual : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) →
      Tendsto (fun n ↦ max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a n (k n) + 4 * B) (b n (k n) - 4 * B)
            (c n (k n)) (d n (k n))))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a n (k n)) (b n (k n))
            (c n (k n) + 4 * B) (d n (k n) - 4 * B))))
        atTop (nhds 1)) : False := by
  let horizontal : Nat → Nat → Real := fun n k ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  let vertical : Nat → Nat → Real := fun n k ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualVertical : Nat → Nat → Real := fun n k ↦ mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualHorizontal : Nat → Nat → Real := fun n k ↦ mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
    (fun _ _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_nonneg)
    (fun _ _ ↦ measureReal_le_one) (fun _ _ ↦ measureReal_le_one)
    (by simpa [vertical] using hverticalStart)
    (by simpa [horizontal] using hhorizontalEnd)
  · intro n k
    exact D.matchedCrossing_measureReal_add_le_one mu hBpos hBp hBd
      (hspanX n k) (hspanY n k)
  · intro n k
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu hBpos hBp hBd (hspanX n k) (hspanY n k)
  · intro k hk
    simpa [horizontal, vertical] using hprimal k hk
  · intro k hk
    simpa [dualVertical, dualHorizontal] using hdual k hk





structure PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a : Nat → Nat → Real
  b : Nat → Nat → Real
  c : Nat → Nat → Real
  d : Nat → Nat → Real
  K : Nat → Nat
  spanX : ∀ n k, a n k + 5 * B < b n k - 5 * B
  spanY : ∀ n k, c n k + 5 * B < d n k - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0)))
    atTop (nhds 1)
  horizontalEnd : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a n (K n + 1)) (b n (K n + 1))
      (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B)))
    atTop (nhds 1)
  primalAdjacent : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
    Tendsto (fun n ↦ max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a n (k n)) (b n (k n))
        (c n (k n) + 4 * B) (d n (k n) - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B)
        (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1)
  dualLevels : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) →
    Tendsto (fun n ↦ max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n (k n) + 4 * B) (b n (k n) - 4 * B)
          (c n (k n)) (d n (k n))))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B)))) atTop (nhds 1)



theorem PeriodicPlanarDualPair.RecursiveRectangleArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.RecursiveRectangleArrayCertificate mu) : False := by
  exact D.adjacent_rectangles_contradiction_of_bounded_max_limits mu
    data.Bpos data.primalArcBound data.dualArcBound
    data.a data.b data.c data.d data.K data.spanX data.spanY
    data.verticalStart data.horizontalEnd data.primalAdjacent data.dualLevels


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_recursiveArray
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (harray :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 →
        Nonempty (D.RecursiveRectangleArrayCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := harray hcommon
  exact data.false D _





structure PeriodicPlanarDualPair.MacroArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Nat
  T : Nat
  Bpos : 0 < B
  increment : 8 * B < T
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  K : Nat → Nat
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalEnd :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (q n (K n + 1)).1 (q n (K n + 1)).2.1
        ((q n (K n + 1)).2.2.1 + 4 * B)
        ((q n (K n + 1)).2.2.2 - 4 * B))) atTop (nhds 1)
  primalAdjacent :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
      Tendsto (fun n ↦ max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (q n (k n)).1 (q n (k n)).2.1
          ((q n (k n)).2.2.1 + 4 * B)
          ((q n (k n)).2.2.2 - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (q n (k n)).1 (q n (k n)).2.1
          ((q n (k n)).2.2.1 + 4 * B)
          ((q n (k n)).2.2.2 - 4 * B + (T + 4 * B : Nat)))))
        atTop (nhds 1)
  dualLevels :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) → Tendsto (fun n ↦ max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          ((q n (k n)).1 + 4 * B) ((q n (k n)).2.1 - 4 * B)
          ((q n (k n)).2.2.1) ((q n (k n)).2.2.2)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          ((q n (k n)).1) ((q n (k n)).2.1
          ) ((q n (k n)).2.2.1 + 4 * B)
          ((q n (k n)).2.2.2 - 4 * B)))) atTop (nhds 1)



theorem PeriodicPlanarDualPair.MacroArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.MacroArrayCertificate mu) : False := by
  let q := sheffieldMacroArrayCoordinates data.B data.T
    data.a0 data.b0 data.c0 data.d0
  let a : Nat → Nat → Real := fun n k ↦ (q n k).1
  let b : Nat → Nat → Real := fun n k ↦ (q n k).2.1
  let c : Nat → Nat → Real := fun n k ↦ (q n k).2.2.1
  let d : Nat → Nat → Real := fun n k ↦ (q n k).2.2.2
  have hspans := sheffieldMacroArrayCoordinates_spans
    data.B data.T data.increment data.a0 data.b0 data.c0 data.d0
      data.spanX0 data.spanY0
  apply D.adjacent_rectangles_contradiction_of_bounded_max_limits mu
    (B := (data.B : Real)) (by exact_mod_cast data.Bpos)
    data.primalArcBound data.dualArcBound a b c d data.K
  · simpa only [a, b, c, d, q] using hspans.1
  · simpa only [a, b, c, d, q] using hspans.2
  · simpa only [a, b, c, d, q, sheffieldMacroArrayCoordinates,
      Nat.cast_zero, mul_zero, sub_zero, add_zero] using data.verticalStart
  · simpa only [a, b, c, d, q] using data.horizontalEnd
  · intro k hk
    have hlim := data.primalAdjacent k hk
    apply hlim.congr'
    filter_upwards with n
    apply congrArg (fun x : Real ↦ x)
    congr 3
    · dsimp only [a, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [b, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [c, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
    · dsimp only [d, q, sheffieldMacroArrayCoordinates]
      push_cast
      ring
  · intro k hk
    simpa only [a, b, c, d, q] using data.dualLevels k hk


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_macroArray
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (harray :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 →
        Nonempty (D.MacroArrayCertificate mu)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  obtain ⟨data⟩ := harray hcommon
  exact data.false D _




structure PeriodicPlanarDualPair.PointwiseMacroArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Nat
  T : Nat
  Bpos : 0 < B
  increment : 8 * B < T
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  verticalStart : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    atTop (nhds 1)
  horizontalLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (q n (k + 1)).1 (q n (k + 1)).2.1
        ((q n (k + 1)).2.2.1 + 4 * B)
        ((q n (k + 1)).2.2.2 - 4 * B))) atTop (nhds 1)
  primalLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (q n k).1 (q n k).2.1
        ((q n k).2.2.1 + 4 * B) ((q n k).2.2.2 - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (q n k).1 (q n k).2.1 ((q n k).2.2.1 + 4 * B)
        ((q n k).2.2.2 - 4 * B + (T + 4 * B : Nat)))))
      atTop (nhds 1)
  dualLevel :
    let q := sheffieldMacroArrayCoordinates B T a0 b0 c0 d0
    ∀ k, Tendsto (fun n ↦ max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          ((q n k).1 + 4 * B) ((q n k).2.1 - 4 * B)
          ((q n k).2.2.1) ((q n k).2.2.2)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          ((q n k).1) ((q n k).2.1)
          ((q n k).2.2.1 + 4 * B) ((q n k).2.2.2 - 4 * B))))
      atTop (nhds 1)



theorem PeriodicPlanarDualPair.PointwiseMacroArrayCertificate.toMacroArrayCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseMacroArrayCertificate mu) :
    Nonempty (D.MacroArrayCertificate mu) := by
  let q := sheffieldMacroArrayCoordinates raw.B raw.T
    raw.a0 raw.b0 raw.c0 raw.d0
  let horizontal : Nat → Nat → Real := fun k n ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (q n (k + 1)).1 (q n (k + 1)).2.1
      ((q n (k + 1)).2.2.1 + 4 * raw.B)
      ((q n (k + 1)).2.2.2 - 4 * raw.B))
  let primal : Nat → Nat → Real := fun k n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (q n k).1 (q n k).2.1
      ((q n k).2.2.1 + 4 * raw.B) ((q n k).2.2.2 - 4 * raw.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (q n k).1 (q n k).2.1 ((q n k).2.2.1 + 4 * raw.B)
      ((q n k).2.2.2 - 4 * raw.B + (raw.T + 4 * raw.B : Nat))))
  let dual : Nat → Nat → Real := fun k n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        ((q n k).1 + 4 * raw.B) ((q n k).2.1 - 4 * raw.B)
        ((q n k).2.2.1) ((q n k).2.2.2)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        ((q n k).1) ((q n k).2.1
        ) ((q n k).2.2.1 + 4 * raw.B) ((q n k).2.2.2 - 4 * raw.B)))
  let combined : Nat → Nat → Real := fun k n ↦
    min (horizontal k n) (min (primal k n) (dual k n))
  have hhorizontal (k : Nat) : Tendsto (horizontal k) atTop (nhds 1) := by
    simpa only [horizontal, q] using raw.horizontalLevel k
  have hprimal (k : Nat) : Tendsto (primal k) atTop (nhds 1) := by
    simpa only [primal, q] using raw.primalLevel k
  have hdual (k : Nat) : Tendsto (dual k) atTop (nhds 1) := by
    simpa only [dual, q] using raw.dualLevel k
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hhorizontal k).min ((hprimal k).min (hdual k))
  have hcombinedLe (k n : Nat) : combined k n ≤ 1 := by
    exact (min_le_left _ _).trans measureReal_le_one
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  have hindexTop : Tendsto index atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hindex n)
  let K : Nat → Nat := fun n ↦ n.pred
  let a0 : Nat → Real := fun n ↦ raw.a0 (index n)
  let b0 : Nat → Real := fun n ↦ raw.b0 (index n)
  let c0 : Nat → Real := fun n ↦ raw.c0 (index n)
  let d0 : Nat → Real := fun n ↦ raw.d0 (index n)
  let q' := sheffieldMacroArrayCoordinates raw.B raw.T a0 b0 c0 d0
  have hq (n k : Nat) : q' n k = q (index n) k := rfl
  have hcomponentLimit (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ combined (k n) (index n)) atTop (nhds 1) :=
    huniform k hk
  have hhorizontalOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ horizontal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_left _ _)) (fun _ ↦ measureReal_le_one)
  have hprimalOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ primal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_right _ _).trans (min_le_left _ _))
      (fun _ ↦ max_le measureReal_le_one measureReal_le_one)
  have hdualOfCombined (k : Nat → Nat) (hk : ∀ n, k n < n + 1) :
      Tendsto (fun n ↦ dual (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n ↦ (min_le_right _ _).trans (min_le_right _ _))
      (fun _ ↦ max_le measureReal_le_one measureReal_le_one)
  refine ⟨{
    B := raw.B
    T := raw.T
    Bpos := raw.Bpos
    increment := raw.increment
    primalArcBound := raw.primalArcBound
    dualArcBound := raw.dualArcBound
    a0 := a0
    b0 := b0
    c0 := c0
    d0 := d0
    K := K
    spanX0 := fun n ↦ raw.spanX0 (index n)
    spanY0 := fun n ↦ raw.spanY0 (index n)
    verticalStart := raw.verticalStart.comp hindexTop
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }⟩
  · dsimp only
    have hK : ∀ n, K n < n + 1 := by
      intro n
      dsimp only [K]
      exact (Nat.pred_le n).trans_lt (Nat.lt_succ_self n)
    have hlim := hhorizontalOfCombined K hK
    simpa only [horizontal, q', hq] using hlim
  · dsimp only
    intro k hk
    have hk' : ∀ n, k n < n + 1 := by
      intro n
      have hkn := hk n
      dsimp only [K] at hkn
      exact hkn.trans_le (Nat.succ_le_succ (Nat.pred_le n))
    have hlim := hprimalOfCombined k hk'
    simpa only [primal, q', hq] using hlim
  · dsimp only
    intro k hk
    let k' : Nat → Nat := fun n ↦ if n = 0 then 0 else k n
    have hk' : ∀ n, k' n < n + 1 := by
      intro n
      by_cases hn : n = 0
      · simp [k', hn]
      · have hkn := hk n
        dsimp only [K] at hkn
        have hp : n.pred + 1 = n := by
          cases n with
          | zero => exact (hn rfl).elim
          | succ m => rfl
        rw [hp] at hkn
        simp only [k', hn, if_neg]
        exact Nat.lt_succ_of_le hkn
    have hlim := hdualOfCombined k' hk'
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simpa [dual, q', hq, k', hn0]




structure PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) (B : Real) where
  Bpos : 0 < B
  primalArcBound : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B
  dualArcBound : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B
  a0 : Nat → Real
  b0 : Nat → Real
  c0 : Nat → Real
  d0 : Nat → Real
  a1 : Nat → Real
  b1 : Nat → Real
  c1 : Nat → Real
  d1 : Nat → Real
  spanX0 : ∀ n, a0 n + 5 * B < b0 n - 5 * B
  spanY0 : ∀ n, c0 n + 5 * B < d0 n - 5 * B
  spanX1 : ∀ n, a1 n + 5 * B < b1 n - 5 * B
  spanY1 : ∀ n, c1 n + 5 * B < d1 n - 5 * B
  bottomSource : Nat → Finset V
  topSource : Nat → Finset V
  leftSource : Nat → Finset V
  rightSource : Nat → Finset V
  bottomLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (bottomSource n : Set V)
      (D.primalEmbedding.rectBottomBoundaryVertices
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n))))
    atTop (nhds 1)
  topLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (topSource n : Set V)
      (D.primalEmbedding.rectTopBoundaryVertices
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n))))
    atTop (nhds 1)
  verticalMergeLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectanglePairMergeErrorUnion
      (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)
      (bottomSource n) (topSource n))) atTop (nhds 0)
  leftLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (leftSource n : Set V)
      (D.primalEmbedding.rectLeftBoundaryVertices
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)
  rightLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectSideConnectionEvent
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (rightSource n : Set V)
      (D.primalEmbedding.rectRightBoundaryVertices
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)
  horizontalMergeLimit : Tendsto (fun n ↦ mu.real
    (D.primalEmbedding.rectanglePairMergeErrorUnion
      (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B)
      (leftSource n) (rightSource n))) atTop (nhds 0)
  primalAdjacent : Tendsto (fun n ↦ max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
    atTop (nhds 1)
  dualLevel0 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + 4 * B) (b0 n - 4 * B) (c0 n) (d0 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B))))
    atTop (nhds 1)
  dualLevel1 : Tendsto (fun n ↦ max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + 4 * B) (d1 n - 4 * B))))
    atTop (nhds 1)



theorem PeriodicPlanarDualPair.TwoLevelBoundaryScoreArray.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {B : Real}
    (data : D.TwoLevelBoundaryScoreArray mu B) : False := by
  have hvertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_boundaryScores
      mu hFKG
      (fun n ↦ data.a0 n + 4 * B) (fun n ↦ data.b0 n - 4 * B)
      data.c0 data.d0 data.bottomSource data.topSource
      data.bottomLimit data.topLimit data.verticalMergeLimit
  have hhorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores
      mu hFKG data.a1 data.b1
      (fun n ↦ data.c1 n + 4 * B) (fun n ↦ data.d1 n - 4 * B)
      data.leftSource data.rightSource
      data.leftLimit data.rightLimit data.horizontalMergeLimit
  exact PeriodicPlanarDualPair.TwoLevelRectangleArray.false D mu {
    Bpos := data.Bpos
    primalArcBound := data.primalArcBound
    dualArcBound := data.dualArcBound
    a0 := data.a0
    b0 := data.b0
    c0 := data.c0
    d0 := data.d0
    a1 := data.a1
    b1 := data.b1
    c1 := data.c1
    d1 := data.d1
    spanX0 := data.spanX0
    spanY0 := data.spanY0
    spanX1 := data.spanX1
    spanY1 := data.spanY1
    verticalStart := hvertical
    horizontalEnd := hhorizontal
    primalAdjacent := data.primalAdjacent
    dualLevel0 := data.dualLevel0
    dualLevel1 := data.dualLevel1 }





theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_boundaryScoreArray
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (harray :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1 →
        ∃ B : Real, Nonempty (D.TwoLevelBoundaryScoreArray mu B)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only
  intro hcommon
  have hdata := D.freeBufferedInfiniteVolume_sheffieldData_of_common
    hp hp1 hq hcommon
  obtain ⟨B, ⟨data⟩⟩ := harray hcommon
  exact data.false D _ hdata.1

end StatMech.FK.PeriodicPlanar
