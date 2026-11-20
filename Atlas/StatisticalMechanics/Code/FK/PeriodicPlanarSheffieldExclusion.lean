/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarSheffieldCommonArray
import Code.FK.PeriodicPlanarSheffieldCommonRectangle
import Code.FK.PeriodicPlanarSheffieldSynchronization
import Code.FK.PeriodicPlanarSheffieldDualTransverse
import Code.FK.PeriodicPlanarCanonicalErgodicity
import Code.FK.PeriodicPlanarCanonicalFKG

open Filter MeasureTheory Set Topology

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [Countable V] [Countable W]
  [DecidableEq V] [DecidableEq W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



def PeriodicGraph.fourShiftTemplate (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) : Finset V :=
  (S.image (P.shift zLeft) ∪ S.image (P.shift zRight)) ∪
    (S.image (P.shift zBottom) ∪ S.image (P.shift zTop))

omit [Countable V] in
theorem PeriodicGraph.image_subset_fourShiftTemplate
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) :
    S.image (P.shift zLeft) ⊆
      P.fourShiftTemplate S zLeft zRight zBottom zTop := by
  intro x hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union]
  exact Or.inl (Or.inl hx)

omit [Countable V] in
theorem PeriodicGraph.image_right_subset_fourShiftTemplate
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) :
    S.image (P.shift zRight) ⊆
      P.fourShiftTemplate S zLeft zRight zBottom zTop := by
  intro x hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union]
  exact Or.inl (Or.inr hx)

omit [Countable V] in
theorem PeriodicGraph.image_bottom_subset_fourShiftTemplate
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) :
    S.image (P.shift zBottom) ⊆
      P.fourShiftTemplate S zLeft zRight zBottom zTop := by
  intro x hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union]
  exact Or.inr (Or.inl hx)

omit [Countable V] in
theorem PeriodicGraph.image_top_subset_fourShiftTemplate
    (P : PeriodicGraph V) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) :
    S.image (P.shift zTop) ⊆
      P.fourShiftTemplate S zLeft zRight zBottom zTop := by
  intro x hx
  simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union]
  exact Or.inr (Or.inr hx)

omit [Countable V] in


theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_mono_source
    (E : PeriodicPlaneEmbedding P) {a b c d : Real}
    {S T side : Set V} (hST : S ⊆ T) :
    E.rectSideConnectionEvent a b c d S side ⊆
      E.rectSideConnectionEvent a b c d T side := by
  rintro omega ⟨x, hxS, hxInfinite, y, hySide, hxy⟩
  exact ⟨x, hST hxS, hxInfinite, y, hySide, hxy⟩






theorem PeriodicPlaneEmbedding.fourShiftTemplate_preferenceGrid_subset_rect
    (E : PeriodicPlaneEmbedding P) (M width height : Nat) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2)
    (hleft : (S.image (P.shift zLeft) : Set V) ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (hright : (S.image (P.shift zRight) : Set V) ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (hbottom : (S.image (P.shift zBottom) : Set V) ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
    (htop : (S.image (P.shift zTop) : Set V) ⊆ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)) :
    ∀ v : PreferenceGridVertex width height,
      ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift (preferenceGridSite v)) : Set V) ⊆
        E.rectVertices (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real) := by
  intro v x hx
  change x ∈ (P.fourShiftTemplate S zLeft zRight zBottom zTop).image
    (P.shift (preferenceGridSite v)) at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hySquare : y ∈ E.rectVertices
      (-(M : Real)) (M : Real) (-(M : Real)) (M : Real) := by
    simp only [PeriodicGraph.fourShiftTemplate, Finset.mem_union] at hy
    rcases hy with (hy | hy) | (hy | hy)
    · exact hleft hy
    · exact hright hy
    · exact hbottom hy
    · exact htop hy
  have hi0 : 0 ≤ (v.1.val : Real) := by positivity
  have hiW : (v.1.val : Real) ≤ width := by
    exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have hj0 : 0 ≤ (v.2.val : Real) := by positivity
  have hjH : (v.2.val : Real) ≤ height := by
    exact_mod_cast Nat.le_of_lt_succ v.2.isLt
  change -(M : Real) ≤ E.vertexCoord
      (P.shift (preferenceGridSite v) y) 0 ∧
    E.vertexCoord (P.shift (preferenceGridSite v) y) 0 ≤ M + width ∧
    -(M : Real) ≤ E.vertexCoord
      (P.shift (preferenceGridSite v) y) 1 ∧
    E.vertexCoord (P.shift (preferenceGridSite v) y) 1 ≤ M + height
  simp only [E.vertexCoord_shift, preferenceGridSite]
  norm_num
  rcases hySquare with ⟨hyL, hyR, hyB, hyT⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith




theorem PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_rect_of_coordinateBound
    (E : PeriodicPlaneEmbedding P) (R M width height : Nat)
    (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) ≤ M)
    (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) ≤ M) :
    ∀ v : PreferenceGridVertex width height,
      P.shift (preferenceGridSite v) '' (P.orbitBox R : Set V) ⊆
        E.rectVertices (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real) := by
  intro v x hxmem
  obtain ⟨u, hu, rfl⟩ := hxmem
  have hu0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (0 : Fin 2)
  have hu1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hu (1 : Fin 2)
  have hu0M : |E.vertexCoord u 0| ≤ (M : Real) := hu0.trans hx
  have hu1M : |E.vertexCoord u 1| ≤ (M : Real) := hu1.trans hy
  have hi0 : 0 ≤ (v.1.val : Real) := by positivity
  have hiW : (v.1.val : Real) ≤ width := by
    exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have hj0 : 0 ≤ (v.2.val : Real) := by positivity
  have hjH : (v.2.val : Real) ≤ height := by
    exact_mod_cast Nat.le_of_lt_succ v.2.isLt
  change -(M : Real) ≤ E.vertexCoord
      (P.shift (preferenceGridSite v) u) 0 ∧
    E.vertexCoord (P.shift (preferenceGridSite v) u) 0 ≤ M + width ∧
    -(M : Real) ≤ E.vertexCoord
      (P.shift (preferenceGridSite v) u) 1 ∧
    E.vertexCoord (P.shift (preferenceGridSite v) u) 1 ≤ M + height
  simp only [E.vertexCoord_shift, preferenceGridSite]
  norm_num
  rcases abs_le.mp hu0M with ⟨hu0Lower, hu0Upper⟩
  rcases abs_le.mp hu1M with ⟨hu1Lower, hu1Upper⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith



theorem PeriodicPlaneEmbedding.rectBottomConnection_fourShiftTemplate_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M width height : Nat) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) (i : Fin (width + 1)) :
    mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
        (S.image (P.shift zBottom) : Set V)
        (E.rectBottomBoundaryVertices
          (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤
      mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift (preferenceGridSite
            (i, (0 : Fin (height + 1))))) : Set V)
        (E.rectBottomBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
  let z : Site 2 := preferenceGridSite (i, (0 : Fin (height + 1)))
  have hz : z 1 = 0 := by simp [z, preferenceGridSite]
  have hi : (i.val : Real) ≤ width := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hle := E.rectBottomConnection_tangential_measureReal_le
    mu hTI z hz (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (-(M : Real)) (M + width : Real) (M + height : Real)
      (S.image (P.shift zBottom) : Set V)
      (by simp [z, preferenceGridSite])
      (by
        change (M : Real) + i.val ≤ M + width
        simpa [add_comm] using add_le_add_left hi (M : Real))
      (by simp [z, preferenceGridSite])
  refine hle.trans (measureReal_mono (μ := mu)
    (E.rectSideConnectionEvent_mono_source ?_))
  rintro x ⟨y, hy, rfl⟩
  change P.shift z y ∈
    (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift z)
  exact Finset.mem_image.mpr
    ⟨y, P.image_bottom_subset_fourShiftTemplate S
      zLeft zRight zBottom zTop hy, rfl⟩


theorem PeriodicPlaneEmbedding.rectLeftConnection_fourShiftTemplate_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M width height : Nat) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) (j : Fin (height + 1)) :
    mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
        (S.image (P.shift zLeft) : Set V)
        (E.rectLeftBoundaryVertices
          (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤
      mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift (preferenceGridSite
            ((0 : Fin (width + 1)), j))) : Set V)
        (E.rectLeftBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
  let z : Site 2 := preferenceGridSite ((0 : Fin (width + 1)), j)
  have hz : z 0 = 0 := by simp [z, preferenceGridSite]
  have hj : (j.val : Real) ≤ height := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hle := E.rectLeftConnection_tangential_measureReal_le
    mu hTI z hz (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (M + width : Real) (-(M : Real)) (M + height : Real)
      (S.image (P.shift zLeft) : Set V)
      (by simp [z, preferenceGridSite])
      (by simp [z, preferenceGridSite])
      (by
        change (M : Real) + j.val ≤ M + height
        simpa [add_comm] using add_le_add_left hj (M : Real))
  refine hle.trans (measureReal_mono (μ := mu)
    (E.rectSideConnectionEvent_mono_source ?_))
  rintro x ⟨y, hy, rfl⟩
  change P.shift z y ∈
    (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift z)
  exact Finset.mem_image.mpr
    ⟨y, P.image_subset_fourShiftTemplate S
      zLeft zRight zBottom zTop hy, rfl⟩



theorem PeriodicPlaneEmbedding.rectRightConnection_fourShiftTemplate_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M width height : Nat) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) (j : Fin (height + 1)) :
    mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
        (S.image (P.shift zRight) : Set V)
        (E.rectRightBoundaryVertices
          (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤
      mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift (preferenceGridSite
            (Fin.last width, j))) : Set V)
        (E.rectRightBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
  let z : Site 2 := preferenceGridSite (Fin.last width, j)
  have hz0 : (z 0 : Real) = width := by simp [z, preferenceGridSite]
  have hz1 : (z 1 : Real) = j.val := by simp [z, preferenceGridSite]
  have hj : (j.val : Real) ≤ height := by
    exact_mod_cast Nat.le_of_lt_succ j.isLt
  have htranslate := E.rectRightConnection_translate_measureReal_eq
    mu hTI z (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift zRight) : Set V)
  rw [hz0, hz1] at htranslate
  calc
    _ = mu.real (E.rectSideConnectionEvent
        (-(M : Real) + width) (M + width : Real)
        (-(M : Real) + j.val) ((M : Real) + j.val)
        (P.shift z '' (S.image (P.shift zRight) : Set V))
        (E.rectRightBoundaryVertices
          (-(M : Real) + width) (M + width : Real)
          (-(M : Real) + j.val) ((M : Real) + j.val))) :=
      htranslate.symm
    _ ≤ mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        (P.shift z '' (S.image (P.shift zRight) : Set V))
        (E.rectRightBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
      apply measureReal_mono (μ := mu)
      apply E.rectRightConnectionEvent_mono_otherBounds
      · norm_num
      · norm_num
      · simpa [add_comm] using add_le_add_left hj (M : Real)
    _ ≤ _ := by
      refine measureReal_mono (μ := mu)
        (E.rectSideConnectionEvent_mono_source ?_)
      rintro x ⟨y, hy, rfl⟩
      change P.shift z y ∈
        (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift z)
      exact Finset.mem_image.mpr
        ⟨y, P.image_right_subset_fourShiftTemplate S
          zLeft zRight zBottom zTop hy, rfl⟩



theorem PeriodicPlaneEmbedding.rectTopConnection_fourShiftTemplate_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (M width height : Nat) (S : Finset V)
    (zLeft zRight zBottom zTop : Site 2) (i : Fin (width + 1)) :
    mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
        (S.image (P.shift zTop) : Set V)
        (E.rectTopBoundaryVertices
          (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))) ≤
      mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image
          (P.shift (preferenceGridSite
            (i, Fin.last height))) : Set V)
        (E.rectTopBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
  let z : Site 2 := preferenceGridSite (i, Fin.last height)
  have hz0 : (z 0 : Real) = i.val := by simp [z, preferenceGridSite]
  have hz1 : (z 1 : Real) = height := by simp [z, preferenceGridSite]
  have hi : (i.val : Real) ≤ width := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have htranslate := E.rectTopConnection_translate_measureReal_eq
    mu hTI z (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)
      (S.image (P.shift zTop) : Set V)
  rw [hz0, hz1] at htranslate
  calc
    _ = mu.real (E.rectSideConnectionEvent
        (-(M : Real) + i.val) ((M : Real) + i.val)
        (-(M : Real) + height) (M + height : Real)
        (P.shift z '' (S.image (P.shift zTop) : Set V))
        (E.rectTopBoundaryVertices
          (-(M : Real) + i.val) ((M : Real) + i.val)
          (-(M : Real) + height) (M + height : Real))) :=
      htranslate.symm
    _ ≤ mu.real (E.rectSideConnectionEvent
        (-(M : Real)) (M + width : Real)
        (-(M : Real)) (M + height : Real)
        (P.shift z '' (S.image (P.shift zTop) : Set V))
        (E.rectTopBoundaryVertices
          (-(M : Real)) (M + width : Real)
          (-(M : Real)) (M + height : Real))) := by
      apply measureReal_mono (μ := mu)
      apply E.rectTopConnectionEvent_mono_otherBounds
      · norm_num
      · simpa [add_comm] using add_le_add_left hi (M : Real)
      · norm_num
    _ ≤ _ := by
      refine measureReal_mono (μ := mu)
        (E.rectSideConnectionEvent_mono_source ?_)
      rintro x ⟨y, hy, rfl⟩
      change P.shift z y ∈
        (P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift z)
      exact Finset.mem_image.mpr
        ⟨y, P.image_top_subset_fourShiftTemplate S
          zLeft zRight zBottom zTop hy, rfl⟩



theorem PeriodicGraph.fourShiftTemplate_hitsInfinite_tendsto_one
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1)
    (zLeft zRight zBottom zTop : Nat → Site 2) :
    Tendsto (fun n => mu.real (P.setHitsInfinite
      (P.fourShiftTemplate (P.orbitBox n) (zLeft n) (zRight n)
        (zBottom n) (zTop n) : Set V))) atTop (nhds 1) := by
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  let left : Nat → Finset V := fun n =>
    (P.orbitBox n).image (P.shift (zLeft n))
  have hleft : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (left n : Set V))) atTop (nhds 1) := by
    apply hhit.congr'
    filter_upwards with n
    have hset : ((left n : Finset V) : Set V) =
        P.shift (zLeft n) '' (P.orbitBox n : Set V) := by
      ext v
      simp [left]
    rw [hset, P.setHitsInfinite_translate_measureReal_eq mu hTI,
      P.setHitsInfinite_orbitBox]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    hleft tendsto_const_nhds
  · intro n
    exact measureReal_mono (μ := mu) (by
      rintro omega ⟨x, hx, hinfinite⟩
      exact ⟨x, P.image_subset_fourShiftTemplate (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n) hx, hinfinite⟩)
  · exact fun _ => measureReal_le_one

omit [Countable V] in
omit [Countable V] [DecidableEq V] in


theorem isFKG_decreasing
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsDecreasing A) (hB : IsDecreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    mu.real A * mu.real B <= mu.real (A ∩ B) := by
  have hfkg := hFKG Aᶜ Bᶜ hAm.compl hBm.compl hA.compl hB.compl
  have hca : mu.real Aᶜ = 1 - mu.real A := by
    rw [measureReal_compl hAm, probReal_univ]
  have hcb : mu.real Bᶜ = 1 - mu.real B := by
    rw [measureReal_compl hBm, probReal_univ]
  have hcum : mu.real (Aᶜ ∩ Bᶜ) = 1 - mu.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hAm.union hBm), probReal_univ]
  rw [hca, hcb, hcum] at hfkg
  have hie : mu.real (A ∪ B) + mu.real (A ∩ B) =
      mu.real A + mu.real B := measureReal_union_add_inter hBm
  nlinarith

omit [Countable V] [Countable W] [DecidableEq V] [DecidableEq W] in

theorem dualConfigEquiv_antitone (edgeDual : Sym2 V ≃ Sym2 W) :
    Antitone (dualConfigEquiv edgeDual) := by
  intro omega omega' homega f
  have hf := homega (edgeDual.symm f)
  simp only [dualConfigEquiv_apply]
  cases ha : omega (edgeDual.symm f) <;>
    cases hb : omega' (edgeDual.symm f) <;>
      simp_all [Bool.le_iff_imp]



theorem PeriodicPlanarDualPair.dualMeasure_isFKG
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) : IsFKG (D.dualMeasure mu) := by
  intro A B hAm hBm hA hB
  rw [D.dualMeasure_measureReal mu hAm,
    D.dualMeasure_measureReal mu hBm,
    D.dualMeasure_measureReal mu (hAm.inter hBm)]
  rw [Set.preimage_inter]
  apply isFKG_decreasing mu hFKG
  · intro omega omega' homega hmem
    exact hA (dualConfigEquiv_antitone D.edgeDual homega) hmem
  · intro omega omega' homega hmem
    exact hB (dualConfigEquiv_antitone D.edgeDual homega) hmem
  · exact hAm.preimage (continuous_dualConfigEquiv D.edgeDual).measurable
  · exact hBm.preimage (continuous_dualConfigEquiv D.edgeDual).measurable


theorem PeriodicPlanarDualPair.primalUnique_measure_eq_one_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hcommon : mu D.commonUniqueInfiniteClusterEvent = 1) :
    mu {omega | P.HasUniqueInfiniteCluster omega} = 1 := by
  apply le_antisymm prob_le_one
  rw [← hcommon]
  exact measure_mono fun _ h => h.1



theorem PeriodicPlanarDualPair.dualUnique_measure_eq_one_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hcommon : mu D.commonUniqueInfiniteClusterEvent = 1) :
    D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
  let B : Set (ConfigSpace (Sym2 W)) :=
    {eta | Pdual.HasUniqueInfiniteCluster eta}
  have hpre : mu ((dualConfigEquiv D.edgeDual) ⁻¹' B) = 1 := by
    apply le_antisymm prob_le_one
    rw [← hcommon]
    exact measure_mono fun _ h => h.2
  unfold PeriodicPlanarDualPair.dualMeasure
  rw [Measure.map_apply (continuous_dualConfigEquiv D.edgeDual).measurable
    Pdual.measurableSet_hasUniqueInfiniteCluster]
  exact hpre




theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_sheffieldData_of_common
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      mu D.commonUniqueInfiniteClusterEvent = 1) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    IsFKG mu ∧
      P.IsTranslationInvariant mu ∧
      IsFKG (D.dualMeasure mu) ∧
      Pdual.IsTranslationInvariant (D.dualMeasure mu) ∧
      mu {omega | P.HasUniqueInfiniteCluster omega} = 1 ∧
      D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hFKG : IsFKG mu := P.freeBufferedInfiniteVolume_isFKG hp hp1 hq
  have hTI : P.IsTranslationInvariant mu :=
    P.freeBufferedInfiniteVolume_isTranslationInvariant hp hp1 hq
  exact ⟨hFKG, hTI, D.dualMeasure_isFKG mu hFKG,
    D.dualMeasure_isTranslationInvariant mu hTI,
    D.primalUnique_measure_eq_one_of_common mu hcommon,
    D.dualUnique_measure_eq_one_of_common mu hcommon⟩

set_option linter.unusedVariables false in




theorem PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
        atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n)
      (base : Nat → Site 2)
      (a b c d : Nat → Real)
      (bottom top left right : (n : Nat) →
        PreferenceGridVertex (width n) (height n) → Real)
      (pBottom pTop pLeft pRight : Nat → Real),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (base n + preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (a n) (b n) (c n) (d n)) →
      (∀ n v, bottom n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, top n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, left n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n v, right n v = mu.real
        (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
          ((template n).image
            (P.shift (base n + preferenceGridSite v)) : Set V)
          (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) →
      (∀ n, pBottom n ≤ 1) → (∀ n, pTop n ≤ 1) →
      (∀ n, pLeft n ≤ 1) → (∀ n, pRight n ≤ 1) →
      (∀ n (i : Fin (width n + 1)),
        pBottom n ≤ bottom n (i, 0)) →
      (∀ n (i : Fin (width n + 1)),
        pTop n ≤ top n (i, Fin.last (height n))) →
      (∀ n (j : Fin (height n + 1)),
        pLeft n ≤ left n (0, j)) →
      (∀ n (j : Fin (height n + 1)),
        pRight n ≤ right n (Fin.last (width n), j)) →
      Tendsto pBottom atTop (nhds 1) →
      Tendsto pTop atTop (nhds 1) →
      Tendsto pLeft atTop (nhds 1) →
      Tendsto pRight atTop (nhds 1) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
        (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_approxPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight base a b c d
    bottom top left right pBottom pTop pLeft pRight
    hsource hrect hbottomScore htopScore hleftScore hrightScore
    hpBottom hpTop hpLeft hpRight hbottom htop hleft hright
    hpBottomLim hpTopLim hpLeftLim hpRightLim
  let epsilon : Nat → Real := fun n =>
    max (max (1 - pBottom n) (1 - pTop n))
      (max (1 - pLeft n) (1 - pRight n))
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    have hB := (tendsto_const_nhds (x := (1 : Real))).sub hpBottomLim
    have hT := (tendsto_const_nhds (x := (1 : Real))).sub hpTopLim
    have hL := (tendsto_const_nhds (x := (1 : Real))).sub hpLeftLim
    have hR := (tendsto_const_nhds (x := (1 : Real))).sub hpRightLim
    simpa [epsilon] using (hB.max hT).max (hL.max hR)
  apply hcross width height hwidth hheight base a b c d epsilon
    bottom top left right hepsilon
  · intro n
    exact (sub_nonneg.mpr (hpBottom n)).trans
      (le_max_left _ _ |>.trans (le_max_left _ _))
  · exact hsource
  · exact hrect
  · exact hbottomScore
  · exact htopScore
  · exact hleftScore
  · exact hrightScore
  · intro n i
    have hTopLe : top n (i, 0) ≤ 1 := by
      rw [htopScore]
      exact measureReal_le_one
    have hdefect : 1 - pBottom n ≤ epsilon n :=
      (le_max_left _ _).trans (le_max_left _ _)
    linarith [hbottom n i]
  · intro n i
    have hBottomLe : bottom n (i, Fin.last (height n)) ≤ 1 := by
      rw [hbottomScore]
      exact measureReal_le_one
    have hdefect : 1 - pTop n ≤ epsilon n :=
      (le_max_right _ _).trans (le_max_left _ _)
    linarith [htop n i]
  · intro n j
    have hRightLe : right n (0, j) ≤ 1 := by
      rw [hrightScore]
      exact measureReal_le_one
    have hdefect : 1 - pLeft n ≤ epsilon n :=
      (le_max_left _ _).trans (le_max_right _ _)
    linarith [hleft n j]
  · intro n j
    have hLeftLe : left n (Fin.last (width n), j) ≤ 1 := by
      rw [hleftScore]
      exact measureReal_le_one
    have hdefect : 1 - pRight n ≤ epsilon n :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith [hright n j]






theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector
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
    (hleftLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real)) (M n + height n : Real)) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  let template : Nat → Finset V := fun n =>
    P.fourShiftTemplate (P.orbitBox n) (zLeft n) (zRight n)
      (zBottom n) (zTop n)
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h => h.1
  have htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template] using
      P.fourShiftTemplate_hitsInfinite_tendsto_one mu hTI hexists
        zLeft zRight zBottom zTop
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_boundaryLimits_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight hconnector
  let bottom : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (-(M n : Real)) (M n + width n : Real)
      (-(M n : Real)) (M n + height n : Real)
      ((template n).image (P.shift (preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices
        (-(M n : Real)) (M n + width n : Real)
        (-(M n : Real)) (M n + height n : Real)))
  let top : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (-(M n : Real)) (M n + width n : Real)
      (-(M n : Real)) (M n + height n : Real)
      ((template n).image (P.shift (preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices
        (-(M n : Real)) (M n + width n : Real)
        (-(M n : Real)) (M n + height n : Real)))
  let left : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (-(M n : Real)) (M n + width n : Real)
      (-(M n : Real)) (M n + height n : Real)
      ((template n).image (P.shift (preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices
        (-(M n : Real)) (M n + width n : Real)
        (-(M n : Real)) (M n + height n : Real)))
  let right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v =>
    mu.real (E.rectSideConnectionEvent
      (-(M n : Real)) (M n + width n : Real)
      (-(M n : Real)) (M n + height n : Real)
      ((template n).image (P.shift (preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices
        (-(M n : Real)) (M n + width n : Real)
        (-(M n : Real)) (M n + height n : Real)))
  let pBottom : Nat → Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
      (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let pTop : Nat → Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
      (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let pLeft : Nat → Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
      (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let pRight : Nat → Real := fun n => mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
      (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  apply hcross width height hwidth hheight (fun _ => 0)
    (fun n => -(M n : Real)) (fun n => (M n + width n : Real))
    (fun n => -(M n : Real)) (fun n => (M n + height n : Real))
    bottom top left right pBottom pTop pLeft pRight
  · intro n v
    simpa only [template, zero_add] using
      E.fourShiftTemplate_preferenceGrid_subset_rect
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n)
        (hleft n) (hright n) (hbottom n) (htop n) v
  · intro n v
    simpa only [zero_add] using hconnector n v
  · intro n v
    simp [bottom]
  · intro n v
    simp [top]
  · intro n v
    simp [left]
  · intro n v
    simp [right]
  · exact fun _ => measureReal_le_one
  · exact fun _ => measureReal_le_one
  · exact fun _ => measureReal_le_one
  · exact fun _ => measureReal_le_one
  · intro n i
    simpa only [pBottom, bottom, template] using
      E.rectBottomConnection_fourShiftTemplate_le mu hTI
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n) i
  · intro n i
    simpa only [pTop, top, template] using
      E.rectTopConnection_fourShiftTemplate_le mu hTI
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n) i
  · intro n j
    simpa only [pLeft, left, template] using
      E.rectLeftConnection_fourShiftTemplate_le mu hTI
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n) j
  · intro n j
    simpa only [pRight, right, template] using
      E.rectRightConnection_fourShiftTemplate_le mu hTI
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n) j
  · simpa only [pBottom] using hbottomLimit
  · simpa only [pTop] using htopLimit
  · simpa only [pLeft] using hleftLimit
  · simpa only [pRight] using hrightLimit




theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds
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
    (hleftLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1)) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) →
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_fourShiftTemplate_crossing_max_tendsto_one_of_connector
      mu hFKG hTI hunique M zLeft zRight zBottom zTop
        hleft hright hbottom htop hleftLimit hrightLimit
          hbottomLimit htopLimit
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight hx hy
  apply hcross width height hwidth hheight
  intro n v
  exact E.preferenceGrid_orbitBox_subset_rect_of_coordinateBound
    (P.bufferedRadius (radius n)) (M n) (width n) (height n)
      (hx n) (hy n) v






theorem PeriodicPlaneEmbedding.exists_commonSquare_fourShift_crossing_max_tendsto_one_of_coordinateBounds
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2)
      (radius : Nat → Nat), ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) →
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) →
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  obtain ⟨M, baseL, baseR, baseB, baseT,
      hleft, hright, hbottom, htop,
      hleftLimit, hrightLimit, hbottomLimit, htopLimit⟩ :=
    E.exists_commonSquare_fourBoundaryPlacements mu hFKG hTI hunique
      (fun n => n) (fun _ => le_rfl)
  let zLeft : Nat → Site 2 := fun n => baseL n + commonRectLeftShift M n
  let zRight : Nat → Site 2 := fun n => baseR n + commonRectRightShift M n
  let zBottom : Nat → Site 2 := fun n => baseB n + commonRectBottomShift M n
  let zTop : Nat → Site 2 := fun n => baseT n + commonRectTopShift M n
  have hshiftSet (z b : Site 2) (n : Nat) :
      P.shift z '' (P.shift b '' (P.orbitBox n : Set V)) =
        P.shift (b + z) '' (P.orbitBox n : Set V) := by
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, P.shift_add b z u⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨P.shift b u, ⟨u, hu, rfl⟩, (P.shift_add b z u).symm⟩
  have hfinsetSet (z : Site 2) (n : Nat) :
      ((P.orbitBox n).image (P.shift z) : Set V) =
        P.shift z '' (P.orbitBox n : Set V) := by
    ext x
    simp
  have hleft' (n : Nat) :
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    rw [hfinsetSet]
    dsimp only [zLeft]
    rw [← hshiftSet]
    exact hleft n
  have hright' (n : Nat) :
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    rw [hfinsetSet]
    dsimp only [zRight]
    rw [← hshiftSet]
    exact hright n
  have hbottom' (n : Nat) :
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    rw [hfinsetSet]
    dsimp only [zBottom]
    rw [← hshiftSet]
    exact hbottom n
  have htop' (n : Nat) :
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    rw [hfinsetSet]
    dsimp only [zTop]
    rw [← hshiftSet]
    exact htop n
  have hleftLimit' : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1) := by
    simpa only [hfinsetSet, zLeft, ← hshiftSet] using hleftLimit
  have hrightLimit' : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1) := by
    simpa only [hfinsetSet, zRight, ← hshiftSet] using hrightLimit
  have hbottomLimit' : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1) := by
    simpa only [hfinsetSet, zBottom, ← hshiftSet] using hbottomLimit
  have htopLimit' : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1) := by
    simpa only [hfinsetSet, zTop, ← hshiftSet] using htopLimit
  obtain ⟨radius, hcross⟩ :=
    E.exists_fourShiftTemplate_crossing_max_tendsto_one_of_coordinateBounds
      mu hFKG hTI hunique M zLeft zRight zBottom zTop
        hleft' hright' hbottom' htop' hleftLimit' hrightLimit'
          hbottomLimit' htopLimit'
  exact ⟨M, zLeft, zRight, zBottom, zTop, radius, hcross⟩



theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent = 0 ∨
      mu D.commonUniqueInfiniteClusterEvent = 1 := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have herg := D.primalEmbedding.freeBufferedInfiniteVolume_isErgodic
    hp hp1 hq
  exact herg.2 D.commonUniqueInfiniteClusterEvent
    D.commonUniqueInfiniteClusterEvent_measurableSet
    D.commonUniqueInfiniteClusterEvent_translate_preimage



theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_eq_zero_iff_ne_one
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent = 0 ↔
      mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  constructor
  · intro hzero hone
    rw [hzero] at hone
    exact zero_ne_one hone
  · intro hne
    rcases D.freeBufferedInfiniteVolume_commonUnique_measure_zero_or_one
      hp hp1 hq with hzero | hone
    · exact hzero
    · exact (hne hone).elim

end StatMech.FK.PeriodicPlanar
