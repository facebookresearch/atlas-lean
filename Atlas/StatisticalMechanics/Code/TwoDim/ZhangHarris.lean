/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Probability.InfiniteHarris
import Code.TwoDim.ZhangFixedK
import Code.Percolation.DctItem2

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality
open StatMech.RSW.Box

def zih_centerShift (x : Site 2) : Multiplicative (Site 2) :=
  Multiplicative.ofAdd (-x)

def zih_clusterApprox (x : Site 2) (m : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (zih_centerShift x)) ⁻¹' crossingEvent 2 (m + 1)

noncomputable def zih_clusterSupport (x : Site 2) (m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  (boxEdgeFinset 2 (m + 1)).image
    (fun e => (zih_centerShift x)⁻¹ • e)

theorem zih_clusterApprox_dependsOn (x : Site 2) (m : ℕ) :
    StatMech.DependsOn (zih_clusterApprox x m) (zih_clusterSupport x m) := by
  rw [zih_clusterApprox, crossingEvent_eq_boxCrossingEvent (m + 1) (by omega)]
  have hbase : StatMech.DependsOn (Percolation.boxCrossingEvent 2 (m + 1))
      (boxEdgeFinset 2 (m + 1) : Set (Sym2 (Site 2))) :=
    ih_event_dependsOn_of_indicator
      (Percolation.boxCrossingEvent_dependsOn (d := 2) (m + 1))
  intro omega omega' hagree
  apply hbase
  intro e he
  simp only [ConfigSpace.shift_apply]
  apply hagree
  rw [Finset.mem_coe, zih_clusterSupport, Finset.mem_image]
  exact ⟨e, by simpa using he, rfl⟩

theorem zih_clusterApprox_isIncreasing (x : Site 2) (m : ℕ) :
    IsIncreasing (zih_clusterApprox x m) := by
  rw [zih_clusterApprox, crossingEvent_eq_boxCrossingEvent (m + 1) (by omega)]
  intro omega omega' hle hmem
  exact Percolation.boxCrossingEvent_isIncreasing (m + 1) (fun e => hle _) hmem

theorem zih_clusterApprox_measurableSet (x : Site 2) (m : ℕ) :
    MeasurableSet (zih_clusterApprox x m) := by
  unfold zih_clusterApprox
  exact (measurableSet_crossingEvent (d := 2) (m + 1)).preimage
    (ConfigSpace.measurable_shift (zih_centerShift x))

theorem zih_clusterApprox_antitone (x : Site 2) : Antitone (zih_clusterApprox x) := by
  intro m n hmn omega hmem
  exact crossingEvent_antitone (m + 1) (n + 1) (by omega) hmem

theorem zih_cluster_shift_infinite_iff (omega : ConfigSpace (Sym2 (Site 2)))
    (x : Site 2) :
    (cluster 2 (ConfigSpace.shift (zih_centerShift x) omega) (origin 2)).Infinite ↔
      (cluster 2 omega x).Infinite := by
  have hg : zih_centerShift x • x = origin 2 := by
    funext i
    simp [zih_centerShift, smul_site_apply, origin]
  rw [← hg, cluster_shift]
  exact Set.infinite_image_iff
    ((MulAction.injective (zih_centerShift x) : Function.Injective
      (fun y : Site 2 => zih_centerShift x • y)).injOn)

theorem zih_clusterInfinite_eq_iInter (x : Site 2) :
    {omega : ConfigSpace (Sym2 (Site 2)) | (cluster 2 omega x).Infinite} =
      ⋂ m : ℕ, zih_clusterApprox x m := by
  ext omega
  rw [Set.mem_setOf_eq, ← zih_cluster_shift_infinite_iff omega x,
    ← Percolation.mem_percolationEvent, Percolation.percolationEvent_eq_iInter]
  simp only [zih_clusterApprox, Set.mem_iInter, Set.mem_preimage]

noncomputable def zih_leftSquareFinset (N : ℕ) : Finset (Site 2) :=
  (rect_finite (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)).toFinset

noncomputable def zih_leftSquareEdges (N : ℕ) : Finset (Sym2 (Site 2)) :=
  edgesWithinFinset (zih_leftSquareFinset N)

theorem zih_leftArmFrom_dependsOn (x : Site 2) (N : ℕ) :
    StatMech.DependsOn {omega | zfk_LeftArmFrom omega x N}
      (zih_leftSquareEdges N) := by
  intro omega omega' hagree
  have hcoord : ∀ a b : Site 2, a ∈ zfk_leftSquare N → b ∈ zfk_leftSquare N →
      omega s(a, b) = omega' s(a, b) := by
    intro a b ha hb
    symm
    apply hagree
    rw [Finset.mem_coe, zih_leftSquareEdges, mem_edgesWithinFinset]
    refine ⟨a, ?_, b, ?_, rfl⟩ <;>
      simpa [zih_leftSquareFinset, zfk_leftSquare] using ‹_›
  have hG : openSubgraphInduce 2 omega (zfk_leftSquare N) =
      openSubgraphInduce 2 omega' (zfk_leftSquare N) := by
    apply SimpleGraph.ext
    ext a b
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord a b a.2 b.2]
  unfold zfk_LeftArmFrom ConnectedWithin
  simp only [Set.mem_setOf_eq, hG]

def zih_LeftArmApprox (k N m : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ x : zfk_leftCentralFinset k,
    zih_clusterApprox (x : Site 2) m ∩ {omega | zfk_LeftArmFrom omega x N}

noncomputable def zih_leftApproxSupport (k N m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  zih_leftSquareEdges N ∪
    (zfk_leftCentralFinset k).biUnion (fun x => zih_clusterSupport x m)

theorem zih_LeftArmApprox_dependsOn (k N m : ℕ) :
    StatMech.DependsOn (zih_LeftArmApprox k N m)
      (zih_leftApproxSupport k N m) := by
  apply ih_dependsOn_iUnion
  intro x
  apply ih_dependsOn_inter
  · apply (zih_clusterApprox_dependsOn (x : Site 2) m).mono
    intro e he
    rw [Finset.mem_coe, zih_leftApproxSupport, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨x, x.2, he⟩)
  · apply (zih_leftArmFrom_dependsOn (x : Site 2) N).mono
    intro e he
    rw [Finset.mem_coe, zih_leftApproxSupport, Finset.mem_union]
    exact Or.inl he

theorem zih_LeftArmApprox_isIncreasing (k N m : ℕ) :
    IsIncreasing (zih_LeftArmApprox k N m) := by
  intro omega omega' hle
  simp only [zih_LeftArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨x, hx, harm⟩
  rcases harm with ⟨hxS, a, hax⟩
  exact ⟨x, zih_clusterApprox_isIncreasing x m hle hx, hxS, a,
    StatMech.TwoDim.connectedWithin_mono hle hax⟩

theorem zih_LeftArmApprox_measurableSet (k N m : ℕ) :
    MeasurableSet (zih_LeftArmApprox k N m) := by
  exact measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (zih_LeftArmApprox_dependsOn k N m))

theorem zih_LeftArmApprox_antitone (k N : ℕ) :
    Antitone (zih_LeftArmApprox k N) := by
  intro m n hmn omega
  simp only [zih_LeftArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨x, hx, harm⟩
  exact ⟨x, zih_clusterApprox_antitone x hmn hx, harm⟩

theorem zih_LeftArmEvent_eq_iInter (k N : ℕ) :
    zfk_LeftArmEvent k N = ⋂ m : ℕ, zih_LeftArmApprox k N m := by
  change zfk_LeftArmEvent k N = ⋂ m : ℕ, ⋃ x : zfk_leftCentralFinset k,
    zih_clusterApprox (x : Site 2) m ∩ {omega | zfk_LeftArmFrom omega x N}
  rw [iInter_iUnion_of_antitone]
  · ext omega
    simp only [zfk_LeftArmEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hxK, hxInf, harm⟩
      let xf : zfk_leftCentralFinset k := ⟨x, zfk_mem_leftCentralFinset.mpr hxK⟩
      refine ⟨xf, ?_⟩
      have hxi : omega ∈ ⋂ m, zih_clusterApprox x m :=
        (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter x) omega).mp hxInf
      have hxi' : ∀ m, omega ∈ zih_clusterApprox x m := by
        simpa only [Set.mem_iInter] using hxi
      intro m
      exact ⟨hxi' m, harm⟩
    · rintro ⟨x, hx⟩
      have hca : (cluster 2 omega (x : Site 2)).Infinite := by
        exact (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter (x : Site 2)) omega).mpr
          (by simpa only [Set.mem_iInter] using (fun m => (hx m).1))
      exact ⟨x, zfk_mem_leftCentralFinset.mp x.2, hca, (hx 0).2⟩
  · intro x
    exact fun m n hmn => inter_subset_inter (zih_clusterApprox_antitone x hmn)
      Subset.rfl

noncomputable def zih_rightSquareFinset (N : ℕ) : Finset (Site 2) :=
  (rect_finite (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)).toFinset

noncomputable def zih_rightSquareEdges (N : ℕ) : Finset (Sym2 (Site 2)) :=
  edgesWithinFinset (zih_rightSquareFinset N)

theorem zih_rightArmFrom_dependsOn (y : Site 2) (N : ℕ) :
    StatMech.DependsOn {omega | zfk_RightArmFrom omega y N}
      (zih_rightSquareEdges N) := by
  intro omega omega' hagree
  have hcoord : ∀ a b : Site 2, a ∈ zfk_rightSquare N → b ∈ zfk_rightSquare N →
      omega s(a, b) = omega' s(a, b) := by
    intro a b ha hb
    symm
    apply hagree
    rw [Finset.mem_coe, zih_rightSquareEdges, mem_edgesWithinFinset]
    refine ⟨a, ?_, b, ?_, rfl⟩ <;>
      simpa [zih_rightSquareFinset, zfk_rightSquare] using ‹_›
  have hG : openSubgraphInduce 2 omega (zfk_rightSquare N) =
      openSubgraphInduce 2 omega' (zfk_rightSquare N) := by
    apply SimpleGraph.ext
    ext a b
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord a b a.2 b.2]
  unfold zfk_RightArmFrom ConnectedWithin
  simp only [Set.mem_setOf_eq, hG]

def zih_RightArmApprox (k N m : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ y : zfk_rightCentralFinset k,
    zih_clusterApprox (y : Site 2) m ∩ {omega | zfk_RightArmFrom omega y N}

noncomputable def zih_rightApproxSupport (k N m : ℕ) :
    Finset (Sym2 (Site 2)) :=
  zih_rightSquareEdges N ∪
    (zfk_rightCentralFinset k).biUnion (fun y => zih_clusterSupport y m)

theorem zih_RightArmApprox_dependsOn (k N m : ℕ) :
    StatMech.DependsOn (zih_RightArmApprox k N m)
      (zih_rightApproxSupport k N m) := by
  apply ih_dependsOn_iUnion
  intro y
  apply ih_dependsOn_inter
  · apply (zih_clusterApprox_dependsOn (y : Site 2) m).mono
    intro e he
    rw [Finset.mem_coe, zih_rightApproxSupport, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨y, y.2, he⟩)
  · apply (zih_rightArmFrom_dependsOn (y : Site 2) N).mono
    intro e he
    rw [Finset.mem_coe, zih_rightApproxSupport, Finset.mem_union]
    exact Or.inl he

theorem zih_RightArmApprox_isIncreasing (k N m : ℕ) :
    IsIncreasing (zih_RightArmApprox k N m) := by
  intro omega omega' hle
  simp only [zih_RightArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨y, hy, harm⟩
  rcases harm with ⟨hyS, b, hyb⟩
  exact ⟨y, zih_clusterApprox_isIncreasing y m hle hy, hyS, b,
    StatMech.TwoDim.connectedWithin_mono hle hyb⟩

theorem zih_RightArmApprox_measurableSet (k N m : ℕ) :
    MeasurableSet (zih_RightArmApprox k N m) :=
  measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (zih_RightArmApprox_dependsOn k N m))

theorem zih_RightArmApprox_antitone (k N : ℕ) :
    Antitone (zih_RightArmApprox k N) := by
  intro m n hmn omega
  simp only [zih_RightArmApprox, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  rintro ⟨y, hy, harm⟩
  exact ⟨y, zih_clusterApprox_antitone y hmn hy, harm⟩

theorem zih_RightArmEvent_eq_iInter (k N : ℕ) :
    zfk_RightArmEvent k N = ⋂ m : ℕ, zih_RightArmApprox k N m := by
  change zfk_RightArmEvent k N = ⋂ m : ℕ, ⋃ y : zfk_rightCentralFinset k,
    zih_clusterApprox (y : Site 2) m ∩ {omega | zfk_RightArmFrom omega y N}
  rw [iInter_iUnion_of_antitone]
  · ext omega
    simp only [zfk_RightArmEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨y, hyK, hyInf, harm⟩
      let yf : zfk_rightCentralFinset k :=
        ⟨y, zfk_mem_rightCentralFinset.mpr hyK⟩
      refine ⟨yf, ?_⟩
      have hyi : omega ∈ ⋂ m, zih_clusterApprox y m :=
        (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter y) omega).mp hyInf
      have hyi' : ∀ m, omega ∈ zih_clusterApprox y m := by
        simpa only [Set.mem_iInter] using hyi
      intro m
      exact ⟨hyi' m, harm⟩
    · rintro ⟨y, hy⟩
      have hca : (cluster 2 omega (y : Site 2)).Infinite := by
        exact (Set.ext_iff.mp (zih_clusterInfinite_eq_iInter (y : Site 2)) omega).mpr
          (by simpa only [Set.mem_iInter] using (fun m => (hy m).1))
      exact ⟨y, zfk_mem_rightCentralFinset.mp y.2, hca, (hy 0).2⟩
  · intro y
    exact fun m n hmn => inter_subset_inter (zih_clusterApprox_antitone y hmn)
      Subset.rfl

theorem zih_armPair_fkg (k N : ℕ) :
    halfMeasure.real (zfk_LeftArmEvent k N) *
        halfMeasure.real (zfk_RightArmEvent k N) ≤
      halfMeasure.real (zfk_ArmPairEvent k N) := by
  let F : ℕ → Finset (Sym2 (Site 2)) := fun m =>
    zih_leftApproxSupport k N m ∪ zih_rightApproxSupport k N m
  have hstage : ∀ m,
      halfMeasure.real (zih_LeftArmApprox k N m) *
          halfMeasure.real (zih_RightArmApprox k N m) ≤
        halfMeasure.real
          (zih_LeftArmApprox k N m ∩ zih_RightArmApprox k N m) := by
    intro m
    apply ih_harris_of_finite_dependsOn half_le_one (F m)
    · apply (zih_LeftArmApprox_dependsOn k N m).mono
      intro e he
      exact Finset.mem_union_left _ he
    · apply (zih_RightArmApprox_dependsOn k N m).mono
      intro e he
      exact Finset.mem_union_right _ he
    · exact zih_LeftArmApprox_isIncreasing k N m
    · exact zih_RightArmApprox_isIncreasing k N m
  have hlim := ih_harris_iInter_of_antitone halfMeasure
    (zih_LeftArmApprox k N) (zih_RightArmApprox k N)
    (zih_LeftArmApprox_antitone k N) (zih_RightArmApprox_antitone k N)
    (zih_LeftArmApprox_measurableSet k N) (zih_RightArmApprox_measurableSet k N)
    hstage
  rw [← zih_LeftArmEvent_eq_iInter, ← zih_RightArmEvent_eq_iInter,
    ← zfk_armPair_eq_inter] at hlim
  exact hlim

noncomputable def zih_rotSupport (F : Finset (Sym2 (Site 2))) :
    Finset (Sym2 (Site 2)) := F.image kdi_rotEdgeEquiv.symm

theorem zih_rot_dependsOn {A : Set (ConfigSpace (Sym2 (Site 2)))}
    {F : Finset (Sym2 (Site 2))} (hA : StatMech.DependsOn A F) :
    StatMech.DependsOn (zrs_rot A) (zih_rotSupport F) := by
  intro omega omega' hagree
  apply hA
  intro e he
  simp only [zrs_rot, Set.mem_preimage, zrs_rotConfig_apply]
  apply hagree
  rw [Finset.mem_coe, zih_rotSupport, Finset.mem_image]
  exact ⟨e, by simpa using he, rfl⟩

noncomputable def zih_sideSupport (F : Finset (Sym2 (Site 2))) (i : Fin 4) :
    Finset (Sym2 (Site 2)) :=
  match i with
  | 0 => F
  | 1 => zih_rotSupport (zih_rotSupport F)
  | 2 => zih_rotSupport F
  | 3 => zih_rotSupport (zih_rotSupport (zih_rotSupport F))

theorem zih_sideFamily_dependsOn {A : Set (ConfigSpace (Sym2 (Site 2)))}
    {F : Finset (Sym2 (Site 2))} (hA : StatMech.DependsOn A F) (i : Fin 4) :
    StatMech.DependsOn (zrs_sideFamily A i) (zih_sideSupport F i) := by
  fin_cases i
  · exact hA
  · exact zih_rot_dependsOn (zih_rot_dependsOn hA)
  · exact zih_rot_dependsOn hA
  · exact zih_rot_dependsOn (zih_rot_dependsOn (zih_rot_dependsOn hA))

theorem zih_complUnion_bound_of_finite_dependsOn
    {A B : Set (ConfigSpace (Sym2 (Site 2)))} (F : Finset (Sym2 (Site 2)))
    (hAdep : StatMech.DependsOn A F) (hBdep : StatMech.DependsOn B F)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (1 - halfMeasure.real A) * (1 - halfMeasure.real B) ≤
      1 - halfMeasure.real (A ∪ B) := by
  have hfkg := ih_harris_of_finite_dependsOn half_le_one F
    hAdep hBdep hAinc hBinc
  change halfMeasure.real A * halfMeasure.real B ≤ halfMeasure.real (A ∩ B) at hfkg
  have hie : halfMeasure.real (A ∪ B) + halfMeasure.real (A ∩ B) =
      halfMeasure.real A + halfMeasure.real B :=
    measureReal_union_add_inter hBm
  nlinarith

theorem zih_complUnion_four_of_finite_dependsOn
    {A B C D : Set (ConfigSpace (Sym2 (Site 2)))} (F : Finset (Sym2 (Site 2)))
    (hAdep : StatMech.DependsOn A F) (hBdep : StatMech.DependsOn B F)
    (hCdep : StatMech.DependsOn C F) (hDdep : StatMech.DependsOn D F)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (hCinc : IsIncreasing C) (hDinc : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D) :
    (1 - halfMeasure.real A) * (1 - halfMeasure.real B) *
        (1 - halfMeasure.real C) * (1 - halfMeasure.real D) ≤
      1 - halfMeasure.real (A ∪ B ∪ C ∪ D) := by
  have hABdep : StatMech.DependsOn (A ∪ B) F := by
    intro omega omega' hagree
    simp only [Set.mem_union, hAdep omega omega' hagree, hBdep omega omega' hagree]
  have hABCdep : StatMech.DependsOn (A ∪ B ∪ C) F := by
    intro omega omega' hagree
    simp only [Set.mem_union, hAdep omega omega' hagree, hBdep omega omega' hagree,
      hCdep omega omega' hagree]
  have h1 := zih_complUnion_bound_of_finite_dependsOn F hAdep hBdep
    hAinc hBinc hAm hBm
  have h2 := zih_complUnion_bound_of_finite_dependsOn F hABdep hCdep
    (hAinc.union hBinc) hCinc (hAm.union hBm) hCm
  have h3 := zih_complUnion_bound_of_finite_dependsOn F hABCdep hDdep
    ((hAinc.union hBinc).union hCinc) hDinc ((hAm.union hBm).union hCm) hDm
  have nC : 0 ≤ 1 - halfMeasure.real C := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := C)]
  have nD : 0 ≤ 1 - halfMeasure.real D := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := D)]
  calc
    _ ≤ (1 - halfMeasure.real (A ∪ B)) * (1 - halfMeasure.real C) *
        (1 - halfMeasure.real D) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 nC) nD
    _ ≤ (1 - halfMeasure.real (A ∪ B ∪ C)) *
        (1 - halfMeasure.real D) := mul_le_mul_of_nonneg_right h2 nD
    _ ≤ _ := h3

theorem zih_sideApprox_antitone (k N : ℕ) (i : Fin 4) :
    Antitone (fun m => zrs_sideFamily (zih_LeftArmApprox k N m) i) := by
  intro m n hmn
  have hbase := zih_LeftArmApprox_antitone k N hmn
  fin_cases i
  · exact hbase
  · exact Set.preimage_mono (Set.preimage_mono hbase)
  · exact Set.preimage_mono hbase
  · exact Set.preimage_mono (Set.preimage_mono (Set.preimage_mono hbase))

theorem zih_sideApprox_iInter (k N : ℕ) (i : Fin 4) :
    (⋂ m, zrs_sideFamily (zih_LeftArmApprox k N m) i) =
      zrs_sideFamily (zfk_LeftArmEvent k N) i := by
  rw [zih_LeftArmEvent_eq_iInter]
  fin_cases i <;> ext omega <;>
    simp [zrs_sideFamily, zrs_rot]

theorem zih_complUnion_four_left (k N : ℕ) :
    let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
    (1 - halfMeasure.real (S 0)) * (1 - halfMeasure.real (S 1)) *
        (1 - halfMeasure.real (S 2)) * (1 - halfMeasure.real (S 3)) ≤
      1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
  let S : Fin 4 → ℕ → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i m => zrs_sideFamily (zih_LeftArmApprox k N m) i
  let F : ℕ → Finset (Sym2 (Site 2)) := fun m =>
    Finset.univ.biUnion (fun i : Fin 4 => zih_sideSupport (zih_leftApproxSupport k N m) i)
  have hdep : ∀ i m, StatMech.DependsOn (S i m) (F m) := by
    intro i m
    apply (zih_sideFamily_dependsOn (zih_LeftArmApprox_dependsOn k N m) i).mono
    intro e he
    change e ∈ Finset.univ.biUnion
      (fun i : Fin 4 => zih_sideSupport (zih_leftApproxSupport k N m) i)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩
  have hinc : ∀ i m, IsIncreasing (S i m) := fun i m =>
    zrs_sideFamily_isIncreasing (zih_LeftArmApprox_isIncreasing k N m) i
  have hmeas : ∀ i m, MeasurableSet (S i m) := fun i m =>
    zrs_sideFamily_measurableSet (zih_LeftArmApprox_measurableSet k N m) i
  have hstage : ∀ m,
      (1 - halfMeasure.real (S 0 m)) * (1 - halfMeasure.real (S 1 m)) *
          (1 - halfMeasure.real (S 2 m)) * (1 - halfMeasure.real (S 3 m)) ≤
        1 - halfMeasure.real (S 0 m ∪ S 1 m ∪ S 2 m ∪ S 3 m) := by
    intro m
    exact zih_complUnion_four_of_finite_dependsOn (F m)
      (hdep 0 m) (hdep 1 m) (hdep 2 m) (hdep 3 m)
      (hinc 0 m) (hinc 1 m) (hinc 2 m) (hinc 3 m)
      (hmeas 0 m) (hmeas 1 m) (hmeas 2 m) (hmeas 3 m)
  let U : ℕ → Set (ConfigSpace (Sym2 (Site 2))) := fun m => ⋃ i : Fin 4, S i m
  have hUeq (m : ℕ) : U m = S 0 m ∪ S 1 m ∪ S 2 m ∪ S 3 m := by
    ext omega
    simp only [U, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro h
      rcases h with ((h0 | h1) | h2) | h3
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
  have hUanti : Antitone U := by
    intro m n hmn omega
    simp only [U, Set.mem_iUnion]
    rintro ⟨i, hi⟩
    exact ⟨i, zih_sideApprox_antitone k N i hmn hi⟩
  have hUmeas : ∀ m, MeasurableSet (U m) := fun m => by
    apply MeasurableSet.iUnion
    exact fun i => hmeas i m
  have hSi : ∀ i, (⋂ m, S i m) = zrs_sideFamily (zfk_LeftArmEvent k N) i :=
    fun i => zih_sideApprox_iInter k N i
  have hUi : (⋂ m, U m) = ⋃ i : Fin 4, zrs_sideFamily (zfk_LeftArmEvent k N) i := by
    change (⋂ m, ⋃ i : Fin 4, S i m) = _
    rw [iInter_iUnion_of_antitone (fun i => zih_sideApprox_antitone k N i)]
    congr 1
    funext i
    exact hSi i
  have hT (i : Fin 4) : Tendsto (fun m => halfMeasure.real (S i m)) atTop
      (nhds (halfMeasure.real (zrs_sideFamily (zfk_LeftArmEvent k N) i))) := by
    rw [← hSi i]
    exact ih_tendsto_measureReal_iInter halfMeasure (S i)
      (zih_sideApprox_antitone k N i) (hmeas i)
  have hUT : Tendsto (fun m => halfMeasure.real (U m)) atTop
      (nhds (halfMeasure.real (⋃ i : Fin 4, zrs_sideFamily (zfk_LeftArmEvent k N) i))) := by
    rw [← hUi]
    exact ih_tendsto_measureReal_iInter halfMeasure U hUanti hUmeas
  have hleft := (((hT 0).const_sub 1).mul ((hT 1).const_sub 1)).mul
    ((hT 2).const_sub 1) |>.mul ((hT 3).const_sub 1)
  have hright := hUT.const_sub 1
  have hlim := le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall fun m => by simpa [hUeq m] using hstage m)
  let T := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
  change (1 - halfMeasure.real (T 0)) * (1 - halfMeasure.real (T 1)) *
      (1 - halfMeasure.real (T 2)) * (1 - halfMeasure.real (T 3)) ≤
    1 - halfMeasure.real (T 0 ∪ T 1 ∪ T 2 ∪ T 3)
  have hTU : (⋃ i : Fin 4, T i) = T 0 ∪ T 1 ∪ T 2 ∪ T 3 := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro h
      rcases h with ((h0 | h1) | h2) | h3
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
  rwa [hTU] at hlim

theorem zih_sqrt_trick_left (k N : ℕ) :
    let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
    1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
        ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by
  let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
  have hprod := zih_complUnion_four_left k N
  have hsym (i : Fin 4) : halfMeasure.real (S i) = halfMeasure.real (S 0) :=
    zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) i
  have hpow : (1 - halfMeasure.real (S 0)) ^ 4 ≤
      1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    have hrw : (1 - halfMeasure.real (S 0)) * (1 - halfMeasure.real (S 1)) *
        (1 - halfMeasure.real (S 2)) * (1 - halfMeasure.real (S 3)) =
        (1 - halfMeasure.real (S 0)) ^ 4 := by
      rw [hsym 1, hsym 2, hsym 3]
      ring
    linarith
  have nA : 0 ≤ 1 - halfMeasure.real (S 0) := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := S 0)]
  set u := halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)
  have hroot : 1 - halfMeasure.real (S 0) ≤ (1 - u) ^ ((1 : ℝ) / 4) := by
    have hmono : ((1 - halfMeasure.real (S 0)) ^ 4) ^ ((1 : ℝ) / 4) ≤
        (1 - u) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    have hreduce : ((1 - halfMeasure.real (S 0)) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) =
        1 - halfMeasure.real (S 0) := by
      rw [← Real.rpow_natCast (1 - halfMeasure.real (S 0)) 4,
        ← Real.rpow_mul nA]
      norm_num
    rwa [hreduce] at hmono
  linarith

theorem zih_armLower_le_left (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
  let S : Fin 4 → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => zrs_sideFamily (zfk_LeftArmEvent k N) i
  have hsqrt := zih_sqrt_trick_left k N
  have hmono : halfMeasure.real (zbd_boxHitsInfinite k) ≤
      halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) :=
    measureReal_mono (zfk_boxHitsInfinite_subset_armUnion k N hkN)
      (measure_ne_top _ _)
  have hU0 : 0 ≤ 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := S 0 ∪ S 1 ∪ S 2 ∪ S 3)]
  have hcomp : 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) ≤
      1 - halfMeasure.real (zbd_boxHitsInfinite k) := by linarith
  have hrpow := Real.rpow_le_rpow hU0 hcomp (by norm_num : (0 : ℝ) ≤ 1 / 4)
  change 1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) at hsqrt
  change (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤
    (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^ ((1 : ℝ) / 4) at hrpow
  have hfinal : 1 - (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by linarith
  simpa [zfk_armLower, S] using hfinal

theorem zih_armLower_le_right (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
  rw [zfk_right_prob_eq_left]
  exact zih_armLower_le_left k N hkN

theorem zih_fixedK_contradiction
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2))
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    False := by
  have hk : ∀ k, zfk_armLower k * zfk_armLower k ≤ (1 : ℝ) / 2 := by
    intro k
    have hpoint : ∀ N, k + 1 ≤ N →
        zfk_armLower k * zfk_armLower k ≤ (1 : ℝ) / 2 +
          halfMeasure.real (zfk_pairErrorUnion k N) := by
      intro N hkN
      calc
        zfk_armLower k * zfk_armLower k ≤
            halfMeasure.real (zfk_LeftArmEvent k N) *
              halfMeasure.real (zfk_RightArmEvent k N) := by
          exact mul_le_mul (zih_armLower_le_left k N (by omega))
            (zih_armLower_le_right k N (by omega))
            (zfk_armLower_nonneg k) measureReal_nonneg
        _ ≤ halfMeasure.real (zfk_ArmPairEvent k N) := zih_armPair_fkg k N
        _ ≤ halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
              (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
              halfMeasure.real (zfk_pairErrorUnion k N) :=
          zfk_armPair_probability_le_crossing_add_error k N
        _ ≤ (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N) := by
          gcongr
          exact hhalf N
    have hlim : Tendsto
        (fun N => (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N))
        atTop (nhds ((1 : ℝ) / 2)) := by
      simpa using tendsto_const_nhds.add (zfk_pairErrorUnion_tendsto_zero k)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      ((eventually_ge_atTop (k + 1)).mono fun N hN => hpoint N hN)
  have hq := zfk_armLower_tendsto_one hpos
  have hqq : Tendsto (fun k => zfk_armLower k * zfk_armLower k)
      atTop (nhds 1) := by
    simpa using hq.mul hq
  have hbad : (1 : ℝ) ≤ (1 : ℝ) / 2 :=
    le_of_tendsto_of_tendsto hqq tendsto_const_nhds
      (Filter.Eventually.of_forall hk)
  norm_num at hbad

theorem zih_thetaReal_zero_of_matched_half
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    halfMeasure.real (Universality.percolationEvent 2) = 0 := by
  by_contra hne
  exact zih_fixedK_contradiction
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)) hhalf

theorem zih_percolationProbability_zero_of_matched_half
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  unfold Universality.percolationProbability
  have hr := zih_thetaReal_zero_of_matched_half hhalf
  have hle : halfMeasure (Universality.percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right
    (ne_top_of_le_ne_top (by simp) hle)

theorem zih_percolationProbability_zero_of_faithful_exclusive
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
    Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  zih_percolationProbability_zero_of_matched_half
    (fun N => zfk_matched_half_of_faithful_exclusive N (hexcl N))

theorem zih_criticalProbability_eq_half_of_faithful_exclusive
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
    criticalProbability 2 = (1 : ℝ) / 2 := by
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical
      (zih_percolationProbability_zero_of_faithful_exclusive hexcl)
  have hle := kbw_criticalProbability_le_half_square_faithful
    hmeasGenH hmeasFace hmeasThin
  linarith


end StatMech.TwoDim
