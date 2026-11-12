/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FK.PeriodicPlanarSheffield

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





def PeriodicGraph.connectedWithinSet
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ l : List V,
    List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
    (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
    ∀ v ∈ x :: l, v ∈ A}

theorem PeriodicGraph.connectedWithinSet_measurableSet
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    MeasurableSet (P.connectedWithinSet A x y) := by
  classical
  have heq : P.connectedWithinSet A x y =
      ⋃ l : List V, if
        (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
          ∀ v ∈ x :: l, v ∈ A
        then {omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)}
        else ∅ := by
    ext omega
    simp only [PeriodicGraph.connectedWithinSet, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨l, hchain, hlast, hA⟩
      refine ⟨l, ?_⟩
      rw [if_pos ⟨hlast, hA⟩]
      exact hchain
    · rintro ⟨l, hl⟩
      split_ifs at hl with h
      · exact ⟨l, hl, h.1, h.2⟩
      · exact False.elim (by simpa using hl)
  rw [heq]
  exact MeasurableSet.iUnion fun l => by
    split_ifs
    · exact P.measurableSet_openChain_sheffield (x :: l)
    · exact MeasurableSet.empty

theorem PeriodicGraph.connectedWithinSet_isIncreasing
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    IsIncreasing (P.connectedWithinSet A x y) := by
  intro omega eta home
  rintro ⟨l, hchain, hlast, hA⟩
  refine ⟨l, hchain.imp ?_, hlast, hA⟩
  intro a b hab
  rw [P.openSubgraph_adj] at hab ⊢
  refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hab.2] using home s(a, b)

theorem PeriodicGraph.connectedWithinSet_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (x y : V) :
    P.connectedWithinSet A x y ⊆ P.connectedWithinSet B x y := by
  rintro omega ⟨l, hchain, hlast, hA⟩
  exact ⟨l, hchain, hlast, fun v hv => hAB (hA v hv)⟩



theorem PeriodicGraph.connectedWithinSet_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) (x y : V) :
    P.configTranslate z omega ∈
        P.connectedWithinSet (P.shift z '' A) (P.shift z x) (P.shift z y) ↔
      omega ∈ P.connectedWithinSet A x y := by
  constructor
  · rintro ⟨l, hchain, hlast, hregion⟩
    let l₀ := l.map (P.shift (-z))
    refine ⟨l₀, ?_, ?_, ?_⟩
    · have hmap := List.isChain_map_of_isChain (P.shift (-z))
          (fun a b hab =>
            (P.openSubgraphTranslateHom (-z)
              (P.configTranslate z omega)).map_rel hab) hchain
      simpa [l₀] using hmap
    · calc
        (x :: l₀).getLast (List.cons_ne_nil _ _) =
            (P.shift (-z))
              ((P.shift z x :: l).getLast (List.cons_ne_nil _ _)) := by
                simpa [l₀] using
                  (List.getLast_map
                    (f := P.shift (-z))
                    (l := P.shift z x :: l) (by simp))
        _ = (P.shift (-z)) (P.shift z y) := congrArg (P.shift (-z)) hlast
        _ = y := P.shift_neg_shift z y
    · intro v hv
      have hvmap : P.shift z v ∈ P.shift z x :: l := by
        have := List.mem_map_of_mem (f := P.shift z) hv
        simpa [l₀, List.map_map, Function.comp_def] using this
      obtain ⟨a, ha, hav⟩ := hregion (P.shift z v) hvmap
      have hav' : a = v := (P.shift z).injective hav
      simpa only [hav'] using ha
  · rintro ⟨l, hchain, hlast, hregion⟩
    let lz := l.map (P.shift z)
    refine ⟨lz, ?_, ?_, ?_⟩
    · have hmap := List.isChain_map_of_isChain (P.shift z)
          (fun a b hab => (P.openSubgraphTranslateHom z omega).map_rel hab)
          hchain
      simpa [lz] using hmap
    · calc
        (P.shift z x :: lz).getLast (List.cons_ne_nil _ _) =
            P.shift z ((x :: l).getLast (List.cons_ne_nil _ _)) := by
              simpa [lz] using
                (List.getLast_map
                  (f := P.shift z) (l := x :: l) (by simp))
        _ = P.shift z y := congrArg (P.shift z) hlast
    · intro v hv
      change v ∈ P.shift z x :: l.map (P.shift z) at hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        exact ⟨x, hregion x (by simp), rfl⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        exact ⟨a, hregion a (by simp [ha]), rfl⟩


def PeriodicGraph.setConnectionWithin
    (P : PeriodicGraph V) (A S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, ∃ y ∈ T, omega ∈ P.connectedWithinSet A x y}

theorem PeriodicGraph.setConnectionWithin_measurableSet
    (P : PeriodicGraph V) (A S T : Set V) :
    MeasurableSet (P.setConnectionWithin A S T) := by
  have heq : P.setConnectionWithin A S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S), ⋃ y : V, ⋃ (_hy : y ∈ T),
        P.connectedWithinSet A x y := by
    ext omega
    simp [PeriodicGraph.setConnectionWithin]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      P.connectedWithinSet_measurableSet A x y

theorem PeriodicGraph.setConnectionWithin_isIncreasing
    (P : PeriodicGraph V) (A S T : Set V) :
    IsIncreasing (P.setConnectionWithin A S T) := by
  intro omega eta home
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    P.connectedWithinSet_isIncreasing A x y home hxy⟩

theorem PeriodicGraph.setConnectionWithin_union_target
    (P : PeriodicGraph V) (A S T U : Set V) :
    P.setConnectionWithin A S (T ∪ U) =
      P.setConnectionWithin A S T ∪ P.setConnectionWithin A S U := by
  ext omega
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    rcases hy with hy | hy
    · exact Or.inl ⟨x, hx, y, hy, hxy⟩
    · exact Or.inr ⟨x, hx, y, hy, hxy⟩
  · rintro (h | h)
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact ⟨x, hx, y, Or.inl hy, hxy⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := h
      exact ⟨x, hx, y, Or.inr hy, hxy⟩






theorem directional_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hBA : mu.real B ≤ mu.real A) :
    1 - Real.sqrt (1 - mu.real (A ∪ B)) ≤ mu.real A := by
  have h := measurable_sqrt_trick mu hFKG hA hB hAm hBm
  rwa [max_eq_left hBA] at h



theorem three_event_intersection_lower_bound
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {A B C : Set (ConfigSpace (Sym2 V))}
    (hBm : MeasurableSet B) (hCm : MeasurableSet C) :
    mu.real A + mu.real B + mu.real C - 2 ≤
      mu.real ((A ∩ B) ∩ C) := by
  have pairLower {S T : Set (ConfigSpace (Sym2 V))}
      (hTm : MeasurableSet T) :
      mu.real S + mu.real T - 1 ≤ mu.real (S ∩ T) := by
    have hie := measureReal_union_add_inter (μ := mu) (s := S) hTm
    have hu : mu.real (S ∪ T) ≤ 1 := measureReal_le_one
    linarith
  have hAB := pairLower (S := A) (T := B) hBm
  have hABC := pairLower (S := A ∩ B) (T := C) hCm
  linarith




def PeriodicPlaneEmbedding.rightHalfPlaneVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | r ≤ E.vertexCoord x 0}



def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | x ∈ E.rightHalfPlaneVertices r ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < r}


def PeriodicPlaneEmbedding.lowerBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | E.vertexCoord x 1 ≤ s}


def PeriodicPlaneEmbedding.upperBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | s ≤ E.vertexCoord x 1}

theorem PeriodicPlaneEmbedding.boundary_eq_lower_union_upper
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) :
    E.rightHalfPlaneBoundaryVertices r =
      E.lowerBoundaryRayVertices r s ∪ E.upperBoundaryRayVertices r s := by
  ext x
  constructor
  · intro hx
    rcases le_total (E.vertexCoord x 1) s with hxs | hsx
    · exact Or.inl ⟨hx, hxs⟩
    · exact Or.inr ⟨hx, hsx⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx



theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B r : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : V} (hx : x ∈ E.rightHalfPlaneBoundaryVertices r) :
    E.vertexCoord x 0 < r + B := by
  obtain ⟨_hxr, y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x) 0 =
      E.vertexCoord y 0 - E.vertexCoord x 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith



theorem PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (r s : ℝ) (S : Set V)
    (hcomp : mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s))) :
    1 - Real.sqrt (1 - mu.real
        (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
          (E.rightHalfPlaneBoundaryVertices r))) ≤
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  let L := P.setConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.lowerBoundaryRayVertices r s)
  let U := P.setConnectionWithin (E.rightHalfPlaneVertices r) S
    (E.upperBoundaryRayVertices r s)
  have hsqrt := directional_sqrt_trick mu hFKG
    (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) S
      (E.lowerBoundaryRayVertices r s))
    (P.setConnectionWithin_isIncreasing (E.rightHalfPlaneVertices r) S
      (E.upperBoundaryRayVertices r s))
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) S
      (E.lowerBoundaryRayVertices r s))
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r) S
      (E.upperBoundaryRayVertices r s)) hcomp
  change 1 - Real.sqrt (1 - mu.real (L ∪ U)) ≤ mu.real L at hsqrt
  rw [← P.setConnectionWithin_union_target, ← E.boundary_eq_lower_union_upper]
    at hsqrt
  exact hsqrt



theorem PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z : Site 2, ∀ v ∈ P.orbitBox N,
      P.shift z v ∈ E.rightHalfPlaneVertices r := by
  classical
  let M : ℝ := ∑ v ∈ P.orbitBox N, |r - E.vertexCoord v 0|
  obtain ⟨n, hn⟩ := exists_nat_ge M
  let z : Site 2 := fun _ => (n : ℤ)
  refine ⟨z, ?_⟩
  intro v hv
  have hterm : |r - E.vertexCoord v 0| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _hw => abs_nonneg (r - E.vertexCoord w 0)) hv
  have hdiff : r - E.vertexCoord v 0 ≤ M :=
    (le_abs_self (r - E.vertexCoord v 0)).trans hterm
  change r ≤ E.vertexCoord (P.shift z v) 0
  rw [E.vertexCoord_shift]
  change r ≤ E.vertexCoord v 0 + (n : ℝ)
  linarith



theorem PeriodicPlaneEmbedding.exists_shift_connectedWithinOrbit_into_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) :
    ∃ z : Site 2, ∀ (omega : ConfigSpace (Sym2 V)) (x y : V),
      omega ∈ P.connectedWithinOrbit x y N →
        P.configTranslate z omega ∈
          P.connectedWithinSet (E.rightHalfPlaneVertices r)
            (P.shift z x) (P.shift z y) := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_orbitBox_subset_rightHalfPlane (P.bufferedRadius N) r
  refine ⟨z, ?_⟩
  intro omega x y hxy
  have hsub : P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rightHalfPlaneVertices r := by
    rintro v ⟨u, hu, rfl⟩
    exact hz u hu
  apply P.connectedWithinSet_mono_region hsub (P.shift z x) (P.shift z y)
  apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
  exact hxy





def PeriodicPlaneEmbedding.halfPlanePairMergeError
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  ({omega | (P.cluster omega x).Infinite} ∩
    {omega | (P.cluster omega y).Infinite}) \
      P.connectedWithinSet (E.rightHalfPlaneVertices r) x y

theorem PeriodicPlaneEmbedding.halfPlanePairMergeError_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (x y : V) :
    MeasurableSet (E.halfPlanePairMergeError r x y) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinSet_measurableSet (E.rightHalfPlaneVertices r) x y)



theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_preimage_subset
    (E : PeriodicPlaneEmbedding P) (N : ℕ) (r : ℝ) (x y : V) :
    ∃ z : Site 2,
      P.configTranslate z ⁻¹'
          E.halfPlanePairMergeError r (P.shift z x) (P.shift z y) ⊆
        P.pairMergeError x y N := by
  obtain ⟨z, htransport⟩ :=
    E.exists_shift_connectedWithinOrbit_into_rightHalfPlane N r
  refine ⟨z, ?_⟩
  intro omega herror
  change P.configTranslate z omega ∈
    E.halfPlanePairMergeError r (P.shift z x) (P.shift z y) at herror
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (P.cluster_infinite_configTranslate z omega x).mp herror.1.1
  · exact (P.cluster_infinite_configTranslate z omega y).mp herror.1.2
  · intro hmerge
    exact herror.2 (htransport omega x y hmerge)



theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (N : ℕ) (r : ℝ) (x y : V) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) ≤
        mu.real (P.pairMergeError x y N) := by
  obtain ⟨z, hsub⟩ :=
    E.exists_shift_halfPlanePairMergeError_preimage_subset N r x y
  refine ⟨z, ?_⟩
  have hmeasure := P.translateEvent_measure_eq mu hTI z
    (E.halfPlanePairMergeError_measurableSet r (P.shift z x) (P.shift z y))
  have hreal :
      mu.real (P.configTranslate z ⁻¹'
        E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) =
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) :=
    congrArg ENNReal.toReal hmeasure
  rw [← hreal]
  exact measureReal_mono hsub



theorem PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : ℝ) (x y : V) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Site 2,
      mu.real (E.halfPlanePairMergeError r (P.shift z x) (P.shift z y)) < ε := by
  have ht := P.pairMergeError_real_tendsto_zero mu hunique x y
  have hev : ∀ᶠ N in atTop, mu.real (P.pairMergeError x y N) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeError_measureReal_le mu hTI N r x y
  exact ⟨z, hz.trans_lt hN⟩

end StatMech.FK.PeriodicPlanar
