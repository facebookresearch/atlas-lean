/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic

/-!
# Connections inside a half-plane and merging of infinite clusters

Open connections constrained to a vertex set, the right half-plane and its boundary rays, and
the statement that two infinite clusters meet inside a half-plane after a suitable translation.

## i. Overview

`PeriodicGraph.connectedWithinSet A x y` is the event that an open path from `x` to `y` stays in
`A`; `setConnectionWithin A S T` asks for such a path from some vertex of `S` to some vertex of
`T`. Both are measurable, increasing and transform correctly under lattice translations.

For an embedding, the right half-plane `{x | r ≤ x₀}` has a boundary (half-plane vertices with
a neighbour to the left), split at height `s` into a lower and an upper boundary ray. With the
square-root trick, a likely connection to the whole boundary forces a likely connection to the
more probable of the two rays.

Translating a large box deep into the half-plane shows that, under translation invariance and
almost-sure uniqueness of the infinite cluster, two given vertices are, after a suitable
translation, either not both in infinite clusters or connected inside the half-plane, up to an
error smaller than any `ε > 0`.

## ii. Key results

- `PeriodicGraph.connectedWithinSet_measurableSet`, `connectedWithinSet_isIncreasing`,
  `connectedWithinSet_configTranslate` : unconditional.
- `directional_sqrt_trick`, `PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick` :
  conditional on `IsFKG mu`.
- `three_event_intersection_lower_bound` : the Bonferroni bound
  `μ A + μ B + μ C - 2 ≤ μ (A ∩ B ∩ C)` for a probability measure (unconditional).
- `PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_lt` : conditional on
  translation invariance and almost-sure uniqueness of the infinite cluster.

## iii. Table of contents

- A. Connections inside a vertex set
- B. The square-root trick with a preferred event
- C. The right half-plane and its boundary rays
- D. Merging infinite clusters inside a half-plane

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

/-! ## A. Connections inside a vertex set -/

/-- The event that an open path from `x` to `y` stays inside the vertex set `A`. See also
`PeriodicGraph.connectedWithinOrbit`, the case of an orbit box. -/
def PeriodicGraph.connectedWithinSet
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ l : List V,
    List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
    (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
    ∀ v ∈ x :: l, v ∈ A}

lemma PeriodicGraph.connectedWithinSet_measurableSet
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
    simp only [PeriodicGraph.connectedWithinSet, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨l, hchain, hlast, hA⟩
      refine ⟨l, ?_⟩
      rw [ite_eq_left ⟨hlast, hA⟩]
      exact hchain
    · rintro ⟨l, hl⟩
      split_ifs at hl with h
      · exact ⟨l, hl, h.1, h.2⟩
      · exact False.elim (by simp at hl)
  rw [heq]
  exact MeasurableSet.iUnion fun l => by
    split_ifs
    · exact P.measurableSet_openChain (x :: l)
    · exact MeasurableSet.empty

omit [Countable V] in
lemma PeriodicGraph.connectedWithinSet_isIncreasing
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    IsIncreasing (P.connectedWithinSet A x y) := by
  intro omega eta home
  rintro ⟨l, hchain, hlast, hA⟩
  refine ⟨l, hchain.imp ?_, hlast, hA⟩
  intro a b hab
  rw [P.openSubgraph_adj] at hab ⊢
  refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hab.2] using home s(a, b)

omit [Countable V] in
lemma PeriodicGraph.connectedWithinSet_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (x y : V) :
    P.connectedWithinSet A x y ⊆ P.connectedWithinSet B x y := by
  rintro omega ⟨l, hchain, hlast, hA⟩
  exact ⟨l, hchain, hlast, fun v hv => hAB (hA v hv)⟩

omit [Countable V] in
lemma PeriodicGraph.connectedWithinSet_configTranslate
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

/-- The event that some vertex of `S` is joined to some vertex of `T` by an open path inside `A`. -/
def PeriodicGraph.setConnectionWithin
    (P : PeriodicGraph V) (A S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, ∃ y ∈ T, omega ∈ P.connectedWithinSet A x y}

lemma PeriodicGraph.setConnectionWithin_measurableSet
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

omit [Countable V] in
lemma PeriodicGraph.setConnectionWithin_isIncreasing
    (P : PeriodicGraph V) (A S T : Set V) :
    IsIncreasing (P.setConnectionWithin A S T) := by
  intro omega eta home
  rintro ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy,
    P.connectedWithinSet_isIncreasing A x y home hxy⟩

omit [Countable V] in
lemma PeriodicGraph.setConnectionWithin_union_target
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

/-! ## B. The square-root trick with a preferred event -/

omit [DecidableEq V] [Countable V] in
/-- Square-root trick with a preferred event: if `μ B ≤ μ A` for increasing `A`, `B` under an FKG
measure, then `1 - √(1 - μ(A ∪ B)) ≤ μ A`. See also `StatMech.Universality.rsw_sqrt_trick_eq`
(equal probabilities, positive association). -/
lemma directional_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hBA : mu.real B ≤ mu.real A) :
    1 - Real.sqrt (1 - mu.real (A ∪ B)) ≤ mu.real A := by
  have h := measurable_sqrt_trick mu hFKG hA hB hAm hBm
  rwa [max_eq_left hBA] at h

omit [DecidableEq V] [Countable V] in
/-- Bonferroni lower bound for three events: `μ A + μ B + μ C - 2 ≤ μ (A ∩ B ∩ C)`. -/
lemma three_event_intersection_lower_bound
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

/-! ## C. The right half-plane and its boundary rays -/

/-- The vertices in the closed right half-plane `{x | r ≤ x₀}`. -/
def PeriodicPlaneEmbedding.rightHalfPlaneVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | r ≤ E.vertexCoord x 0}

/-- The boundary of the right half-plane: its vertices with a neighbour strictly left of `r`. -/
def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryVertices
    (E : PeriodicPlaneEmbedding P) (r : ℝ) : Set V :=
  {x | x ∈ E.rightHalfPlaneVertices r ∧
    ∃ y, P.graph.Adj x y ∧ E.vertexCoord y 0 < r}

/-- The lower boundary ray: boundary vertices of the right half-plane at height at most `s`. -/
def PeriodicPlaneEmbedding.lowerBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | E.vertexCoord x 1 ≤ s}

/-- The upper boundary ray: boundary vertices of the right half-plane at height at least `s`. -/
def PeriodicPlaneEmbedding.upperBoundaryRayVertices
    (E : PeriodicPlaneEmbedding P) (r s : ℝ) : Set V :=
  E.rightHalfPlaneBoundaryVertices r ∩ {x | s ≤ E.vertexCoord x 1}

omit [Countable V] in
lemma PeriodicPlaneEmbedding.boundary_eq_lower_union_upper
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

omit [Countable V] in
lemma PeriodicPlaneEmbedding.rightHalfPlaneBoundary_coord_lt
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

/-- If connecting `S` to the lower boundary ray is at least as likely as connecting it to the upper
ray, the square-root trick bounds the lower-ray probability below by that of the whole boundary
(under FKG). -/
lemma PeriodicPlaneEmbedding.lowerBoundaryRay_directional_sqrt_trick
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

/-! ## D. Merging infinite clusters inside a half-plane -/

omit [Countable V] in
lemma PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_rightHalfPlane
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

omit [Countable V] in
lemma PeriodicPlaneEmbedding.exists_shift_connectedWithinOrbit_into_rightHalfPlane
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

/-- `x` and `y` both lie in infinite clusters but are not connected inside the right half-plane
`{r ≤ x₀}`. See also `PeriodicGraph.pairMergeError`, the same event for an orbit box. -/
def PeriodicPlaneEmbedding.halfPlanePairMergeError
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  ({omega | (P.cluster omega x).Infinite} ∩
    {omega | (P.cluster omega y).Infinite}) \
      P.connectedWithinSet (E.rightHalfPlaneVertices r) x y

lemma PeriodicPlaneEmbedding.halfPlanePairMergeError_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : ℝ) (x y : V) :
    MeasurableSet (E.halfPlanePairMergeError r x y) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinSet_measurableSet (E.rightHalfPlaneVertices r) x y)

omit [Countable V] in
lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_preimage_subset
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

lemma PeriodicPlaneEmbedding.exists_shift_halfPlanePairMergeError_measureReal_le
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

/-- Under translation invariance and almost-sure uniqueness of the infinite cluster, for every
`ε > 0` some translate of `x`, `y` has half-plane merging error below `ε`. -/
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
