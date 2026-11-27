/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableList

@[expose] public section

/-! # Measurable sPRM and PRM* roadmaps

This file proves that the sPRM and PRM* vertex and edge lists are measurable
functions of the explicit finite sample list, and that they ignore samples
that are not collision free.

Model: planners are deterministic functions of the sample list. At each step
they keep the subsample filtered by the collision test `O.free`; PRM* reads
its radius from the filtered count. Oracles are jointly measurable, `Bool`,
`ℕ`, `ℤ`, `ℚ` carry discrete σ-algebras, and finite lists carry the
length-stratified σ-algebra.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- Filtering samples by a measurable freeness test is measurable. -/
private theorem measurable_filterFree {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun samples : List C => samples.filter O.free) := by
  have hq : Measurable (fun p : Unit × C => O.free p.2) :=
    hO.free.comp measurable_snd
  have h := measurable_list_filter (q := fun p : Unit × C => O.free p.2) hq
  have hPair : Measurable (fun samples : List C => ((), samples)) :=
    measurable_const.prodMk measurable_id
  have hComp := h.comp hPair
  simpa [Function.comp_def] using hComp

/-- sPRM vertices are a measurable function of the sample list. -/
theorem measurable_sprmVertices {C : Type} [DecidableEq C] [MeasurableSpace C] [MeasurableEq C]
    {O : Oracles C} (hO : OraclesMeasurable O) (start : C) :
    Measurable (sprmVertices O start) := by
  have hFilt := measurable_filterFree (O := O) hO
  have hPair : Measurable (fun samples : List C => (start, samples.filter O.free)) :=
    measurable_const.prodMk hFilt
  have hCons : Measurable (fun samples : List C => start :: samples.filter O.free) := by
    have h := measurable_list_cons (α := C).comp hPair
    simpa [Function.comp_def] using h
  have hDedup := measurable_list_dedup (α := C)
  have hComp : Measurable (fun samples : List C => (start :: samples.filter O.free).dedup) := by
    have h := hDedup.comp hCons
    simpa [Function.comp_def] using h
  have hEq : sprmVertices O start =
      fun samples : List C => (start :: samples.filter O.free).dedup := rfl
  rw [hEq]
  exact hComp

/-- A decidable measurable proposition gives a measurable Boolean test. -/
private theorem measurable_decide_of_prop {α : Type*} [MeasurableSpace α]
    {P : α → Prop} [DecidablePred P] (hP : Measurable P) :
    Measurable (fun a => decide (P a)) := by
  apply measurable_to_bool
  have hSet : MeasurableSet (P ⁻¹' {True}) := hP (MeasurableSet.singleton True)
  have hEq : (fun a => decide (P a)) ⁻¹' {true} = P ⁻¹' {True} := by
    ext a
    simp
  rw [hEq]
  exact hSet

/-- The sPRM edge proposition is measurable. -/
private theorem measurable_isSprmEdge_prop {C : Type} [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun p : C × C => IsSprmEdge O p.1 p.2) := by
  have hNe : Measurable (fun p : C × C => p.1 ≠ p.2) :=
    (Measurable.eq measurable_fst measurable_snd).not
  have hLe1 : Measurable (fun p : C × C => O.cost p.1 p.2 ≤ O.radius) := by
    apply measurable_to_prop
    have hEq : (fun p : C × C => O.cost p.1 p.2 ≤ O.radius) ⁻¹' {True} =
        (fun p : C × C => O.cost p.1 p.2) ⁻¹' {q : ℚ | q ≤ O.radius} := by
      ext a
      simp
    rw [hEq]
    exact MeasurableSet.preimage MeasurableSet.of_discrete hO.cost
  have hCostSwap : Measurable (fun p : C × C => O.cost p.2 p.1) := by
    have h := hO.cost.comp measurable_swap
    simpa [Function.comp_def, Prod.swap] using h
  have hLe2 : Measurable (fun p : C × C => O.cost p.2 p.1 ≤ O.radius) := by
    apply measurable_to_prop
    have hEq : (fun p : C × C => O.cost p.2 p.1 ≤ O.radius) ⁻¹' {True} =
        (fun p : C × C => O.cost p.2 p.1) ⁻¹' {q : ℚ | q ≤ O.radius} := by
      ext a
      simp
    rw [hEq]
    exact MeasurableSet.preimage MeasurableSet.of_discrete hCostSwap
  have hLink1 : Measurable (fun p : C × C => O.link p.1 p.2 = true) := by
    apply measurable_to_prop
    have hEq : (fun p : C × C => O.link p.1 p.2 = true) ⁻¹' {True} =
        (fun p : C × C => O.link p.1 p.2) ⁻¹' {true} := by
      ext a
      simp
    rw [hEq]
    exact MeasurableSet.preimage (MeasurableSet.singleton true) hO.link
  have hLinkSwap : Measurable (fun p : C × C => O.link p.2 p.1) := by
    have h := hO.link.comp measurable_swap
    simpa [Function.comp_def, Prod.swap] using h
  have hLink2 : Measurable (fun p : C × C => O.link p.2 p.1 = true) := by
    apply measurable_to_prop
    have hEq : (fun p : C × C => O.link p.2 p.1 = true) ⁻¹' {True} =
        (fun p : C × C => O.link p.2 p.1) ⁻¹' {true} := by
      ext a
      simp
    rw [hEq]
    exact MeasurableSet.preimage (MeasurableSet.singleton true) hLinkSwap
  have h := hNe.and (hLe1.and (hLe2.and (hLink1.and hLink2)))
  exact h

/-- The sPRM edge test is measurable. -/
private theorem measurable_edgeCond {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun p : C × C => edgeCond O p.1 p.2) := by
  have hProp := measurable_isSprmEdge_prop (O := O) hO
  have hDec := measurable_decide_of_prop (P := fun p : C × C => IsSprmEdge O p.1 p.2) hProp
  have hEq : (fun p : C × C => edgeCond O p.1 p.2) =
      fun p : C × C => decide (IsSprmEdge O p.1 p.2) := rfl
  rw [hEq]
  exact hDec

/-- Pairing one vertex with its forward neighbors is measurable. -/
private theorem measurable_pairsWith {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun p : C × List C => pairsWith O p.1 p.2) := by
  have hQ : Measurable (fun r : C × C => edgeCond O r.1 r.2) :=
    measurable_edgeCond (O := O) hO
  have hFilt : Measurable
      (fun p : C × List C => p.2.filter (fun v => edgeCond O p.1 v)) := by
    have h := measurable_list_filter
      (q := fun r : C × C => edgeCond O r.1 r.2) hQ
    simpa using h
  have hf : Measurable (fun r : C × C => (r.1, r.2)) :=
    measurable_fst.prodMk measurable_snd
  have hMap : Measurable (fun q : C × List C => q.2.map (fun v => (q.1, v))) := by
    have h := measurable_list_map (f := fun r : C × C => (r.1, r.2)) hf
    simpa using h
  have hPair : Measurable
      (fun p : C × List C => (p.1, p.2.filter (fun v => edgeCond O p.1 v))) :=
    measurable_fst.prodMk hFilt
  have hComp := hMap.comp hPair
  have hEq : (fun p : C × List C => pairsWith O p.1 p.2) =
      fun p : C × List C =>
        (p.2.filter (fun v => edgeCond O p.1 v)).map (fun v => (p.1, v)) := rfl
  rw [hEq]
  simpa [Function.comp_def] using hComp

/-- All forward pairs are measurable. -/
private theorem measurable_allPairs {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (allPairs O) := by
  have hPairs := measurable_pairsWith (O := O) hO
  have hUV : Measurable
      (fun p : Unit × C × List C × List (C × C) => (p.2.1, p.2.2.1)) := by
    have hId : Measurable (fun p : Unit × C × List C × List (C × C) => p) :=
      measurable_id
    have hSnd := hId.snd
    have h1 : Measurable
        (fun p : Unit × C × List C × List (C × C) => p.2.1) := by
      have h := hSnd.fst
      simpa using h
    have hSnd2 := hSnd.snd
    have h2 : Measurable
        (fun p : Unit × C × List C × List (C × C) => p.2.2.1) := by
      have h := hSnd2.fst
      simpa using h
    exact h1.prodMk h2
  have hHead : Measurable
      (fun p : Unit × C × List C × List (C × C) =>
        pairsWith O p.2.1 p.2.2.1) := by
    have h := hPairs.comp hUV
    simpa [Function.comp_def] using h
  have hTail : Measurable
      (fun p : Unit × C × List C × List (C × C) => p.2.2.2) := by
    have hId : Measurable (fun p : Unit × C × List C × List (C × C) => p) :=
      measurable_id
    have h := hId.snd.snd.snd
    simpa using h
  have hCons : Measurable
      (fun p : Unit × C × List C × List (C × C) =>
        pairsWith O p.2.1 p.2.2.1 ++ p.2.2.2) := by
    have h := measurable_list_append (α := C × C).comp (hHead.prodMk hTail)
    simpa [Function.comp_def] using h
  have hNil : Measurable (fun _ : Unit => ([] : List (C × C))) :=
    measurable_const
  have hRec := measurable_list_rec (nil := fun _ : Unit => ([] : List (C × C)))
    (cons := fun p : Unit × C × List C × List (C × C) =>
      pairsWith O p.2.1 p.2.2.1 ++ p.2.2.2) hNil hCons
  have hPair : Measurable (fun verts : List C => ((), verts)) :=
    measurable_const.prodMk measurable_id
  have hComp := hRec.comp hPair
  have hEq : allPairs O = fun verts : List C =>
      List.rec (motive := fun _ => List (C × C)) []
        (fun a l ih => pairsWith O a l ++ ih) verts := by
    funext verts
    induction verts with
    | nil => rfl
    | cons u vs ih => simp [allPairs, ih]
  rw [hEq]
  simpa [Function.comp_def] using hComp

/-- Appending reversed edges is measurable. -/
private theorem measurable_withReversals {C : Type} [MeasurableSpace C] :
    Measurable (withReversals (C := C)) := by
  have hf : Measurable (fun r : Unit × (C × C) => r.2.swap) :=
    measurable_swap.comp measurable_snd
  have hMapUnit := measurable_list_map
    (f := fun r : Unit × (C × C) => r.2.swap) hf
  have hPair : Measurable (fun edges : List (C × C) => ((), edges)) :=
    measurable_const.prodMk measurable_id
  have hSwapMap : Measurable (fun edges : List (C × C) => edges.map Prod.swap) := by
    have h := hMapUnit.comp hPair
    simpa [Function.comp_def] using h
  have hApp := measurable_list_append (α := C × C).comp
    (measurable_id.prodMk hSwapMap)
  have hEq : withReversals (C := C) =
      fun edges : List (C × C) => edges ++ edges.map Prod.swap := rfl
  rw [hEq]
  simpa [Function.comp_def] using hApp

/-- sPRM edges are a measurable function of the sample list. -/
theorem measurable_sprmEdges {C : Type} [DecidableEq C] [MeasurableSpace C] [MeasurableEq C]
    {O : Oracles C} (hO : OraclesMeasurable O) (start : C) :
    Measurable (sprmEdges O start) := by
  have hVerts := measurable_sprmVertices (O := O) hO start
  have hPairs := measurable_allPairs (O := O) hO
  have hRev := measurable_withReversals (C := C)
  have hComp1 := hPairs.comp hVerts
  have hComp2 := hRev.comp hComp1
  have hEq : sprmEdges O start =
      withReversals ∘ allPairs O ∘ sprmVertices O start := rfl
  rw [hEq]
  exact hComp2

/-- PRM* vertices are a measurable function of the sample list. -/
theorem measurable_prmStarVertices {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) :
    Measurable (prmStarVertices O start) := by
  have h := measurable_sprmVertices (O := O) hO start
  have hEq : prmStarVertices O start = sprmVertices O start := rfl
  rw [hEq]
  exact h

/-- Updating the radius preserves oracle measurability. -/
private theorem oraclesMeasurable_with_radius {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) (r : Rat) :
    OraclesMeasurable { O with radius := r } :=
  ⟨hO.free, hO.link, hO.steer, hO.cost⟩

/-- The filtered-sample count is measurable. -/
private theorem measurable_filterLength {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun samples : List C => (samples.filter O.free).length) := by
  have hFilt := measurable_filterFree (O := O) hO
  have hLen := measurable_list_length (α := C)
  have h := hLen.comp hFilt
  simpa [Function.comp_def] using h

/-- PRM* edges are a measurable function of the sample list, for any radius schedule. -/
theorem measurable_prmStarEdges {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : C) : Measurable (prmStarEdges O radiusOf start) := by
  have hF : Measurable
      (fun p : ℕ × List C =>
        withReversals (allPairs { O with radius := radiusOf p.1 } p.2)) := by
    apply measurable_from_prod_countable_right
    intro n
    have hOn := oraclesMeasurable_with_radius (O := O) hO (radiusOf n)
    have hPairs := measurable_allPairs (O := { O with radius := radiusOf n }) hOn
    have hRev := measurable_withReversals (C := C)
    have h := hRev.comp hPairs
    have hEq : (fun verts : List C =>
            withReversals (allPairs { O with radius := radiusOf n } verts)) =
        withReversals ∘ allPairs { O with radius := radiusOf n } := rfl
    rw [hEq]
    exact h
  have hLen := measurable_filterLength (O := O) hO
  have hVerts := measurable_prmStarVertices (O := O) hO start
  have hPair : Measurable (fun samples : List C =>
      ((samples.filter O.free).length, prmStarVertices O start samples)) :=
    hLen.prodMk hVerts
  have hComp := hF.comp hPair
  have hEq : prmStarEdges O radiusOf start =
      (fun p : ℕ × List C =>
        withReversals (allPairs { O with radius := radiusOf p.1 } p.2)) ∘
      (fun samples : List C =>
        ((samples.filter O.free).length,
          prmStarVertices O start samples)) := rfl
  rw [hEq]
  exact hComp

/-- Filtering twice by freeness is the same as filtering once. -/
private theorem filter_free_idem {C : Type} (O : Oracles C) (samples : List C) :
    (samples.filter O.free).filter O.free = samples.filter O.free := by
  rw [List.filter_filter]
  have hEq : (fun a : C => O.free a && O.free a) = O.free := by
    funext a
    exact Bool.and_self _
  rw [hEq]

/-- sPRM vertices ignore samples that are not collision free. -/
theorem sprmVertices_filter_free {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    sprmVertices O start (samples.filter O.free) = sprmVertices O start samples := by
  unfold sprmVertices
  rw [filter_free_idem]

/-- sPRM edges ignore samples that are not collision free. -/
theorem sprmEdges_filter_free {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    sprmEdges O start (samples.filter O.free) = sprmEdges O start samples := by
  unfold sprmEdges
  rw [sprmVertices_filter_free]

/-- PRM* vertices ignore samples that are not collision free. -/
theorem prmStarVertices_filter_free {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    prmStarVertices O start (samples.filter O.free) = prmStarVertices O start samples := by
  unfold prmStarVertices
  rw [sprmVertices_filter_free]

/-- PRM* edges ignore samples that are not collision free; the radius schedule already
reads the filtered count. -/
theorem prmStarEdges_filter_free {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : ℕ → ℚ) (start : C) (samples : List C) :
    prmStarEdges O radiusOf start (samples.filter O.free) =
      prmStarEdges O radiusOf start samples := by
  unfold prmStarEdges
  rw [filter_free_idem, prmStarVertices_filter_free]

end Cslib.Planning.MotionPlanning.SamplingPlanners
