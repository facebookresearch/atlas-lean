/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneEscape









open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



theorem PeriodicGraph.setConnectionWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A S T : Set V) :
    P.configTranslate z omega ∈
        P.setConnectionWithin (P.shift z '' A)
          (P.shift z '' S) (P.shift z '' T) ↔
      omega ∈ P.setConnectionWithin A S T := by
  constructor
  · rintro ⟨xz, ⟨x, hx, rfl⟩, yz, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, y, hy,
      (P.connectedWithinSet_configTranslate z omega A x y).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨P.shift z x, ⟨x, hx, rfl⟩,
      P.shift z y, ⟨y, hy, rfl⟩,
      (P.connectedWithinSet_configTranslate z omega A x y).mpr hxy⟩

theorem PeriodicGraph.setConnectionWithin_mono_target
    (P : PeriodicGraph V) (A S : Set V) {T U : Set V} (hTU : T ⊆ U) :
    P.setConnectionWithin A S T ⊆ P.setConnectionWithin A S U := by
  rintro omega ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hTU hy, hxy⟩


def verticalShift (t : Int) : Site 2 :=
  fun i => if i = 1 then t else 0

@[simp] theorem verticalShift_zero_apply (t : Int) :
    verticalShift t 0 = 0 := by
  simp [verticalShift]

@[simp] theorem verticalShift_one_apply (t : Int) :
    verticalShift t 1 = t := by
  simp [verticalShift]

theorem PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r : Real) (x : V) :
    P.shift (verticalShift t) x ∈ E.rightHalfPlaneVertices r ↔
      x ∈ E.rightHalfPlaneVertices r := by
  simp only [PeriodicPlaneEmbedding.rightHalfPlaneVertices, Set.mem_setOf_eq,
    E.vertexCoord_shift, verticalShift_zero_apply, Int.cast_zero, add_zero]

theorem PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r : Real) :
    P.shift (verticalShift t) '' E.rightHalfPlaneVertices r =
      E.rightHalfPlaneVertices r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (E.shift_mem_rightHalfPlaneVertices_vertical t r y).mpr hy
  · intro hx
    refine ⟨P.shift (-(verticalShift t)) x, ?_, ?_⟩
    · have hback : P.shift (verticalShift t)
          (P.shift (-(verticalShift t)) x) = x := by
        simpa using P.shift_shift_neg (verticalShift t) x
      have himage : P.shift (-(verticalShift t)) x ∈
          E.rightHalfPlaneVertices r := by
        rw [← hback] at hx
        exact (E.shift_mem_rightHalfPlaneVertices_vertical t r _).mp hx
      exact himage
    · simpa using P.shift_shift_neg (verticalShift t) x

theorem PeriodicPlaneEmbedding.shift_mem_rightHalfPlaneBoundaryVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r : Real) (x : V) :
    P.shift (verticalShift t) x ∈ E.rightHalfPlaneBoundaryVertices r ↔
      x ∈ E.rightHalfPlaneBoundaryVertices r := by
  constructor
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rightHalfPlaneVertices_vertical t r x).mp hx,
      P.shift (-(verticalShift t)) y, ?_, ?_⟩
    · have hadj := (P.shift_adj (-(verticalShift t))
        (P.shift (verticalShift t) x) y).mpr hxy
      simpa using hadj
    · have hy' : E.vertexCoord (P.shift (-(verticalShift t)) y) 0 =
          E.vertexCoord y 0 := by
        rw [E.vertexCoord_shift]
        simp [verticalShift]
      rwa [hy']
  · rintro ⟨hx, y, hxy, hy⟩
    refine ⟨(E.shift_mem_rightHalfPlaneVertices_vertical t r x).mpr hx,
      P.shift (verticalShift t) y, (P.shift_adj _ _ _).mpr hxy, ?_⟩
    rw [E.vertexCoord_shift]
    simpa [verticalShift] using hy

theorem PeriodicPlaneEmbedding.shift_image_rightHalfPlaneBoundaryVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r : Real) :
    P.shift (verticalShift t) '' E.rightHalfPlaneBoundaryVertices r =
      E.rightHalfPlaneBoundaryVertices r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r y).mpr hy
  · intro hx
    refine ⟨P.shift (-(verticalShift t)) x, ?_, ?_⟩
    · have hback : P.shift (verticalShift t)
          (P.shift (-(verticalShift t)) x) = x := by
        simpa using P.shift_shift_neg (verticalShift t) x
      rw [← hback] at hx
      exact (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r _).mp hx
    · simpa using P.shift_shift_neg (verticalShift t) x

theorem PeriodicPlaneEmbedding.shift_image_lowerBoundaryRayVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r s : Real) :
    P.shift (verticalShift t) '' E.lowerBoundaryRayVertices r s =
      E.lowerBoundaryRayVertices r (s + t) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyB, hyS⟩, rfl⟩
    refine ⟨(E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r y).mpr hyB, ?_⟩
    change E.vertexCoord (P.shift (verticalShift t) y) 1 ≤ s + (t : Real)
    change E.vertexCoord y 1 ≤ s at hyS
    rw [E.vertexCoord_shift]
    simp only [verticalShift_one_apply]
    linarith
  · rintro ⟨hxB, hxS⟩
    let y := P.shift (-(verticalShift t)) x
    have hxy : P.shift (verticalShift t) y = x := by
      dsimp only [y]
      simpa using P.shift_shift_neg (verticalShift t) x
    refine ⟨y, ⟨?_, ?_⟩, hxy⟩
    · rw [← hxy] at hxB
      exact (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r y).mp hxB
    · change E.vertexCoord x 1 ≤ s + (t : Real) at hxS
      rw [← hxy, E.vertexCoord_shift] at hxS
      simp only [verticalShift_one_apply] at hxS
      change E.vertexCoord y 1 ≤ s
      linarith

theorem PeriodicPlaneEmbedding.shift_image_upperBoundaryRayVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r s : Real) :
    P.shift (verticalShift t) '' E.upperBoundaryRayVertices r s =
      E.upperBoundaryRayVertices r (s + t) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyB, hyS⟩, rfl⟩
    refine ⟨(E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r y).mpr hyB, ?_⟩
    change s + (t : Real) ≤ E.vertexCoord (P.shift (verticalShift t) y) 1
    change s ≤ E.vertexCoord y 1 at hyS
    rw [E.vertexCoord_shift]
    simp only [verticalShift_one_apply]
    linarith
  · rintro ⟨hxB, hxS⟩
    let y := P.shift (-(verticalShift t)) x
    have hxy : P.shift (verticalShift t) y = x := by
      dsimp only [y]
      simpa using P.shift_shift_neg (verticalShift t) x
    refine ⟨y, ⟨?_, ?_⟩, hxy⟩
    · rw [← hxy] at hxB
      exact (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r y).mp hxB
    · change s + (t : Real) ≤ E.vertexCoord x 1 at hxS
      rw [← hxy, E.vertexCoord_shift] at hxS
      simp only [verticalShift_one_apply] at hxS
      change s ≤ E.vertexCoord y 1
      linarith

theorem PeriodicPlaneEmbedding.lowerBoundaryRay_connection_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n)) := by
  intro n N hnN
  apply P.setConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change E.vertexCoord y 1 ≤ (n : Real) at hy
  change E.vertexCoord y 1 ≤ (N : Real)
  exact hy.trans (by exact_mod_cast hnN)

theorem PeriodicPlaneEmbedding.iUnion_lowerBoundaryRay_connection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n)) =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    rcases hn with ⟨x, hx, y, ⟨hyB, _hy⟩, hxy⟩
    exact ⟨x, hx, y, hyB, hxy⟩
  · rintro ⟨x, hx, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord y 1)
    exact Set.mem_iUnion.2 ⟨n, x, hx, y, ⟨hyB, hn⟩, hxy⟩

theorem PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r n))) atTop
      (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.lowerBoundaryRay_connection_mono r S)
  rw [E.iUnion_lowerBoundaryRay_connection r S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure

theorem PeriodicPlaneEmbedding.upperBoundaryRay_connection_mono_neg
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Monotone (fun n : Nat =>
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real)))) := by
  intro n N hnN
  apply P.setConnectionWithin_mono_target
  rintro y ⟨hyB, hy⟩
  refine ⟨hyB, ?_⟩
  change -(n : Real) ≤ E.vertexCoord y 1 at hy
  change -(N : Real) ≤ E.vertexCoord y 1
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith

theorem PeriodicPlaneEmbedding.iUnion_upperBoundaryRay_connection_neg
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real)))) =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r) := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    rcases hn with ⟨x, hx, y, ⟨hyB, _hy⟩, hxy⟩
    exact ⟨x, hx, y, hyB, hxy⟩
  · rintro ⟨x, hx, y, hyB, hxy⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (-E.vertexCoord y 1)
    have hy : -(n : Real) ≤ E.vertexCoord y 1 := by linarith
    exact Set.mem_iUnion.2 ⟨n, x, hx, y, ⟨hyB, hy⟩, hxy⟩

theorem PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_tendsto_neg
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r (-(n : Real))))) atTop
      (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.upperBoundaryRay_connection_mono_neg r S)
  rw [E.iUnion_upperBoundaryRay_connection_neg r S] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure



theorem PeriodicPlaneEmbedding.lowerBoundaryRay_connection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int) (r s : Real) (S : Set V) :
    mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.lowerBoundaryRayVertices r (s + t))) =
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s)) := by
  let A := P.setConnectionWithin (E.rightHalfPlaneVertices r)
    (P.shift (verticalShift t) '' S)
    (E.lowerBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.lowerBoundaryRayVertices r s) := by
    ext omega
    change P.configTranslate (verticalShift t) omega ∈
        P.setConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift t) '' S)
          (E.lowerBoundaryRayVertices r (s + t)) ↔ _
    have h := P.setConnectionWithin_configTranslate (verticalShift t) omega
      (E.rightHalfPlaneVertices r) S (E.lowerBoundaryRayVertices r s)
    rw [E.shift_image_rightHalfPlaneVertices_vertical,
      E.shift_image_lowerBoundaryRayVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r)
      (P.shift (verticalShift t) '' S)
      (E.lowerBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm



theorem PeriodicPlaneEmbedding.upperBoundaryRay_connection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int) (r s : Real) (S : Set V) :
    mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift t) '' S)
        (E.upperBoundaryRayVertices r (s + t))) =
      mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s)) := by
  let A := P.setConnectionWithin (E.rightHalfPlaneVertices r)
    (P.shift (verticalShift t) '' S)
    (E.upperBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.upperBoundaryRayVertices r s) := by
    ext omega
    change P.configTranslate (verticalShift t) omega ∈
        P.setConnectionWithin (E.rightHalfPlaneVertices r)
          (P.shift (verticalShift t) '' S)
          (E.upperBoundaryRayVertices r (s + t)) ↔ _
    have h := P.setConnectionWithin_configTranslate (verticalShift t) omega
      (E.rightHalfPlaneVertices r) S (E.upperBoundaryRayVertices r s)
    rw [E.shift_image_rightHalfPlaneVertices_vertical,
      E.shift_image_upperBoundaryRayVertices_vertical] at h
    exact h
  have hm := (hTI (verticalShift t)).measure_preimage
    (P.setConnectionWithin_measurableSet (E.rightHalfPlaneVertices r)
      (P.shift (verticalShift t) '' S)
      (E.upperBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm



theorem PeriodicPlaneEmbedding.shift_down_lowerBoundaryRay_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.setConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (-(n : Int))) '' S)
        (E.lowerBoundaryRayVertices r 0))) atTop
      (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.lowerBoundaryRay_connection_measureReal_tendsto mu r S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.lowerBoundaryRay_connection_measureReal_vertical
    mu hTI (-(n : Int)) r (n : Real) S
  simpa using hmove.symm



theorem PeriodicPlaneEmbedding.shift_up_upperBoundaryRay_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) (S : Set V) :
    Tendsto (fun n : Nat => mu.real
      (P.setConnectionWithin (E.rightHalfPlaneVertices r)
        (P.shift (verticalShift (n : Int)) '' S)
        (E.upperBoundaryRayVertices r 0))) atTop
      (nhds (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S
        (E.rightHalfPlaneBoundaryVertices r)))) := by
  have hbase := E.upperBoundaryRay_connection_measureReal_tendsto_neg mu r S
  apply hbase.congr'
  filter_upwards with n
  have hmove := E.upperBoundaryRay_connection_measureReal_vertical
    mu hTI (n : Int) r (-(n : Real)) S
  simpa using hmove.symm

end StatMech.FK.PeriodicPlanar
