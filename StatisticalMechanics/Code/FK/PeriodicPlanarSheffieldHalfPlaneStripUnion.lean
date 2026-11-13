/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneMerge
import Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}



def PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  ⋃ p : ↥(L.product R),
    E.halfPlaneStripPairMergeError r n p.1.1 p.1.2

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat)
    (L R : Finset V) :
    MeasurableSet (E.halfPlaneStripPairMergeErrorUnion r n L R) :=
  MeasurableSet.iUnion fun p =>
    E.halfPlaneStripPairMergeError_measurableSet r n p.1.1 p.1.2

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_antitone
    (E : PeriodicPlaneEmbedding P) (r : Real) (L R : Finset V) :
    Antitone (fun n => E.halfPlaneStripPairMergeErrorUnion r n L R) := by
  intro n N hnN omega homega
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp homega
  exact Set.mem_iUnion.2
    ⟨p, E.halfPlaneStripPairMergeError_antitone r p.1.1 p.1.2 hnN hp⟩

theorem PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion_eq_product
    (E : PeriodicPlaneEmbedding P) (r : Real) (L R : Finset V) :
    E.halfPlanePairMergeErrorUnion r L R =
      ⋃ p : ↥(L.product R), E.halfPlanePairMergeError r p.1.1 p.1.2 := by
  ext omega
  simp only [PeriodicPlaneEmbedding.halfPlanePairMergeErrorUnion,
    Set.mem_iUnion]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩⟩, hxy⟩
  · rintro ⟨⟨⟨x, y⟩, hxy⟩, homega⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    exact ⟨x, hx, y, hy, homega⟩

theorem PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (r : Real) (L R : Finset V) :
    (⋂ n : Nat, E.halfPlaneStripPairMergeErrorUnion r n L R) =
      E.halfPlanePairMergeErrorUnion r L R := by
  rw [E.halfPlanePairMergeErrorUnion_eq_product]
  change (⋂ n : Nat, ⋃ p : ↥(L.product R),
      E.halfPlaneStripPairMergeError r n p.1.1 p.1.2) = _
  rw [iInter_iUnion_of_antitone]
  · congr 1
    funext p
    exact E.iInter_halfPlaneStripPairMergeError r p.1.1 p.1.2
  · intro p
    exact E.halfPlaneStripPairMergeError_antitone r p.1.1 p.1.2

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (L R : Finset V) :
    Tendsto (fun n => mu.real
      (E.halfPlaneStripPairMergeErrorUnion r n L R)) atTop
      (nhds (mu.real (E.halfPlanePairMergeErrorUnion r L R))) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (E.halfPlaneStripPairMergeErrorUnion r n L R)) atTop
      (nhds (mu (⋂ n : Nat,
        E.halfPlaneStripPairMergeErrorUnion r n L R))) :=
    tendsto_measure_iInter_atTop
      (fun n =>
        (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n L R).nullMeasurableSet)
      (E.halfPlaneStripPairMergeErrorUnion_antitone r L R)
      ⟨0, measure_ne_top mu _⟩
  rw [E.iInter_halfPlaneStripPairMergeErrorUnion r L R] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure



theorem PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (L R : Finset V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (R.image (P.shift z))) < epsilon := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeErrorUnion_measureReal_lt
      mu hTI hunique r L R (half_pos hepsilon)
  have ht := E.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto
    mu r (L.image (P.shift z)) (R.image (P.shift z))
  have hev : ∀ᶠ n in atTop,
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (R.image (P.shift z))) < epsilon :=
    (tendsto_order.1 ht).2 epsilon (hz.trans (half_lt_self hepsilon))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨z, n, hn⟩



theorem PeriodicPlaneEmbedding.shift_image_rightHalfPlaneStripVertices_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int) (r : Real) (n : Nat) :
    P.shift (verticalShift t) '' E.rightHalfPlaneStripVertices r n =
      E.rightHalfPlaneStripVertices r n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(E.shift_mem_rightHalfPlaneVertices_vertical t r y).mpr hy.1, ?_⟩
    change E.vertexCoord (P.shift (verticalShift t) y) 0 ≤ r + (n : Real)
    rw [E.vertexCoord_shift]
    simpa using hy.2
  · intro hx
    let y := P.shift (-(verticalShift t)) x
    have hxy : P.shift (verticalShift t) y = x := by
      simpa [y] using P.shift_shift_neg (verticalShift t) x
    refine ⟨y, ?_, hxy⟩
    rw [← hxy] at hx
    change P.shift (verticalShift t) y ∈ E.rightHalfPlaneVertices r ∧
      E.vertexCoord (P.shift (verticalShift t) y) 0 ≤ r + (n : Real) at hx
    refine ⟨(E.shift_mem_rightHalfPlaneVertices_vertical t r y).mp hx.1, ?_⟩
    change E.vertexCoord y 0 ≤ r + (n : Real)
    rw [E.vertexCoord_shift] at hx
    simpa using hx.2

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_configTranslate_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int)
    (omega : ConfigSpace (Sym2 V)) (r : Real) (n : Nat) (x y : V) :
    P.configTranslate (verticalShift t) omega ∈
        E.halfPlaneStripPairMergeError r n
          (P.shift (verticalShift t) x) (P.shift (verticalShift t) y) ↔
      omega ∈ E.halfPlaneStripPairMergeError r n x y := by
  simp only [PeriodicPlaneEmbedding.halfPlaneStripPairMergeError,
    Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [P.cluster_infinite_configTranslate, P.cluster_infinite_configTranslate]
  have hconn := P.connectedWithinSet_configTranslate (verticalShift t) omega
    (E.rightHalfPlaneStripVertices r n) x y
  rw [E.shift_image_rightHalfPlaneStripVertices_vertical] at hconn
  exact and_congr_right fun _ => not_congr hconn

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_configTranslate_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int)
    (omega : ConfigSpace (Sym2 V)) (r : Real) (n : Nat)
    (L R : Finset V) :
    P.configTranslate (verticalShift t) omega ∈
        E.halfPlaneStripPairMergeErrorUnion r n
          (L.image (P.shift (verticalShift t)))
          (R.image (P.shift (verticalShift t))) ↔
      omega ∈ E.halfPlaneStripPairMergeErrorUnion r n L R := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
    rcases p with ⟨⟨px, py⟩, hpMem⟩
    obtain ⟨hpxMem, hpyMem⟩ := Finset.mem_product.mp hpMem
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpxMem
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hpyMem
    apply Set.mem_iUnion.2
    refine ⟨⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩⟩, ?_⟩
    exact (E.halfPlaneStripPairMergeError_configTranslate_vertical
      t omega r n x y).mp hp
  · intro h
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
    rcases p with ⟨⟨x, y⟩, hpMem⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpMem
    apply Set.mem_iUnion.2
    let pt : V × V :=
      (P.shift (verticalShift t) x, P.shift (verticalShift t) y)
    have hpt : pt ∈
        (L.image (P.shift (verticalShift t))).product
          (R.image (P.shift (verticalShift t))) := by
      apply Finset.mem_product.2
      exact ⟨Finset.mem_image.2 ⟨x, hx, rfl⟩,
        Finset.mem_image.2 ⟨y, hy, rfl⟩⟩
    refine ⟨⟨pt, hpt⟩, ?_⟩
    exact (E.halfPlaneStripPairMergeError_configTranslate_vertical
      t omega r n x y).mpr hp

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r : Real) (n : Nat) (L R : Finset V) :
    mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift (verticalShift t)))
        (R.image (P.shift (verticalShift t)))) =
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R) := by
  let C := E.halfPlaneStripPairMergeErrorUnion r n
    (L.image (P.shift (verticalShift t)))
    (R.image (P.shift (verticalShift t)))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' C =
      E.halfPlaneStripPairMergeErrorUnion r n L R := by
    ext omega
    exact E.halfPlaneStripPairMergeErrorUnion_configTranslate_vertical
      t omega r n L R
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n
      (L.image (P.shift (verticalShift t)))
      (R.image (P.shift (verticalShift t)))).nullMeasurableSet
  change mu.real C = _
  rw [hpre] at hm
  exact congrArg ENNReal.toReal hm.symm



theorem PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_sources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (L R : Finset V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧
      (R.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (R.image (P.shift z))) < epsilon := by
  obtain ⟨M, hM⟩ := P.finite_subset_orbitBox (L ∪ R)
  have ht := P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R
  have herr : ∀ᶠ N in atTop,
      mu.real (P.pairMergeErrorUnion L R N) < epsilon / 2 :=
    (tendsto_order.1 ht).2 (epsilon / 2) (half_pos hepsilon)
  have hboth : ∀ᶠ N in atTop, M ≤ N ∧
      mu.real (P.pairMergeErrorUnion L R N) < epsilon / 2 := by
    filter_upwards [eventually_ge_atTop M, herr] with N hMN hN
    exact ⟨hMN, hN⟩
  obtain ⟨N, hMN, hNerror⟩ := hboth.exists
  have hLR : ∀ v ∈ L ∪ R, v ∈ P.orbitBox (P.bufferedRadius N) := by
    intro v hv
    exact P.orbitBox_mono
      (hMN.trans (P.id_le_bufferedRadius N)) (hM v hv)
  obtain ⟨z, hLH, hRH, hz⟩ :=
    E.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_sources
      mu hTI N r L R hLR
  have hhalf : mu.real (E.halfPlanePairMergeErrorUnion r
      (L.image (P.shift z)) (R.image (P.shift z))) < epsilon / 2 :=
    hz.trans_lt hNerror
  have hstrip := E.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto
    mu r (L.image (P.shift z)) (R.image (P.shift z))
  have hev : ∀ᶠ n in atTop,
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (R.image (P.shift z))) < epsilon :=
    (tendsto_order.1 hstrip).2 epsilon
      (hhalf.trans (half_lt_self hepsilon))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨z, n, hLH, hRH, hn⟩



theorem PeriodicPlaneEmbedding.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (L Rset : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (Rset.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (Rset.image (P.shift z))) < epsilon := by
  obtain ⟨M, hM⟩ := P.finite_subset_orbitBox (L ∪ Rset)
  have ht := P.pairMergeErrorUnion_real_tendsto_zero mu hunique L Rset
  have herr : ∀ᶠ N in atTop,
      mu.real (P.pairMergeErrorUnion L Rset N) < epsilon / 2 :=
    (tendsto_order.1 ht).2 (epsilon / 2) (half_pos hepsilon)
  have hboth : ∀ᶠ N in atTop, M ≤ N ∧
      mu.real (P.pairMergeErrorUnion L Rset N) < epsilon / 2 := by
    filter_upwards [eventually_ge_atTop M, herr] with N hMN hN
    exact ⟨hMN, hN⟩
  obtain ⟨N, hMN, hNerror⟩ := hboth.exists
  have hLR : ∀ v ∈ L ∪ Rset,
      v ∈ P.orbitBox (P.bufferedRadius N) := by
    intro v hv
    exact P.orbitBox_mono
      (hMN.trans (P.id_le_bufferedRadius N)) (hM v hv)
  obtain ⟨z, hLH, hRH, hz⟩ :=
    E.exists_shift_halfPlanePairMergeErrorUnion_measureReal_le_with_margin
      mu hTI N hrR L Rset hLR
  have hhalf : mu.real (E.halfPlanePairMergeErrorUnion r
      (L.image (P.shift z)) (Rset.image (P.shift z))) < epsilon / 2 :=
    hz.trans_lt hNerror
  have hstrip := E.halfPlaneStripPairMergeErrorUnion_measureReal_tendsto
    mu r (L.image (P.shift z)) (Rset.image (P.shift z))
  have hev : ∀ᶠ n in atTop,
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z)) (Rset.image (P.shift z))) < epsilon :=
    (tendsto_order.1 hstrip).2 epsilon
      (hhalf.trans (half_lt_self hepsilon))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨z, n, hLH, hRH, hn⟩



theorem PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (L : Finset V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices r ∧
      ((L.image (P.shift z)).image (P.shift (verticalShift 1)) : Set V) ⊆
        E.rightHalfPlaneVertices r ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z))
        ((L.image (P.shift z)).image (P.shift (verticalShift 1)))) < epsilon := by
  let R := L.image (P.shift (verticalShift 1))
  obtain ⟨z, n, hL, hR, herror⟩ :=
    E.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_sources
      mu hTI hunique r L R hepsilon
  have hcomm : R.image (P.shift z) =
      (L.image (P.shift z)).image (P.shift (verticalShift 1)) := by
    ext y
    simp only [R, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift z u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift 1) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  rw [hcomm] at hR herror
  exact ⟨z, n, hL, hR, herror⟩



theorem PeriodicPlaneEmbedding.exists_inward_adjacent_stripPlacement_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (L : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      ((L.image (P.shift z)).image (P.shift (verticalShift 1)) : Set V) ⊆
        E.rightHalfPlaneVertices R ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z))
        ((L.image (P.shift z)).image (P.shift (verticalShift 1)))) < epsilon := by
  let Rset := L.image (P.shift (verticalShift 1))
  obtain ⟨z, n, hL, hR, herror⟩ :=
    E.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin
      mu hTI hunique hrR L Rset hepsilon
  have hcomm : Rset.image (P.shift z) =
      (L.image (P.shift z)).image (P.shift (verticalShift 1)) := by
    ext y
    simp only [Rset, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift z u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift 1) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  rw [hcomm] at hR herror
  exact ⟨z, n, hL, hR, herror⟩



theorem PeriodicPlaneEmbedding.exists_inward_twoStep_stripPlacement_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (L : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      ((L.image (P.shift z)).image (P.shift (verticalShift 2)) : Set V) ⊆
        E.rightHalfPlaneVertices R ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z))
        ((L.image (P.shift z)).image (P.shift (verticalShift 2)))) < epsilon := by
  let Rset := L.image (P.shift (verticalShift 2))
  obtain ⟨z, n, hL, hR, herror⟩ :=
    E.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin
      mu hTI hunique hrR L Rset hepsilon
  have hcomm : Rset.image (P.shift z) =
      (L.image (P.shift z)).image (P.shift (verticalShift 2)) := by
    ext y
    simp only [Rset, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift z u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift 2) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  rw [hcomm] at hR herror
  exact ⟨z, n, hL, hR, herror⟩



theorem PeriodicPlaneEmbedding.exists_inward_separated_stripPlacement_with_margin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (t : Int) (L : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      (L.image (P.shift z) : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      ((L.image (P.shift z)).image
          (P.shift (verticalShift (1 + t))) : Set V) ⊆
        E.rightHalfPlaneVertices R ∧
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n
        (L.image (P.shift z))
        ((L.image (P.shift z)).image
          (P.shift (verticalShift (1 + t))))) < epsilon := by
  let Rset := L.image (P.shift (verticalShift (1 + t)))
  obtain ⟨z, n, hL, hR, herror⟩ :=
    E.exists_shift_stripPairMergeErrorUnion_measureReal_lt_with_margin
      mu hTI hunique hrR L Rset hepsilon
  have hcomm : Rset.image (P.shift z) =
      (L.image (P.shift z)).image
        (P.shift (verticalShift (1 + t))) := by
    ext y
    simp only [Rset, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift z u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add, ← P.shift_add, add_comm]
  rw [hcomm] at hR herror
  exact ⟨z, n, hL, hR, herror⟩

end StatMech.FK.PeriodicPlanar
