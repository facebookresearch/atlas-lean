/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FK.InfiniteFiniteEnergy
import Code.FK.PeriodicPlanarCanonicalErgodicity

open Filter MeasureTheory Set Topology
open scoped ENNReal StatMech

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [Countable V] [DecidableEq V]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrictLE_setOpen
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    (e : Sym2 (P.BufferedVertex N))
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    P.bufferedRestrictLE hNm
        (setOpen (Sym2.map (P.bufferedVertexInclLE hNm) e) omega) =
      setOpen e (P.bufferedRestrictLE hNm omega) := by
  funext x
  have hinj : Function.Injective
      (Sym2.map (P.bufferedVertexInclLE hNm)) :=
    Sym2.map.injective (P.bufferedVertexInclLE hNm).injective
  by_cases hx : x = e
  · subst x
    simp [PeriodicGraph.bufferedRestrictLE]
  · have hmap : Sym2.map (P.bufferedVertexInclLE hNm) x ≠
        Sym2.map (P.bufferedVertexInclLE hNm) e := hinj.ne hx
    unfold PeriodicGraph.bufferedRestrictLE
    rw [setOpen_of_ne hx, setOpen_of_ne hmap]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrict_setOpen
    (P : PeriodicGraph V) (N : Nat)
    (e : Sym2 (P.BufferedVertex N))
    (omega : ConfigSpace (Sym2 V)) :
    P.bufferedRestrict N
        (setOpen (P.edgeIncl (P.bufferedRadius N) e) omega) =
      setOpen e (P.bufferedRestrict N omega) := by
  funext x
  have hinj := P.edgeIncl_injective (P.bufferedRadius N)
  by_cases hx : x = e
  · subst x
    simp [PeriodicGraph.bufferedRestrict]
  · have hmap : P.edgeIncl (P.bufferedRadius N) x ≠
        P.edgeIncl (P.bufferedRadius N) e := hinj.ne hx
    unfold PeriodicGraph.bufferedRestrict
    rw [setOpen_of_ne hx, setOpen_of_ne hmap]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrictLE_setClosed
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    (e : Sym2 (P.BufferedVertex N))
    (omega : ConfigSpace (Sym2 (P.BufferedVertex m))) :
    P.bufferedRestrictLE hNm
        (setClosed (Sym2.map (P.bufferedVertexInclLE hNm) e) omega) =
      setClosed e (P.bufferedRestrictLE hNm omega) := by
  funext x
  have hinj : Function.Injective
      (Sym2.map (P.bufferedVertexInclLE hNm)) :=
    Sym2.map.injective (P.bufferedVertexInclLE hNm).injective
  by_cases hx : x = e
  · subst x
    simp [PeriodicGraph.bufferedRestrictLE]
  · have hmap : Sym2.map (P.bufferedVertexInclLE hNm) x ≠
        Sym2.map (P.bufferedVertexInclLE hNm) e := hinj.ne hx
    unfold PeriodicGraph.bufferedRestrictLE
    rw [setClosed_of_ne hx, setClosed_of_ne hmap]

omit [Countable V] in
theorem PeriodicGraph.bufferedRestrict_setClosed
    (P : PeriodicGraph V) (N : Nat)
    (e : Sym2 (P.BufferedVertex N))
    (omega : ConfigSpace (Sym2 V)) :
    P.bufferedRestrict N
        (setClosed (P.edgeIncl (P.bufferedRadius N) e) omega) =
      setClosed e (P.bufferedRestrict N omega) := by
  funext x
  have hinj := P.edgeIncl_injective (P.bufferedRadius N)
  by_cases hx : x = e
  · subst x
    simp [PeriodicGraph.bufferedRestrict]
  · have hmap : P.edgeIncl (P.bufferedRadius N) x ≠
        P.edgeIncl (P.bufferedRadius N) e := hinj.ne hx
    unfold PeriodicGraph.bufferedRestrict
    rw [setClosed_of_ne hx, setClosed_of_ne hmap]



theorem PeriodicGraph.freeBufferedMeasure_singleOpen_preimage_bound
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setOpen e ⁻¹' S)) <=
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  classical
  let em := Sym2.map (P.bufferedVertexInclLE hNm) e
  let T := P.bufferedRestrictLE hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (P.BufferedVertex m))) :=
    fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (P.BufferedVertex m))) eta =
      setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hpre : P.bufferedRestrictLE hNm ⁻¹' (setOpen e ⁻¹' S) =
      setOpen em ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [P.bufferedRestrictLE_setOpen]
  rw [P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq), hpre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (P.bufferedGraph m)
    (⊥ : SimpleGraph (P.BufferedVertex m)) hp hp1 hq
    ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound



theorem PeriodicGraph.wiredBufferedMeasure_singleOpen_preimage_bound
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setOpen e ⁻¹' S)) <=
      (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  classical
  let em := Sym2.map (P.bufferedVertexInclLE hNm) e
  let T := P.bufferedRestrictLE hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (P.BufferedVertex m))) :=
    fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (P.BufferedVertex m))) eta =
      setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hpre : P.bufferedRestrictLE hNm ⁻¹' (setOpen e ⁻¹' S) =
      setOpen em ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [P.bufferedRestrictLE_setOpen]
  rw [P.wiredBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq),
    P.wiredBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq), hpre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (P.bufferedGraph m)
    (Lattice.boundaryCliqueGraph (P.bufferedBoundary m)) hp hp1 hq
    ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one,
    bcProb_clique_eq_wiredFkProb] using hbound



theorem PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_cylinder_bound
    (P : PeriodicGraph V) (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setOpen e ⁻¹' S)) <=
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  have hpre := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N (setOpen e ⁻¹' S))
  have hbase := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hc : Tendsto (fun _ : Nat => cFE p q) atTop (nhds (cFE p q)) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [eventually_ge_atTop N] with m hm
  exact P.freeBufferedMeasure_singleOpen_preimage_bound hm hp hp1 hq e S



theorem PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_cylinder_bound
    (P : PeriodicGraph V) (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.wiredBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setOpen e ⁻¹' S)) <=
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  have hpre :=
    (P.wiredBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
      (P.bufferedCylinder_isClopen N (setOpen e ⁻¹' S))
  have hbase :=
    (P.wiredBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
      (P.bufferedCylinder_isClopen N S)
  have hc : Tendsto (fun _ : Nat => cFE p q) atTop (nhds (cFE p q)) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [eventually_ge_atTop N] with m hm
  exact P.wiredBufferedMeasure_singleOpen_preimage_bound hm hp hp1 hq e S

theorem PeriodicGraph.freeBufferedMeasure_singleClosed_preimage_bound
    (P : PeriodicGraph V) {N m : Nat} (hNm : N <= m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setClosed e ⁻¹' S)) <=
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  classical
  let em := Sym2.map (P.bufferedVertexInclLE hNm) e
  let T := P.bufferedRestrictLE hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (P.BufferedVertex m))) :=
    fun _ => false
  have hset : setPattern ({em} : Finset (Sym2 (P.BufferedVertex m))) eta =
      setClosed em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setClosed_of_ne hx]
  have hpre : P.bufferedRestrictLE hNm ⁻¹' (setClosed e ⁻¹' S) =
      setClosed em ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [P.bufferedRestrictLE_setClosed]
  rw [P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq),
    P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq), hpre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (P.bufferedGraph m)
    (⊥ : SimpleGraph (P.BufferedVertex m)) hp hp1 hq
    ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound

theorem PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_cylinder_bound
    (P : PeriodicGraph V) (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 (P.BufferedVertex N))
    (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))) :
    cFE p q *
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N (setClosed e ⁻¹' S)) <=
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N S) := by
  have hpre := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N (setClosed e ⁻¹' S))
  have hbase := (P.freeBufferedMeasure_weakConverges hp hp1 hq).tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hc : Tendsto (fun _ : Nat => cFE p q) atTop (nhds (cFE p q)) :=
    tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [eventually_ge_atTop N] with m hm
  exact P.freeBufferedMeasure_singleClosed_preimage_bound hm hp hp1 hq e S


theorem PeriodicGraph.freeBufferedInfiniteVolume_singleOpen_fullCylinder_bound
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 V) (C : Set (ConfigSpace (Sym2 V)))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
    cFE p q *
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setOpen e ⁻¹' C) <=
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges (insert e s)
  obtain ⟨eb, hebe⟩ := hN e (Finset.mem_insert_self e s)
  have hsrange : ∀ x ∈ s,
      x ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
    intro x hx
    exact hN x (Finset.mem_insert_of_mem hx)
  let T := P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S
  have hCeq : cylinder s S = P.bufferedCylinder N T :=
    P.fullCylinder_eq_bufferedCylinder N s S hsrange
  have hpre : setOpen e ⁻¹' cylinder s S =
      P.bufferedCylinder N (setOpen eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, PeriodicGraph.bufferedCylinder]
    rw [hCeq]
    change P.bufferedRestrict N (setOpen e omega) ∈ T ↔
      setOpen eb (P.bufferedRestrict N omega) ∈ T
    rw [← hebe, P.bufferedRestrict_setOpen]
  rw [hpre, hCeq]
  exact P.freeBufferedInfiniteVolume_singleOpen_cylinder_bound N hp hp1 hq eb T



theorem PeriodicGraph.wiredBufferedInfiniteVolume_singleOpen_fullCylinder_bound
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 V) (C : Set (ConfigSpace (Sym2 V)))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
    cFE p q *
        (P.wiredBufferedInfiniteVolume hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real (setOpen e ⁻¹' C) <=
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges (insert e s)
  obtain ⟨eb, hebe⟩ := hN e (Finset.mem_insert_self e s)
  have hsrange : ∀ x ∈ s,
      x ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
    intro x hx
    exact hN x (Finset.mem_insert_of_mem hx)
  let T := P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S
  have hCeq : cylinder s S = P.bufferedCylinder N T :=
    P.fullCylinder_eq_bufferedCylinder N s S hsrange
  have hpre : setOpen e ⁻¹' cylinder s S =
      P.bufferedCylinder N (setOpen eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, PeriodicGraph.bufferedCylinder]
    rw [hCeq]
    change P.bufferedRestrict N (setOpen e omega) ∈ T ↔
      setOpen eb (P.bufferedRestrict N omega) ∈ T
    rw [← hebe, P.bufferedRestrict_setOpen]
  rw [hpre, hCeq]
  exact P.wiredBufferedInfiniteVolume_singleOpen_cylinder_bound
    N hp hp1 hq eb T

theorem PeriodicGraph.freeBufferedInfiniteVolume_singleClosed_fullCylinder_bound
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (e : Sym2 V) (C : Set (ConfigSpace (Sym2 V)))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 V => Bool)) :
    cFE p q *
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setClosed e ⁻¹' C) <=
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges (insert e s)
  obtain ⟨eb, hebe⟩ := hN e (Finset.mem_insert_self e s)
  have hsrange : ∀ x ∈ s,
      x ∈ Set.range (P.edgeIncl (P.bufferedRadius N)) := by
    intro x hx
    exact hN x (Finset.mem_insert_of_mem hx)
  let T := P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder s S
  have hCeq : cylinder s S = P.bufferedCylinder N T :=
    P.fullCylinder_eq_bufferedCylinder N s S hsrange
  have hpre : setClosed e ⁻¹' cylinder s S =
      P.bufferedCylinder N (setClosed eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, PeriodicGraph.bufferedCylinder]
    rw [hCeq]
    change P.bufferedRestrict N (setClosed e omega) ∈ T ↔
      setClosed eb (P.bufferedRestrict N omega) ∈ T
    rw [← hebe, P.bufferedRestrict_setClosed]
  rw [hpre, hCeq]
  exact P.freeBufferedInfiniteVolume_singleClosed_cylinder_bound N hp hp1 hq eb T


theorem PeriodicGraph.freeBufferedInfiniteVolume_setOpen_absolutelyContinuous
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) (e : Sym2 V) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map
        (setOpen e) ≪
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  apply map_absolutelyContinuous_of_real_preimage_bound mu
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders mu (setOpen e) (measurable_setOpen e)
    (cFE p q) (cFE_pos hp hp1 hq).le
    (P.freeBufferedInfiniteVolume_singleOpen_fullCylinder_bound hp hp1 hq e) A hA



theorem PeriodicGraph.wiredBufferedInfiniteVolume_setOpen_absolutelyContinuous
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) (e : Sym2 V) :
    (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  apply map_absolutelyContinuous_of_real_preimage_bound mu
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders mu (setOpen e) (measurable_setOpen e)
    (cFE p q) (cFE_pos hp hp1 hq).le
    (P.wiredBufferedInfiniteVolume_singleOpen_fullCylinder_bound
      hp hp1 hq e) A hA

theorem PeriodicGraph.freeBufferedInfiniteVolume_setClosed_absolutelyContinuous
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) (e : Sym2 V) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map
        (setClosed e) ≪
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  apply map_absolutelyContinuous_of_real_preimage_bound mu
    (setClosed e) (measurable_setClosed e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders mu (setClosed e) (measurable_setClosed e)
    (cFE p q) (cFE_pos hp hp1 hq).le
    (P.freeBufferedInfiniteVolume_singleClosed_fullCylinder_bound hp hp1 hq e) A hA



theorem PeriodicGraph.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).map
        (setPattern I eta) ≪
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  exact setPattern_absolutelyContinuous_of_single
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fun e => P.freeBufferedInfiniteVolume_setOpen_absolutelyContinuous hp hp1 hq e)
    (fun e => P.freeBufferedInfiniteVolume_setClosed_absolutelyContinuous hp hp1 hq e)
    I eta

theorem forceOpenFinset_insert (e : Sym2 V) (F : Finset (Sym2 V)) :
    forceOpenFinset (insert e F) = setOpen e ∘ forceOpenFinset F := by
  funext omega x
  by_cases hxe : x = e
  · subst x
    simp [forceOpenFinset]
  · change forceOpenFinset (insert e F) omega x =
      setOpen e (forceOpenFinset F omega) x
    rw [setOpen_of_ne hxe]
    simp only [forceOpenFinset, Finset.mem_insert]
    by_cases hxF : x ∈ F <;> simp [hxe, hxF]



theorem hasFiniteEnergy_of_singleOpen
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hone : ∀ e : Sym2 V, mu.map (setOpen e) ≪ mu) :
    HasFiniteEnergy mu := by
  intro F
  induction F using Finset.induction with
  | empty =>
      have hempty : forceOpenFinset (∅ : Finset (Sym2 V)) = id := by
        funext omega x
        simp [forceOpenFinset]
      rw [hempty, Measure.map_id]
  | @insert e F he ih =>
      have hmap := ih.map (measurable_setOpen e)
      have htrans := hmap.trans (hone e)
      rw [Measure.map_map (measurable_setOpen e)
        (measurable_forceOpenFinset F)] at htrans
      rwa [← forceOpenFinset_insert e F] at htrans


theorem PeriodicGraph.freeBufferedInfiniteVolume_hasFiniteEnergy
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    HasFiniteEnergy
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) := by
  apply hasFiniteEnergy_of_singleOpen (V := V)
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  intro e
  exact P.freeBufferedInfiniteVolume_setOpen_absolutelyContinuous hp hp1 hq e


theorem PeriodicGraph.wiredBufferedInfiniteVolume_hasFiniteEnergy
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    HasFiniteEnergy
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) := by
  apply hasFiniteEnergy_of_singleOpen (V := V)
    (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  intro e
  exact P.wiredBufferedInfiniteVolume_setOpen_absolutelyContinuous hp hp1 hq e

end StatMech.FK.PeriodicPlanar
