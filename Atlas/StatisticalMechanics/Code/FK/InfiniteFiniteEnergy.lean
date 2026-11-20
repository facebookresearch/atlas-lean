/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.FinitePatternEnergy
import Code.FK.FKGeneralQConsumer
import Code.FK.DensityFiniteToInfinite
import Code.FK.FKMixingClose
import Code.Percolation.BurtonKeaneMerge

open MeasureTheory Set Filter Topology SimpleGraph
open scoped BigOperators symmDiff

namespace StatMech
namespace FK

open StatMech.Lattice ConfigSpace

variable {d : ℕ}



theorem boxRestrictLE_setOpen {N m : ℕ} (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) (omega : ConfigSpace (Sym2 (boxVerts d m))) :
    boxRestrictLE d hNm (setOpen (innerEdgeLE d hNm eb) omega) =
      setOpen eb (boxRestrictLE d hNm omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrictLE]
  · have himg : innerEdgeLE d hNm x ≠ innerEdgeLE d hNm eb :=
      fun heq => hx (dfi_innerEdgeLE_injective d hNm heq)
    rw [boxRestrictLE, setOpen_of_ne himg, setOpen_of_ne hx]
    rfl


theorem boxRestrict_setOpen (N : ℕ) (eb : Sym2 (boxVerts d N))
    (omega : ConfigSpace (Sym2 (Site d))) :
    boxRestrict d N (setOpen (edgeIncl d N eb) omega) =
      setOpen eb (boxRestrict d N omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrict]
  · have himg : edgeIncl d N x ≠ edgeIncl d N eb :=
      fun heq => hx (edgeIncl_injective d N heq)
    rw [boxRestrict, setOpen_of_ne himg, setOpen_of_ne hx]
    rfl


theorem boxRestrictLE_setClosed {N m : ℕ} (hNm : N ≤ m)
    (eb : Sym2 (boxVerts d N)) (omega : ConfigSpace (Sym2 (boxVerts d m))) :
    boxRestrictLE d hNm (setClosed (innerEdgeLE d hNm eb) omega) =
      setClosed eb (boxRestrictLE d hNm omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrictLE]
  · have himg : innerEdgeLE d hNm x ≠ innerEdgeLE d hNm eb :=
      fun heq => hx (dfi_innerEdgeLE_injective d hNm heq)
    rw [boxRestrictLE, setClosed_of_ne himg, setClosed_of_ne hx]
    rfl


theorem boxRestrict_setClosed (N : ℕ) (eb : Sym2 (boxVerts d N))
    (omega : ConfigSpace (Sym2 (Site d))) :
    boxRestrict d N (setClosed (edgeIncl d N eb) omega) =
      setClosed eb (boxRestrict d N omega) := by
  funext x
  by_cases hx : x = eb
  · subst x
    simp [boxRestrict]
  · have himg : edgeIncl d N x ≠ edgeIncl d N eb :=
      fun heq => hx (edgeIncl_injective d N heq)
    rw [boxRestrict, setClosed_of_ne himg, setClosed_of_ne hx]
    rfl



theorem wiredFinite_singleOpen_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hpreT : boxRestrictLE d hNm ⁻¹' (setOpen eb ⁻¹' S) = setOpen em ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setOpen em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setOpen em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T hmeasT,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (setOpen em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (boundaryCliqueGraph (boxBoundary d m)) hp hp1 hq ({em} : Finset _)
    eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_clique_eq_wiredFkProb] using hbound


theorem freeFinite_singleOpen_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => true
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setOpen em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setOpen_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setOpen em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setOpen, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setOpen em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq) T hmeasT,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq)
      (setOpen em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (⊥ : SimpleGraph (boxVerts d m)) hp hp1 hq ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound


theorem wiredFinite_singleClosed_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => false
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setClosed em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setClosed_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setClosed em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setClosed, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setClosed em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) T hmeasT,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (setClosed em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (boundaryCliqueGraph (boxBoundary d m)) hp hp1 hq ({em} : Finset _)
    eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_clique_eq_wiredFkProb] using hbound


theorem freeFinite_singleClosed_preimage_bound
    (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  let em := innerEdgeLE d hNm eb
  let T := boxRestrictLE d hNm ⁻¹' S
  let eta : ConfigSpace ↥({em} : Finset (Sym2 (boxVerts d m))) := fun _ => false
  have hset : setPattern ({em} : Finset (Sym2 (boxVerts d m))) eta = setClosed em := by
    funext omega x
    by_cases hx : x = em
    · subst x
      simp [setPattern, eta]
    · rw [setPattern_of_not_mem eta (by simpa using hx), setClosed_of_ne hx]
  have hevent : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext omega
    simp only [Set.mem_preimage, T, boxRestrictLE_boxRestrict]
  have hpreEvent : boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S) =
      boxRestrict d m ⁻¹' (setClosed em ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage, T, em]
    rw [boxRestrictLE_setClosed, boxRestrictLE_boxRestrict]
  have hmeasT : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  have hmeasPre : MeasurableSet (boxRestrict d m ⁻¹' (setClosed em ⁻¹' T)) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [hevent, hpreEvent,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq) T hmeasT,
    freeFiniteMeasure_real_boxRestrictEvent m hp hp1 (zero_lt_one.trans_le hq)
      (setClosed em ⁻¹' T) hmeasPre]
  have hbound := cFE_pow_mul_bcPreimage_le_event (boxGraph d m)
    (⊥ : SimpleGraph (boxVerts d m)) hp hp1 hq ({em} : Finset _) eta T
  rw [hset] at hbound
  simpa only [Finset.card_singleton, pow_one, bcProb_bot_eq_fkProb] using hbound





theorem wiredInfinite_singleOpen_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N (setOpen eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  have hlhs := hc.mul hpre
  apply le_of_tendsto_of_tendsto hlhs hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact wiredFinite_singleOpen_preimage_bound N (phi n) hn hp hp1 hq eb S



theorem freeInfinite_singleOpen_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setOpen eb ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N (setOpen eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  have hlhs := hc.mul hpre
  apply le_of_tendsto_of_tendsto hlhs hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact freeFinite_singleOpen_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem wiredInfinite_singleClosed_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N (setClosed eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact wiredFinite_singleClosed_preimage_bound N (phi n) hn hp hp1 hq eb S


theorem freeInfinite_singleClosed_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (eb : Sym2 (boxVerts d N))
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setClosed eb ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  obtain ⟨phi, hphi, hconv⟩ :=
    freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hpre := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N (setClosed eb ⁻¹' S))
  have hbase := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hc : Tendsto (fun _ : ℕ => cFE p q) atTop (𝓝 (cFE p q)) := tendsto_const_nhds
  apply le_of_tendsto_of_tendsto (hc.mul hpre) hbase
  filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
  exact freeFinite_singleClosed_preimage_bound N (phi n) hn hp hp1 hq eb S




theorem setPattern_insert_eq
    {V : Type*} [DecidableEq V] {I : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∉ I) (eta : ConfigSpace ↥(insert e I))
    (psi : ConfigSpace (Sym2 V)) :
    let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
    setPattern (insert e I) eta psi =
      if eta ⟨e, Finset.mem_insert_self e I⟩ then
        setOpen e (setPattern I etaI psi)
      else setClosed e (setPattern I etaI psi) := by
  dsimp only
  funext x
  by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
  · simp only [heta, if_true]
    by_cases hxe : x = e
    · subst x
      simp [setPattern, he, heta]
    · by_cases hxI : x ∈ I
      · rw [setOpen_of_ne hxe]
        simp [setPattern, hxI, hxe]
      · rw [setOpen_of_ne hxe]
        simp [setPattern, hxI, hxe]
  · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
      Bool.eq_false_of_not_eq_true heta
    simp only [heta0, Bool.false_eq_true, if_false]
    by_cases hxe : x = e
    · subst x
      simp [setPattern, he, heta0]
    · by_cases hxI : x ∈ I
      · rw [setClosed_of_ne hxe]
        simp [setPattern, hxI, hxe]
      · rw [setClosed_of_ne hxe]
        simp [setPattern, hxI, hxe]



theorem wiredInfinite_pattern_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q ^ I.card *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  induction I using Finset.induction generalizing S with
  | empty =>
      simp only [Finset.card_empty, pow_zero, one_mul]
      have hset : setPattern ∅ eta = id := by
        funext psi
        exact setPattern_empty eta psi
      rw [hset]
      rfl
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      have hdecomp := setPattern_insert_eq he eta
      rw [Finset.card_insert_of_notMem he, pow_succ]
      by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
      · have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setOpen e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta, if_true, etaI]
        rw [hpre]
        have hih := ih etaI (setOpen e ⁻¹' S)
        have hone := wiredInfinite_singleOpen_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setOpen e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hone
      · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
          Bool.eq_false_of_not_eq_true heta
        have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setClosed e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta0, Bool.false_eq_true,
            if_false, etaI]
        rw [hpre]
        have hih := ih etaI (setClosed e ⁻¹' S)
        have hclosed := wiredInfinite_singleClosed_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setClosed e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hclosed



theorem freeInfinite_pattern_cylinder_bound
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    cFE p q ^ I.card *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' (setPattern I eta ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  classical
  induction I using Finset.induction generalizing S with
  | empty =>
      simp only [Finset.card_empty, pow_zero, one_mul]
      have hset : setPattern ∅ eta = id := by
        funext psi
        exact setPattern_empty eta psi
      rw [hset]
      rfl
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      have hdecomp := setPattern_insert_eq he eta
      rw [Finset.card_insert_of_notMem he, pow_succ]
      by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
      · have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setOpen e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta, if_true, etaI]
        rw [hpre]
        have hih := ih etaI (setOpen e ⁻¹' S)
        have hone := freeInfinite_singleOpen_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setOpen e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setOpen e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hone
      · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
          Bool.eq_false_of_not_eq_true heta
        have hpre : setPattern (insert e I) eta ⁻¹' S =
            setPattern I etaI ⁻¹' (setClosed e ⁻¹' S) := by
          ext psi
          simp only [Set.mem_preimage, hdecomp psi, heta0, Bool.false_eq_true,
            if_false, etaI]
        rw [hpre]
        have hih := ih etaI (setClosed e ⁻¹' S)
        have hclosed := freeInfinite_singleClosed_cylinder_bound N hp hp1 hq e S
        have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
        calc
          cFE p q ^ I.card * cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S))) =
              cFE p q * (cFE p q ^ I.card *
                (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                  (boxRestrict d N ⁻¹' (setPattern I etaI ⁻¹' (setClosed e ⁻¹' S)))) := by ring
          _ ≤ cFE p q *
              (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
                (boxRestrict d N ⁻¹' (setClosed e ⁻¹' S)) :=
            mul_le_mul_of_nonneg_left hih hc
          _ ≤ _ := hclosed




noncomputable def innerEdgeLEEmbedding (d : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    Sym2 (boxVerts d N) ↪ Sym2 (boxVerts d M) where
  toFun := innerEdgeLE d hNM
  inj' := dfi_innerEdgeLE_injective d hNM


noncomputable def liftPatternFinset (d : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) : Finset (Sym2 (boxVerts d M)) :=
  I.map (innerEdgeLEEmbedding d hNM)


noncomputable def liftPatternConfig (d : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I) :
    ConfigSpace ↥(liftPatternFinset d hNM I) := fun x =>
  eta ⟨Classical.choose (Finset.mem_map.mp x.2),
    (Classical.choose_spec (Finset.mem_map.mp x.2)).1⟩

@[simp]
theorem liftPatternConfig_apply (d : ℕ) {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (e : Sym2 (boxVerts d N)) (he : e ∈ I) :
    liftPatternConfig d hNM I eta
        ⟨innerEdgeLE d hNM e, by
          exact Finset.mem_map.mpr ⟨e, he, rfl⟩⟩ = eta ⟨e, he⟩ := by
  unfold liftPatternConfig
  let hmem : innerEdgeLE d hNM e ∈ liftPatternFinset d hNM I :=
    Finset.mem_map.mpr ⟨e, he, rfl⟩
  let a := Classical.choose (Finset.mem_map.mp hmem)
  have haeq : a = e := by
    apply dfi_innerEdgeLE_injective d hNM
    exact (Classical.choose_spec (Finset.mem_map.mp hmem)).2
  apply congrArg eta
  exact Subtype.ext haeq


theorem boxRestrictLE_setPattern {N M : ℕ} (hNM : N ≤ M)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (omega : ConfigSpace (Sym2 (boxVerts d M))) :
    boxRestrictLE d hNM
        (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) omega) =
      setPattern I eta (boxRestrictLE d hNM omega) := by
  funext e
  by_cases he : e ∈ I
  · rw [setPattern_of_mem eta he]
    rw [boxRestrictLE]
    have hmem : innerEdgeLE d hNM e ∈ liftPatternFinset d hNM I :=
      Finset.mem_map.mpr ⟨e, he, rfl⟩
    rw [setPattern_of_mem (liftPatternConfig d hNM I eta) hmem]
    simpa using liftPatternConfig_apply d hNM I eta e he
  · have hnot : innerEdgeLE d hNM e ∉ liftPatternFinset d hNM I := by
      intro hmem
      obtain ⟨a, haI, hae⟩ := Finset.mem_map.mp hmem
      exact he ((dfi_innerEdgeLE_injective d hNM hae) ▸ haI)
    rw [boxRestrictLE, setPattern_of_not_mem (liftPatternConfig d hNM I eta) hnot,
      setPattern_of_not_mem eta he]
    rfl



theorem wiredInfinite_innerPattern_outerCylinder_bound
    (N M : ℕ) (hNM : N ≤ M) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d M)))) :
    cFE p q ^ I.card *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d M ⁻¹'
            (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) ⁻¹' S)) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d M ⁻¹' S) := by
  have h := wiredInfinite_pattern_cylinder_bound M hp hp1 hq
    (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) S
  simpa [liftPatternFinset, Finset.card_map] using h


theorem freeInfinite_innerPattern_outerCylinder_bound
    (N M : ℕ) (hNM : N ≤ M) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (boxVerts d N))) (eta : ConfigSpace ↥I)
    (S : Set (ConfigSpace (Sym2 (boxVerts d M)))) :
    cFE p q ^ I.card *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d M ⁻¹'
            (setPattern (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) ⁻¹' S)) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d M ⁻¹' S) := by
  have h := freeInfinite_pattern_cylinder_bound M hp hp1 hq
    (liftPatternFinset d hNM I) (liftPatternConfig d hNM I eta) S
  simpa [liftPatternFinset, Finset.card_map] using h





theorem cylinder_eq_boxRestrict_preimage_extend
    (N : ℕ) (s : Finset (Sym2 (Site d)))
    (S : Set (ConfigSpace ↥s))
    (hs : ∀ e ∈ s, e ∈ Set.range (edgeIncl d N)) :
    cylinder s S = boxRestrict d N ⁻¹' (extendEdge d N ⁻¹' cylinder s S) := by
  ext omega
  simp only [Set.mem_preimage, MeasureTheory.mem_cylinder]
  have hrestr : s.restrict (extendEdge d N (boxRestrict d N omega)) = s.restrict omega := by
    funext e
    obtain ⟨eb, heb⟩ := hs e e.2
    change extendEdge d N (boxRestrict d N omega) e = omega e
    rw [← heb, extendEdge_eq_of_range]
    rfl
  rw [hrestr]


theorem wiredInfinite_singleOpen_fullCylinder_bound
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) (C : Set (ConfigSpace (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setOpen e ⁻¹' C) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box (insert e s)
  have heimg : e ∈ t.image (edgeIncl d N) := by
    rw [← hst]
    exact Finset.mem_insert_self e s
  obtain ⟨eb, hebt, hebe⟩ := Finset.mem_image.mp heimg
  have hsrange : ∀ x ∈ s, x ∈ Set.range (edgeIncl d N) := by
    intro x hx
    have hximg : x ∈ t.image (edgeIncl d N) := by
      rw [← hst]
      exact Finset.mem_insert_of_mem hx
    obtain ⟨xb, _, hxb⟩ := Finset.mem_image.mp hximg
    exact ⟨xb, hxb⟩
  let T := extendEdge d N ⁻¹' cylinder s S
  have hCeq : cylinder s S = boxRestrict d N ⁻¹' T :=
    cylinder_eq_boxRestrict_preimage_extend N s S hsrange
  have hpre : setOpen e ⁻¹' cylinder s S =
      boxRestrict d N ⁻¹' (setOpen eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hCeq]
    change boxRestrict d N (setOpen e omega) ∈ T ↔
      setOpen eb (boxRestrict d N omega) ∈ T
    rw [← hebe, boxRestrict_setOpen]
  rw [hpre, hCeq]
  exact wiredInfinite_singleOpen_cylinder_bound N hp hp1 hq eb T


theorem freeInfinite_singleOpen_fullCylinder_bound
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) (C : Set (ConfigSpace (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setOpen e ⁻¹' C) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box (insert e s)
  have heimg : e ∈ t.image (edgeIncl d N) := by
    rw [← hst]
    exact Finset.mem_insert_self e s
  obtain ⟨eb, _, hebe⟩ := Finset.mem_image.mp heimg
  have hsrange : ∀ x ∈ s, x ∈ Set.range (edgeIncl d N) := by
    intro x hx
    have hximg : x ∈ t.image (edgeIncl d N) := by
      rw [← hst]
      exact Finset.mem_insert_of_mem hx
    obtain ⟨xb, _, hxb⟩ := Finset.mem_image.mp hximg
    exact ⟨xb, hxb⟩
  let T := extendEdge d N ⁻¹' cylinder s S
  have hCeq : cylinder s S = boxRestrict d N ⁻¹' T :=
    cylinder_eq_boxRestrict_preimage_extend N s S hsrange
  have hpre : setOpen e ⁻¹' cylinder s S =
      boxRestrict d N ⁻¹' (setOpen eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hCeq]
    change boxRestrict d N (setOpen e omega) ∈ T ↔
      setOpen eb (boxRestrict d N omega) ∈ T
    rw [← hebe, boxRestrict_setOpen]
  rw [hpre, hCeq]
  exact freeInfinite_singleOpen_cylinder_bound N hp hp1 hq eb T


theorem wiredInfinite_singleClosed_fullCylinder_bound
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) (C : Set (ConfigSpace (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
    cFE p q *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setClosed e ⁻¹' C) ≤
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box (insert e s)
  have heimg : e ∈ t.image (edgeIncl d N) := by
    rw [← hst]
    exact Finset.mem_insert_self e s
  obtain ⟨eb, _, hebe⟩ := Finset.mem_image.mp heimg
  have hsrange : ∀ x ∈ s, x ∈ Set.range (edgeIncl d N) := by
    intro x hx
    have hximg : x ∈ t.image (edgeIncl d N) := by
      rw [← hst]
      exact Finset.mem_insert_of_mem hx
    obtain ⟨xb, _, hxb⟩ := Finset.mem_image.mp hximg
    exact ⟨xb, hxb⟩
  let T := extendEdge d N ⁻¹' cylinder s S
  have hCeq : cylinder s S = boxRestrict d N ⁻¹' T :=
    cylinder_eq_boxRestrict_preimage_extend N s S hsrange
  have hpre : setClosed e ⁻¹' cylinder s S =
      boxRestrict d N ⁻¹' (setClosed eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hCeq]
    change boxRestrict d N (setClosed e omega) ∈ T ↔
      setClosed eb (boxRestrict d N omega) ∈ T
    rw [← hebe, boxRestrict_setClosed]
  rw [hpre, hCeq]
  exact wiredInfinite_singleClosed_cylinder_bound N hp hp1 hq eb T


theorem freeInfinite_singleClosed_fullCylinder_bound
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) (C : Set (ConfigSpace (Sym2 (Site d))))
    (hC : C ∈ measurableCylinders (fun _ : Sym2 (Site d) => Bool)) :
    cFE p q *
        (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (setClosed e ⁻¹' C) ≤
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real C := by
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, S, _, rfl⟩ := hC
  obtain ⟨N, t, hst⟩ := cdc_finset_in_box (insert e s)
  have heimg : e ∈ t.image (edgeIncl d N) := by
    rw [← hst]
    exact Finset.mem_insert_self e s
  obtain ⟨eb, _, hebe⟩ := Finset.mem_image.mp heimg
  have hsrange : ∀ x ∈ s, x ∈ Set.range (edgeIncl d N) := by
    intro x hx
    have hximg : x ∈ t.image (edgeIncl d N) := by
      rw [← hst]
      exact Finset.mem_insert_of_mem hx
    obtain ⟨xb, _, hxb⟩ := Finset.mem_image.mp hximg
    exact ⟨xb, hxb⟩
  let T := extendEdge d N ⁻¹' cylinder s S
  have hCeq : cylinder s S = boxRestrict d N ⁻¹' T :=
    cylinder_eq_boxRestrict_preimage_extend N s S hsrange
  have hpre : setClosed e ⁻¹' cylinder s S =
      boxRestrict d N ⁻¹' (setClosed eb ⁻¹' T) := by
    ext omega
    simp only [Set.mem_preimage]
    rw [hCeq]
    change boxRestrict d N (setClosed e omega) ∈ T ↔
      setClosed eb (boxRestrict d N omega) ∈ T
    rw [← hebe, boxRestrict_setClosed]
  rw [hpre, hCeq]
  exact freeInfinite_singleClosed_cylinder_bound N hp hp1 hq eb T






theorem pattern_bound_of_cylinders
    {E : Type*} [Countable E]
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (f : ConfigSpace E → ConfigSpace E) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hcyl : ∀ C ∈ measurableCylinders (fun _ : E => Bool),
      c * mu.real (f ⁻¹' C) ≤ mu.real C)
    (A : Set (ConfigSpace E)) (hA : MeasurableSet A) :
    c * mu.real (f ⁻¹' A) ≤ mu.real A := by
  let nu : Measure (ConfigSpace E) := mu.map f
  let lam : Measure (ConfigSpace E) := mu + nu
  have hfA : MeasurableSet (f ⁻¹' A) := hA.preimage hf
  refine le_of_forall_pos_le_add fun eps heps => ?_
  let delta : ℝ := eps / (c + 1)
  have hc1 : 0 < c + 1 := by linarith
  have hdelta : 0 < delta := div_pos heps hc1
  obtain ⟨C, hCmem, happrox⟩ := fmc_exists_cylinder_symmDiff_lt lam hA
    (ε := ENNReal.ofReal delta) (by simpa using hdelta)
  have hC : MeasurableSet C := MeasurableSet.of_mem_measurableCylinders hCmem
  have hsd : MeasurableSet (C ∆ A) := hC.symmDiff hA
  have hlamReal : lam.real (C ∆ A) < delta := by
    have htop : lam (C ∆ A) ≠ ⊤ := measure_ne_top lam _
    have h := (ENNReal.toReal_lt_toReal htop (by simp)).2 happrox
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  have hmu_le : mu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_right le_rfl) (C ∆ A)
  have hnu_le : nu.real (C ∆ A) ≤ lam.real (C ∆ A) := by
    unfold Measure.real
    apply ENNReal.toReal_mono (measure_ne_top lam _)
    exact Measure.le_iff'.mp (Measure.le_add_left le_rfl) (C ∆ A)
  have hmuDiff : |mu.real C - mu.real A| < delta :=
    lt_of_le_of_lt
      (abs_measureReal_sub_le_measureReal_symmDiff hC.nullMeasurableSet hA.nullMeasurableSet)
      (hmu_le.trans_lt hlamReal)
  have hnuMap : nu.real (C ∆ A) = mu.real (f ⁻¹' (C ∆ A)) := by
    unfold nu Measure.real
    rw [Measure.map_apply hf hsd]
  have hpreSd : (f ⁻¹' (C ∆ A)) = (f ⁻¹' C) ∆ (f ⁻¹' A) :=
    by ext x; simp
  have hnuDiff : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| < delta := by
    have hpreC : MeasurableSet (f ⁻¹' C) := hC.preimage hf
    have habs : |mu.real (f ⁻¹' C) - mu.real (f ⁻¹' A)| ≤
        mu.real ((f ⁻¹' C) ∆ (f ⁻¹' A)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        hpreC.nullMeasurableSet hfA.nullMeasurableSet
    rw [← hpreSd, ← hnuMap] at habs
    exact lt_of_le_of_lt habs (hnu_le.trans_lt hlamReal)
  have hCbound := hcyl C hCmem
  obtain ⟨hmuLower, hmuUpper⟩ := abs_lt.mp hmuDiff
  obtain ⟨hnuLower, hnuUpper⟩ := abs_lt.mp hnuDiff
  dsimp [delta] at hmuLower hmuUpper hnuLower hnuUpper
  nlinarith [div_mul_cancel₀ eps (ne_of_gt hc1)]


theorem measurable_setOpen {E : Type*} [DecidableEq E] (e : E) :
    Measurable (setOpen e : ConfigSpace E → ConfigSpace E) := by
  apply measurable_pi_lambda
  intro x
  by_cases hx : x = e
  · subst x
    simp
  · rw [show (fun omega => setOpen e omega x) = fun omega => omega x by
      funext omega
      rw [setOpen_of_ne hx]]
    exact measurable_pi_apply x


theorem measurable_setClosed {E : Type*} [DecidableEq E] (e : E) :
    Measurable (setClosed e : ConfigSpace E → ConfigSpace E) := by
  apply measurable_pi_lambda
  intro x
  by_cases hx : x = e
  · subst x
    simp
  · rw [show (fun omega => setClosed e omega x) = fun omega => omega x by
      funext omega
      rw [setClosed_of_ne hx]]
    exact measurable_pi_apply x


theorem measurable_setPattern {V : Type*} [DecidableEq V]
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) :
    Measurable (setPattern I eta :
      ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) := by
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ I
  · rw [show (fun omega => setPattern I eta omega e) =
        fun _ => eta ⟨e, he⟩ by
      funext omega
      exact setPattern_of_mem eta he omega]
    exact measurable_const
  · rw [show (fun omega => setPattern I eta omega e) = fun omega => omega e by
      funext omega
      exact setPattern_of_not_mem eta he omega]
    exact measurable_pi_apply e



theorem map_absolutelyContinuous_of_real_preimage_bound
    {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [IsFiniteMeasure mu]
    (f : E → E) (hf : Measurable f) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ A : Set E, MeasurableSet A →
      c * mu.real (f ⁻¹' A) ≤ mu.real A) :
    mu.map f ≪ mu := by
  intro A hmuA
  let B := toMeasurable mu A
  have hAB : A ⊆ B := subset_toMeasurable mu A
  have hBmeas : MeasurableSet B := measurableSet_toMeasurable mu A
  have hmuB : mu B = 0 := by
    change mu (toMeasurable mu A) = 0
    rw [measure_toMeasurable, hmuA]
  have hmuBreal : mu.real B = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top mu B)).2 hmuB
  have hpreReal : mu.real (f ⁻¹' B) = 0 := by
    have h := hbound B hBmeas
    rw [hmuBreal] at h
    have hnonneg : 0 ≤ mu.real (f ⁻¹' B) := measureReal_nonneg
    nlinarith
  have hpre : mu (f ⁻¹' B) = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top mu _)).1 hpreReal
  apply le_antisymm
  · calc
      mu.map f A ≤ mu.map f B := measure_mono hAB
      _ = mu (f ⁻¹' B) := Measure.map_apply hf hBmeas
      _ = 0 := hpre
  · exact bot_le



theorem wiredInfinite_setOpen_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  apply map_absolutelyContinuous_of_real_preimage_bound
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq).le
    (wiredInfinite_singleOpen_fullCylinder_bound hp hp1 hq e) A hA



theorem freeInfinite_setOpen_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setOpen e) ≪
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  apply map_absolutelyContinuous_of_real_preimage_bound
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setOpen e) (measurable_setOpen e) (cFE p q) (cFE_pos hp hp1 hq).le
    (freeInfinite_singleOpen_fullCylinder_bound hp hp1 hq e) A hA



theorem wiredInfinite_setClosed_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setClosed e) ≪
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  apply map_absolutelyContinuous_of_real_preimage_bound
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setClosed e) (measurable_setClosed e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setClosed e) (measurable_setClosed e) (cFE p q) (cFE_pos hp hp1 hq).le
    (wiredInfinite_singleClosed_fullCylinder_bound hp hp1 hq e) A hA



theorem freeInfinite_setClosed_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 (Site d)) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map (setClosed e) ≪
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  apply map_absolutelyContinuous_of_real_preimage_bound
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setClosed e) (measurable_setClosed e) (cFE p q) (cFE_pos hp hp1 hq)
  intro A hA
  exact pattern_bound_of_cylinders
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (setClosed e) (measurable_setClosed e) (cFE p q) (cFE_pos hp hp1 hq).le
    (freeInfinite_singleClosed_fullCylinder_bound hp hp1 hq e) A hA





theorem setPattern_absolutelyContinuous_of_single
    {V : Type*} [DecidableEq V]
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hopen : ∀ e : Sym2 V, mu.map (setOpen e) ≪ mu)
    (hclosed : ∀ e : Sym2 V, mu.map (setClosed e) ≪ mu) :
    ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu := by
  intro I
  induction I using Finset.induction with
  | empty =>
      intro eta
      have hempty : setPattern (∅ : Finset (Sym2 V)) eta = id := by
        funext omega
        exact setPattern_empty eta omega
      rw [hempty, Measure.map_id]
  | @insert e I he ih =>
      intro eta
      let etaI : ConfigSpace ↥I :=
        fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      have hdecomp := setPattern_insert_eq he eta
      by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
      · have hfun : setPattern (insert e I) eta =
            setOpen e ∘ setPattern I etaI := by
          funext omega
          simpa [etaI, heta] using hdecomp omega
        have hmap := (ih etaI).map (measurable_setOpen e)
        have htrans := hmap.trans (hopen e)
        rw [Measure.map_map (measurable_setOpen e)
          (measurable_setPattern I etaI)] at htrans
        rwa [hfun]
      · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
          Bool.eq_false_of_not_eq_true heta
        have hfun : setPattern (insert e I) eta =
            setClosed e ∘ setPattern I etaI := by
          funext omega
          simpa [etaI, heta0] using hdecomp omega
        have hmap := (ih etaI).map (measurable_setClosed e)
        have htrans := hmap.trans (hclosed e)
        rw [Measure.map_map (measurable_setClosed e)
          (measurable_setPattern I etaI)] at htrans
        rwa [hfun]



theorem wiredInfinite_setPattern_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map
        (setPattern I eta) ≪
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  exact setPattern_absolutelyContinuous_of_single
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fun e => wiredInfinite_setOpen_absolutelyContinuous (d := d) hp hp1 hq e)
    (fun e => wiredInfinite_setClosed_absolutelyContinuous (d := d) hp hp1 hq e)
    I eta



theorem freeInfinite_setPattern_absolutelyContinuous
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).map
        (setPattern I eta) ≪
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  exact setPattern_absolutelyContinuous_of_single
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    (fun e => freeInfinite_setOpen_absolutelyContinuous (d := d) hp hp1 hq e)
    (fun e => freeInfinite_setClosed_absolutelyContinuous (d := d) hp hp1 hq e)
    I eta





theorem forceOpenFinset_insert (e : Sym2 (Site d)) (F : Finset (Sym2 (Site d))) :
    StatMech.Percolation.forceOpenFinset (insert e F) =
      setOpen e ∘ StatMech.Percolation.forceOpenFinset F := by
  funext omega x
  by_cases hxe : x = e
  · subst x
    simp [StatMech.Percolation.forceOpenFinset]
  · change StatMech.Percolation.forceOpenFinset (insert e F) omega x =
      setOpen e (StatMech.Percolation.forceOpenFinset F omega) x
    rw [setOpen_of_ne hxe]
    by_cases hxF : x ∈ F <;>
      simp [StatMech.Percolation.forceOpenFinset, hxe, hxF]



theorem hasFiniteEnergyMerge_of_singleOpen
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hone : ∀ e : Sym2 (Site d), mu.map (setOpen e) ≪ mu) :
    StatMech.Percolation.HasFiniteEnergyMerge mu := by
  intro F
  induction F using Finset.induction with
  | empty =>
      have hempty : StatMech.Percolation.forceOpenFinset
          (∅ : Finset (Sym2 (Site d))) = id := by
        funext omega x
        simp [StatMech.Percolation.forceOpenFinset]
      rw [hempty, Measure.map_id]
  | @insert e F he ih =>
      have hmap := ih.map (measurable_setOpen e)
      have htrans := hmap.trans (hone e)
      rw [Measure.map_map (measurable_setOpen e)
        (StatMech.Percolation.measurable_forceOpenFinset F)] at htrans
      rwa [← forceOpenFinset_insert e F] at htrans


theorem wiredInfiniteVolume_hasFiniteEnergyMerge
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    StatMech.Percolation.HasFiniteEnergyMerge (d := d)
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  change StatMech.Percolation.HasFiniteEnergyMerge (d := d) mu
  exact hasFiniteEnergyMerge_of_singleOpen mu
    (fun e => wiredInfinite_setOpen_absolutelyContinuous (d := d) hp hp1 hq e)


theorem freeInfiniteVolume_hasFiniteEnergyMerge
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    StatMech.Percolation.HasFiniteEnergyMerge (d := d)
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  change StatMech.Percolation.HasFiniteEnergyMerge (d := d) mu
  exact hasFiniteEnergyMerge_of_singleOpen mu
    (fun e => freeInfinite_setOpen_absolutelyContinuous (d := d) hp hp1 hq e)


end FK
end StatMech
