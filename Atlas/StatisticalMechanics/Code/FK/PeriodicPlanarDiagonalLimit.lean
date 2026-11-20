/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarCanonicalSheffieldFKG










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]



theorem PeriodicGraph.wiredBufferedRootBoundary_diag_antitone
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    Antitone (fun n =>
      (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n))) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    (P.wiredBufferedMeasure (n + 1) hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real
        (P.bufferedCylinder (n + 1) (P.bufferedRootBoundaryEvent (n + 1)))
      <= (P.wiredBufferedMeasure (n + 1) hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)) :=
        measureReal_mono (P.bufferedRootBoundaryCylinder_antitone
          (Nat.le_succ n))
    _ <= (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)) :=
        P.wiredBufferedMeasure_step_cylinder (le_refl n) hp hp1 hq
          (P.bufferedRootBoundaryEvent_isIncreasing n)



theorem PeriodicGraph.wiredBufferedRootBoundary_diag_tendsto
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    Tendsto
      (fun n =>
        (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)))
      atTop (nhds (P.wiredPercolationProbability p q)) := by
  let mu := fun n =>
    (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  let nu :=
    (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  let C := fun n => P.bufferedCylinder n (P.bufferedRootBoundaryEvent n)
  let a := fun n => (mu n).real (C n)
  let b := fun n => nu.real (C n)
  have hanti : Antitone a := by
    simpa only [a, mu, C] using
      P.wiredBufferedRootBoundary_diag_antitone hp hp1 hq
  have habove : BddBelow (Set.range a) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact measureReal_nonneg⟩
  let L := iInf a
  have halim : Tendsto a atTop (nhds L) := by
    dsimp only [L]
    exact tendsto_atTop_ciInf hanti habove
  have hblim : Tendsto b atTop
      (nhds (P.wiredPercolationProbability p q)) := by
    simpa only [b, nu, C] using
      P.bufferedRootBoundaryCylinder_real_tendsto hp hp1
        (zero_lt_one.trans_le hq)
  have hLle : L <= P.wiredPercolationProbability p q := by
    have hLbk : forall k, L <= b k := by
      intro k
      have hfixed := P.wiredBufferedMeasure_tendsto_cylinder k hp hp1 hq
        (P.bufferedRootBoundaryEvent_isIncreasing k)
      have hdiagShift := halim.comp (tendsto_add_atTop_nat k)
      have hfixedShift := hfixed.comp (tendsto_add_atTop_nat k)
      apply le_of_tendsto_of_tendsto' hdiagShift
        (by simpa only [b, nu, C, mu] using hfixedShift)
      intro n
      exact measureReal_mono
        (P.bufferedRootBoundaryCylinder_antitone (Nat.le_add_left k n))
        (measure_ne_top _ _)
    exact ge_of_tendsto hblim (Filter.Eventually.of_forall hLbk)
  have hthetaLe : P.wiredPercolationProbability p q <= L := by
    have hbk : forall k, b k <= a k := by
      intro k
      have hfixed := P.wiredBufferedMeasure_tendsto_cylinder k hp hp1 hq
        (P.bufferedRootBoundaryEvent_isIncreasing k)
      have hfixed' : Tendsto
          (fun m => (mu m).real (C k)) atTop (nhds (b k)) := by
        simpa only [mu, C, b, nu] using hfixed
      apply le_of_tendsto hfixed'
      filter_upwards [eventually_ge_atTop k] with m hkm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
      have hfixedAnti : Antitone (fun j => (mu (k + j)).real (C k)) := by
        apply antitone_nat_of_succ_le
        intro i
        simpa only [mu, C, Nat.add_assoc] using
          P.wiredBufferedMeasure_step_cylinder (Nat.le_add_right k i)
            hp hp1 hq (P.bufferedRootBoundaryEvent_isIncreasing k)
      simpa only [a, C, mu] using hfixedAnti (Nat.zero_le j)
    exact le_of_tendsto_of_tendsto' hblim halim hbk
  rw [le_antisymm hLle hthetaLe] at halim
  exact halim




theorem PeriodicGraph.wiredBufferedSetBoundary_diag_tendsto
    (P : PeriodicGraph V) (S : Set V) (hSfinite : S.Finite) (N : Nat)
    (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    Tendsto
      (fun n =>
        (P.wiredBufferedMeasure (N + n) hp hp1
          (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (P.bufferedCylinder (N + n)
            (P.bufferedSetBoundaryEvent S (N + n))))
      atTop
      (nhds ((P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V))).real
          (P.setHitsInfinite S))) := by
  let mu := fun n =>
    (P.wiredBufferedMeasure n hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  let nu :=
    (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
  let C := fun n => P.bufferedCylinder n (P.bufferedSetBoundaryEvent S n)
  let a := fun n => (mu (N + n)).real (C (N + n))
  let b := fun n => nu.real (C (N + n))
  have hanti : Antitone a := by
    apply antitone_nat_of_succ_le
    intro n
    calc
      (mu (N + (n + 1))).real (C (N + (n + 1))) ≤
          (mu (N + (n + 1))).real (C (N + n)) :=
        measureReal_mono
          (P.bufferedSetBoundaryCylinder_antitone_from S N hS
            (Nat.le_succ n))
      _ ≤ (mu (N + n)).real (C (N + n)) := by
        simpa only [mu, C, Nat.add_assoc] using
          P.wiredBufferedMeasure_step_cylinder (le_refl (N + n))
            hp hp1 hq (P.bufferedSetBoundaryEvent_isIncreasing S (N + n))
  have habove : BddBelow (Set.range a) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact measureReal_nonneg⟩
  let L := iInf a
  have halim : Tendsto a atTop (nhds L) := by
    dsimp only [L]
    exact tendsto_atTop_ciInf hanti habove
  have hblim : Tendsto b atTop (nhds (nu.real (P.setHitsInfinite S))) := by
    have htend := tendsto_measure_iInter_atTop
      (μ := nu)
      (fun n =>
        (P.bufferedSetBoundaryCylinder_isClopen S (N + n)).1.nullMeasurableSet)
      (P.bufferedSetBoundaryCylinder_antitone_from S N hS)
      ⟨0, measure_ne_top nu _⟩
    rw [P.iInter_bufferedSetBoundaryCylinder S hSfinite N hS] at htend
    have hreal :=
      (ENNReal.tendsto_toReal (measure_ne_top nu (P.setHitsInfinite S))).comp htend
    simpa only [b, C, Function.comp_apply, Measure.real] using hreal
  have hLle : L ≤ nu.real (P.setHitsInfinite S) := by
    have hLbk : ∀ k, L ≤ b k := by
      intro k
      have hfixed := P.wiredBufferedMeasure_tendsto_cylinder (N + k)
        hp hp1 hq (P.bufferedSetBoundaryEvent_isIncreasing S (N + k))
      have hdiagShift := halim.comp (tendsto_add_atTop_nat k)
      have hfixedShift := hfixed.comp (tendsto_add_atTop_nat (N + k))
      apply le_of_tendsto_of_tendsto' hdiagShift
        (by simpa only [b, nu, C, mu, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hfixedShift)
      intro n
      have hm := measureReal_mono
        (P.bufferedSetBoundaryCylinder_antitone_from S N hS
          (Nat.le_add_left k n)) (measure_ne_top (mu (N + (n + k))) _)
      rw [Nat.add_comm n k] at hm
      simpa only [a, mu, C, Function.comp_apply, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hm
    exact ge_of_tendsto hblim (Filter.Eventually.of_forall hLbk)
  have hnuLe : nu.real (P.setHitsInfinite S) ≤ L := by
    have hbk : ∀ k, b k ≤ a k := by
      intro k
      have hfixed := P.wiredBufferedMeasure_tendsto_cylinder (N + k)
        hp hp1 hq (P.bufferedSetBoundaryEvent_isIncreasing S (N + k))
      have hfixed' : Tendsto
          (fun m => (mu m).real (C (N + k))) atTop (nhds (b k)) := by
        simpa only [mu, C, b, nu] using hfixed
      apply le_of_tendsto hfixed'
      filter_upwards [eventually_ge_atTop (N + k)] with m hkm
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
      have hfixedAnti : Antitone
          (fun j => (mu ((N + k) + j)).real (C (N + k))) := by
        apply antitone_nat_of_succ_le
        intro i
        simpa only [mu, C, Nat.add_assoc] using
          P.wiredBufferedMeasure_step_cylinder
            (Nat.le_add_right (N + k) i) hp hp1 hq
            (P.bufferedSetBoundaryEvent_isIncreasing S (N + k))
      simpa only [a, C, mu] using hfixedAnti (Nat.zero_le j)
    exact le_of_tendsto_of_tendsto' hblim halim hbk
  rw [le_antisymm hLle hnuLe] at halim
  exact halim

end StatMech.FK.PeriodicPlanar
