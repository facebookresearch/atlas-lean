/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolumeFKG
public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeDLRExtreme
public import MathlibExt.Probability.CorrelationInequalities.InfiniteHarris
public import PhyslibExt.StatisticalMechanics.RandomCluster.MeasurableFKGClosure

/-!
# The FKG property for the buffered infinite-volume FK measures

For `0 < p < 1` and `q ≥ 1`, the free and wired buffered infinite-volume random-cluster measures on
a periodic graph are FKG.

## i. Overview

The finite-volume free and wired FK measures on buffered boxes satisfy the FKG inequality, so the
inequality holds for increasing cylinder events of a fixed box at every larger volume. Passing to
the weak limits gives it for the infinite-volume measures on increasing cylinders, hence on all
increasing clopen events, and a measurable closure argument extends it to all measurable increasing
events. Antitone limits give the inequality for decreasing intersections of increasing clopen or
cylinder events. `freeBufferedInfiniteVolume_isFKG` and `wiredBufferedInfiniteVolume_isFKG` are
proved unconditionally, with only `0 < p < 1` and `1 ≤ q`.

## ii. Key results

- `PeriodicGraph.freeBufferedInfiniteVolume_fkg_isClopen` : the FKG inequality for increasing
  clopen events under the free limit.
- `PeriodicGraph.freeBufferedInfiniteVolume_isFKG` : the free buffered infinite-volume FK measure
  is FKG.
- `PeriodicGraph.wiredBufferedInfiniteVolume_isFKG` : the wired buffered infinite-volume FK measure
  is FKG.

## iii. Table of contents

- A. Finite-volume FKG on buffered cylinders
- B. Infinite-volume FKG on cylinders and clopen events
- C. The FKG property
- D. Decreasing intersections

## iv. References

- C. M. Fortuin, P. W. Kasteleyn, and J. Ginibre, *Correlation inequalities on some partially
  ordered sets*, Comm. Math. Phys. 22 (1971).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]

/-! ## A. Finite-volume FKG on buffered cylinders -/

lemma PeriodicGraph.freeBufferedMeasure_fkg_cylinder
    (P : PeriodicGraph V) (N m : Nat) (hNm : N <= m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N A) *
        (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N B) <=
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N (A ∩ B)) := by
  let A' := P.bufferedRestrictLE hNm ⁻¹' A
  let B' := P.bufferedRestrictLE hNm ⁻¹' B
  have hA' : IsIncreasing A' := fun _ _ hab ha =>
    hA (P.monotone_bufferedRestrictLE hNm hab) ha
  have hB' : IsIncreasing B' := fun _ _ hab hb =>
    hB (P.monotone_bufferedRestrictLE hNm hab) hb
  rw [P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) A,
    P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) B,
    P.freeBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) (A ∩ B)]
  have hfkg := fkProb_positively_associated_events
    (P.bufferedGraph m) hp hp1 hq hA' hB'
  change
    (∑ omega, A'.indicator (fun _ => (1 : Real)) omega *
        fkProb (P.bufferedGraph m) p q omega) *
      (∑ omega, B'.indicator (fun _ => (1 : Real)) omega *
        fkProb (P.bufferedGraph m) p q omega) <=
      ∑ omega, (A' ∩ B').indicator (fun _ => (1 : Real)) omega *
        fkProb (P.bufferedGraph m) p q omega
  calc
    _ = (∑ omega, fkProb (P.bufferedGraph m) p q omega *
          A'.indicator (fun _ => (1 : Real)) omega) *
        (∑ omega, fkProb (P.bufferedGraph m) p q omega *
          B'.indicator (fun _ => (1 : Real)) omega) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro omega homega <;>
        exact mul_comm _ _
    _ <= ∑ omega, fkProb (P.bufferedGraph m) p q omega *
        (A' ∩ B').indicator (fun _ => (1 : Real)) omega := hfkg
    _ = _ := by
      apply Finset.sum_congr rfl
      intro omega homega
      exact mul_comm _ _

lemma PeriodicGraph.wiredBufferedMeasure_fkg_cylinder
    (P : PeriodicGraph V) (N m : Nat) (hNm : N <= m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N A) *
        (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (P.bufferedCylinder N B) <=
      (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (P.bufferedCylinder N (A ∩ B)) := by
  let A' := P.bufferedRestrictLE hNm ⁻¹' A
  let B' := P.bufferedRestrictLE hNm ⁻¹' B
  have hA' : IsIncreasing A' := fun _ _ hab ha =>
    hA (P.monotone_bufferedRestrictLE hNm hab) ha
  have hB' : IsIncreasing B' := fun _ _ hab hb =>
    hB (P.monotone_bufferedRestrictLE hNm hab) hb
  rw [P.wiredBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) A,
    P.wiredBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) B,
    P.wiredBufferedMeasure_real_cylinder hNm hp hp1
      (zero_lt_one.trans_le hq) (A ∩ B)]
  have hfkg := wiredFkProb_positively_associated_events
    (P.bufferedGraph m) (P.bufferedBoundary m) hp hp1 hq hA' hB'
  change
    (∑ omega, A'.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega) *
      (∑ omega, B'.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega) <=
      ∑ omega, (A' ∩ B').indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega
  calc
    _ = (∑ omega,
          wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega *
            A'.indicator (fun _ => (1 : Real)) omega) *
        (∑ omega,
          wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega *
            B'.indicator (fun _ => (1 : Real)) omega) := by
      congr 1 <;> apply Finset.sum_congr rfl <;> intro omega homega <;>
        exact mul_comm _ _
    _ <= ∑ omega,
        wiredFkProb (P.bufferedGraph m) (P.bufferedBoundary m) p q omega *
          (A' ∩ B').indicator (fun _ => (1 : Real)) omega := hfkg
    _ = _ := by
      apply Finset.sum_congr rfl
      intro omega homega
      exact mul_comm _ _

/-! ## B. Infinite-volume FKG on cylinders and clopen events -/

lemma PeriodicGraph.freeBufferedInfiniteVolume_fkg_cylinder
    (P : PeriodicGraph V) (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.bufferedCylinder N A) * mu.real (P.bufferedCylinder N B) <=
      mu.real (P.bufferedCylinder N (A ∩ B)) := by
  dsimp only
  have hAt := P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hA
  have hBt := P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hB
  have hABt := P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq
    (hA.inter hB)
  exact le_of_tendsto_of_tendsto (hAt.mul hBt) hABt <| by
    filter_upwards [eventually_ge_atTop N] with m hm
    exact P.freeBufferedMeasure_fkg_cylinder N m hm hp hp1 hq hA hB

lemma PeriodicGraph.wiredBufferedInfiniteVolume_fkg_cylinder
    (P : PeriodicGraph V) (N : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.bufferedCylinder N A) * mu.real (P.bufferedCylinder N B) <=
      mu.real (P.bufferedCylinder N (A ∩ B)) := by
  dsimp only
  have hAt := P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hA
  have hBt := P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hB
  have hABt := P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq
    (hA.inter hB)
  exact le_of_tendsto_of_tendsto (hAt.mul hBt) hABt <| by
    filter_upwards [eventually_ge_atTop N] with m hm
    exact P.wiredBufferedMeasure_fkg_cylinder N m hm hp hp1 hq hA hB

/-- The FKG inequality for increasing clopen events under the free buffered infinite-volume FK
measure. -/
lemma PeriodicGraph.freeBufferedInfiniteVolume_fkg_isClopen
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 V))}
    (hAcl : IsClopen A) (hBcl : IsClopen B)
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real A * mu.real B <= mu.real (A ∩ B) := by
  classical
  dsimp only
  obtain ⟨FA, hFA⟩ := isClopen_dependsOn_finset A hAcl
  obtain ⟨FB, hFB⟩ := isClopen_dependsOn_finset B hBcl
  let F : Finset (Sym2 V) := FA ∪ FB
  have hAdep : StatMech.DependsOn A (F : Set (Sym2 V)) :=
    hFA.mono (by intro e he; exact Finset.mem_union_left FB he)
  have hBdep : StatMech.DependsOn B (F : Set (Sym2 V)) :=
    hFB.mono (by intro e he; exact Finset.mem_union_right FA he)
  let SA := ih_section A F
  let SB := ih_section B F
  have hAcyl : A = cylinder F SA := ih_eq_cylinder_of_dependsOn F hAdep
  have hBcyl : B = cylinder F SB := ih_eq_cylinder_of_dependsOn F hBdep
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges F
  let RA : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
    P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder F SA
  let RB : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
    P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder F SB
  have hRA : IsIncreasing RA := by
    dsimp only [RA]
    rw [← hAcyl]
    exact fun omega eta home hmem => hA (P.monotone_extendEdge _ home) hmem
  have hRB : IsIncreasing RB := by
    dsimp only [RB]
    rw [← hBcyl]
    exact fun omega eta home hmem => hB (P.monotone_extendEdge _ home) hmem
  have hAcyl' : A = P.bufferedCylinder N RA := by
    rw [hAcyl]
    exact P.fullCylinder_eq_bufferedCylinder N F SA hN
  have hBcyl' : B = P.bufferedCylinder N RB := by
    rw [hBcyl]
    exact P.fullCylinder_eq_bufferedCylinder N F SB hN
  rw [hAcyl', hBcyl']
  simpa only [PeriodicGraph.bufferedCylinder, Set.preimage_inter] using
    P.freeBufferedInfiniteVolume_fkg_cylinder N hp hp1 hq hRA hRB

lemma PeriodicGraph.wiredBufferedInfiniteVolume_fkg_isClopen
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A B : Set (ConfigSpace (Sym2 V))}
    (hAcl : IsClopen A) (hBcl : IsClopen B)
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real A * mu.real B <= mu.real (A ∩ B) := by
  classical
  dsimp only
  obtain ⟨FA, hFA⟩ := isClopen_dependsOn_finset A hAcl
  obtain ⟨FB, hFB⟩ := isClopen_dependsOn_finset B hBcl
  let F : Finset (Sym2 V) := FA ∪ FB
  have hAdep : StatMech.DependsOn A (F : Set (Sym2 V)) :=
    hFA.mono (by intro e he; exact Finset.mem_union_left FB he)
  have hBdep : StatMech.DependsOn B (F : Set (Sym2 V)) :=
    hFB.mono (by intro e he; exact Finset.mem_union_right FA he)
  let SA := ih_section A F
  let SB := ih_section B F
  have hAcyl : A = cylinder F SA := ih_eq_cylinder_of_dependsOn F hAdep
  have hBcyl : B = cylinder F SB := ih_eq_cylinder_of_dependsOn F hBdep
  obtain ⟨N, hN⟩ := P.exists_bufferedLevel_edges F
  let RA : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
    P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder F SA
  let RB : Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
    P.extendEdge (P.bufferedRadius N) ⁻¹' cylinder F SB
  have hRA : IsIncreasing RA := by
    dsimp only [RA]
    rw [← hAcyl]
    exact fun omega eta home hmem => hA (P.monotone_extendEdge _ home) hmem
  have hRB : IsIncreasing RB := by
    dsimp only [RB]
    rw [← hBcyl]
    exact fun omega eta home hmem => hB (P.monotone_extendEdge _ home) hmem
  have hAcyl' : A = P.bufferedCylinder N RA := by
    rw [hAcyl]
    exact P.fullCylinder_eq_bufferedCylinder N F SA hN
  have hBcyl' : B = P.bufferedCylinder N RB := by
    rw [hBcyl]
    exact P.fullCylinder_eq_bufferedCylinder N F SB hN
  rw [hAcyl', hBcyl']
  simpa only [PeriodicGraph.bufferedCylinder, Set.preimage_inter] using
    P.wiredBufferedInfiniteVolume_fkg_cylinder N hp hp1 hq hRA hRB

/-! ## C. The FKG property -/

/-- For `0 < p < 1` and `q ≥ 1`, the free buffered infinite-volume FK measure is FKG. -/
theorem PeriodicGraph.freeBufferedInfiniteVolume_isFKG
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    IsFKG mu := by
  dsimp only
  intro A B hAmeas hBmeas hAinc hBinc
  apply fkg_measurable_of_isClopen _ _ A B hAmeas hBmeas hAinc hBinc
  intro C D hCcl hDcl hCinc hDinc
  exact P.freeBufferedInfiniteVolume_fkg_isClopen
    hp hp1 hq hCcl hDcl hCinc hDinc

/-- For `0 < p < 1` and `q ≥ 1`, the wired buffered infinite-volume FK measure is FKG. -/
theorem PeriodicGraph.wiredBufferedInfiniteVolume_isFKG
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    IsFKG mu := by
  dsimp only
  intro A B hAmeas hBmeas hAinc hBinc
  apply fkg_measurable_of_isClopen _ _ A B hAmeas hBmeas hAinc hBinc
  intro C D hCcl hDcl hCinc hDinc
  exact P.wiredBufferedInfiniteVolume_fkg_isClopen
    hp hp1 hq hCcl hDcl hCinc hDinc

/-! ## D. Decreasing intersections -/

lemma PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_isClopen
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (A B : Nat -> Set (ConfigSpace (Sym2 V)))
    (hAcl : forall n, IsClopen (A n))
    (hBcl : forall n, IsClopen (B n))
    (hA : forall n, IsIncreasing (A n))
    (hB : forall n, IsIncreasing (B n))
    (hantiA : Antitone A) (hantiB : Antitone B) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (iInter A) * mu.real (iInter B) <=
      mu.real (iInter A ∩ iInter B) := by
  dsimp only
  apply ih_harris_iInter_of_antitone _ A B hantiA hantiB
  · exact fun n => (hAcl n).2.measurableSet
  · exact fun n => (hBcl n).2.measurableSet
  · exact fun n => P.freeBufferedInfiniteVolume_fkg_isClopen
      hp hp1 hq (hAcl n) (hBcl n) (hA n) (hB n)

lemma PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_isClopen
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (A B : Nat -> Set (ConfigSpace (Sym2 V)))
    (hAcl : forall n, IsClopen (A n))
    (hBcl : forall n, IsClopen (B n))
    (hA : forall n, IsIncreasing (A n))
    (hB : forall n, IsIncreasing (B n))
    (hantiA : Antitone A) (hantiB : Antitone B) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (iInter A) * mu.real (iInter B) <=
      mu.real (iInter A ∩ iInter B) := by
  dsimp only
  apply ih_harris_iInter_of_antitone _ A B hantiA hantiB
  · exact fun n => (hAcl n).2.measurableSet
  · exact fun n => (hBcl n).2.measurableSet
  · exact fun n => P.wiredBufferedInfiniteVolume_fkg_isClopen
      hp hp1 hq (hAcl n) (hBcl n) (hA n) (hB n)

lemma PeriodicGraph.wiredBufferedInfiniteVolume_fkg_iInter_cylinder
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (N : Nat -> Nat)
    (A B : (n : Nat) -> Set (ConfigSpace (Sym2 (P.BufferedVertex (N n)))))
    (hA : forall n, IsIncreasing (A n))
    (hB : forall n, IsIncreasing (B n))
    (hantiA : Antitone (fun n => P.bufferedCylinder (N n) (A n)))
    (hantiB : Antitone (fun n => P.bufferedCylinder (N n) (B n))) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (iInter fun n => P.bufferedCylinder (N n) (A n)) *
        mu.real (iInter fun n => P.bufferedCylinder (N n) (B n)) <=
      mu.real ((iInter fun n => P.bufferedCylinder (N n) (A n)) ∩
        (iInter fun n => P.bufferedCylinder (N n) (B n))) := by
  dsimp only
  apply ih_harris_iInter_of_antitone _ _ _ hantiA hantiB
  · exact fun n => P.bufferedCylinder_measurableSet (N n) (A n)
  · exact fun n => P.bufferedCylinder_measurableSet (N n) (B n)
  · intro n
    simpa only [PeriodicGraph.bufferedCylinder, Set.preimage_inter] using
      P.wiredBufferedInfiniteVolume_fkg_cylinder
        (N n) hp hp1 hq (hA n) (hB n)

lemma PeriodicGraph.freeBufferedInfiniteVolume_fkg_iInter_cylinder
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (N : Nat -> Nat)
    (A B : (n : Nat) -> Set (ConfigSpace (Sym2 (P.BufferedVertex (N n)))))
    (hA : forall n, IsIncreasing (A n))
    (hB : forall n, IsIncreasing (B n))
    (hantiA : Antitone (fun n => P.bufferedCylinder (N n) (A n)))
    (hantiB : Antitone (fun n => P.bufferedCylinder (N n) (B n))) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (iInter fun n => P.bufferedCylinder (N n) (A n)) *
        mu.real (iInter fun n => P.bufferedCylinder (N n) (B n)) <=
      mu.real ((iInter fun n => P.bufferedCylinder (N n) (A n)) ∩
        (iInter fun n => P.bufferedCylinder (N n) (B n))) := by
  dsimp only
  apply ih_harris_iInter_of_antitone _ _ _ hantiA hantiB
  · exact fun n => P.bufferedCylinder_measurableSet (N n) (A n)
  · exact fun n => P.bufferedCylinder_measurableSet (N n) (B n)
  · intro n
    simpa only [PeriodicGraph.bufferedCylinder, Set.preimage_inter] using
      P.freeBufferedInfiniteVolume_fkg_cylinder
        (N n) hp hp1 hq (hA n) (hB n)

end StatMech.FK.PeriodicPlanar
