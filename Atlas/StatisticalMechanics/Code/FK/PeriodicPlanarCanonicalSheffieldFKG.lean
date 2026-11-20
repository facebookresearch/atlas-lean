/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarCanonicalFKG
import Code.FK.PeriodicPlanarSheffieldRectanglePreference









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]



def PeriodicGraph.bufferedSetBoundaryEvent
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    Set (ConfigSpace (Sym2 (P.BufferedVertex n))) :=
  {eta | exists x : P.BufferedVertex n, x.1 ∈ S ∧
    exists y : P.BufferedVertex n, P.bufferedBoundary n y ∧
      (FK.openSub (P.bufferedGraph n) eta).Reachable x y}

theorem PeriodicGraph.bufferedSetBoundaryEvent_isIncreasing
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    IsIncreasing (P.bufferedSetBoundaryEvent S n) := by
  intro eta theta hle
  rintro ⟨x, hx, y, hy, hreach⟩
  refine ⟨x, hx, y, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
  simpa [huv.2] using hle s(u, v)

theorem PeriodicGraph.bufferedSetBoundaryCylinder_isClopen
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    IsClopen (P.bufferedCylinder n (P.bufferedSetBoundaryEvent S n)) :=
  P.bufferedCylinder_isClopen n _



theorem PeriodicGraph.bufferedSetBoundaryCylinder_antitone_from
    (P : PeriodicGraph V) (S : Set V) (N : Nat)
    (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
    Antitone (fun k => P.bufferedCylinder (N + k)
      (P.bufferedSetBoundaryEvent S (N + k))) := by
  intro k l hkl omega homega
  by_cases heq : k = l
  · subst l
    exact homega
  have hlevel : N + k < N + l := Nat.add_lt_add_left (lt_of_le_of_ne hkl heq) N
  obtain ⟨x, hxS, y, hybd, hxy⟩ := homega
  have hxsmall : x.1 ∈ P.orbitBox (P.bufferedRadius (N + k)) :=
    P.orbitBox_mono
      (P.bufferedRadius_strictMono.monotone (Nat.le_add_right N k))
      (hS hxS)
  have hfull : (P.openSubgraph omega).Reachable x.1 y.1 :=
    P.bufferedReachable_full (N + l) omega hxy
  have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius (N + k)) :=
    P.bufferedBoundary_not_mem_of_lt hlevel y hybd
  obtain ⟨z, hzbd, hxz⟩ :=
    P.bufferedBoundary_reachable_of_reachable_outside (N + k) omega
      hxsmall hyout hfull
  exact ⟨⟨x.1, hxsmall⟩, hxS, z, hzbd, hxz⟩



theorem PeriodicGraph.iInter_bufferedSetBoundaryCylinder
    (P : PeriodicGraph V) (S : Set V) (hSfinite : S.Finite)
    (N : Nat) (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
    (iInter fun k => P.bufferedCylinder (N + k)
      (P.bufferedSetBoundaryEvent S (N + k))) = P.setHitsInfinite S := by
  classical
  ext omega
  simp only [Set.mem_iInter, PeriodicGraph.bufferedCylinder,
    Set.mem_preimage, PeriodicGraph.bufferedSetBoundaryEvent,
    PeriodicGraph.setHitsInfinite, Set.mem_setOf_eq]
  constructor
  · intro hall
    by_contra hnot
    push Not at hnot
    let U : Set V := ⋃ x ∈ S, P.cluster omega x
    have hUfinite : U.Finite := by
      exact Set.Finite.biUnion hSfinite fun x hx => hnot x hx
    obtain ⟨M, hM⟩ := P.finite_subset_orbitBox hUfinite.toFinset
    obtain ⟨x, hxS, y, hybd, hxy⟩ := hall (M + 1)
    have hfull : (P.openSubgraph omega).Reachable x.1 y.1 :=
      P.bufferedReachable_full (N + (M + 1)) omega hxy
    have hyU : y.1 ∈ U := by
      exact Set.mem_iUnion.2 ⟨x.1, Set.mem_iUnion.2 ⟨hxS, hfull⟩⟩
    have hyM : y.1 ∈ P.orbitBox M := hM y.1 (by simpa using hyU)
    have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius M) :=
      P.bufferedBoundary_not_mem_of_lt (by omega : M < N + (M + 1)) y hybd
    exact hyout (P.orbitBox_mono (P.id_le_bufferedRadius M) hyM)
  · rintro ⟨x, hxS, hxinf⟩ k
    have hxlevel : x ∈ P.orbitBox (P.bufferedRadius (N + k)) :=
      P.orbitBox_mono
        (P.bufferedRadius_strictMono.monotone (Nat.le_add_right N k))
        (hS hxS)
    have hout : ¬P.cluster omega x ⊆
        (P.orbitBox (P.bufferedRadius (N + k)) : Set V) := by
      intro hsub
      exact hxinf ((P.orbitBox (P.bufferedRadius (N + k))).finite_toSet.subset hsub)
    obtain ⟨z, hzcluster, hzout⟩ := Set.not_subset.mp hout
    obtain ⟨y, hybd, hxy⟩ :=
      P.bufferedBoundary_reachable_of_reachable_outside (N + k) omega
        hxlevel hzout hzcluster
    exact ⟨⟨x, hxlevel⟩, hxS, y, hybd, hxy⟩



theorem PeriodicGraph.freeBufferedInfiniteVolume_fkg_setHitsInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.setHitsInfinite (S : Set V)) *
        mu.real (P.setHitsInfinite (T : Set V)) <=
      mu.real (P.setHitsInfinite (S : Set V) ∩
        P.setHitsInfinite (T : Set V)) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (S : Set V) (N + k))
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (T : Set V) (N + k))
  have hfkg := P.freeBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (S : Set V) (N + k))
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (T : Set V) (N + k))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (S : Set V) (N + k)))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (T : Set V) (N + k)))
    (P.bufferedSetBoundaryCylinder_antitone_from (S : Set V) N hS)
    (P.bufferedSetBoundaryCylinder_antitone_from (T : Set V) N hT)
  rw [show iInter A = P.setHitsInfinite (S : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (S : Set V) S.finite_toSet N hS,
      show iInter B = P.setHitsInfinite (T : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (T : Set V) T.finite_toSet N hT] at hfkg
  exact hfkg



theorem PeriodicGraph.wiredBufferedInfiniteVolume_fkg_setHitsInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.setHitsInfinite (S : Set V)) *
        mu.real (P.setHitsInfinite (T : Set V)) <=
      mu.real (P.setHitsInfinite (S : Set V) ∩
        P.setHitsInfinite (T : Set V)) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (S : Set V) (N + k))
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (T : Set V) (N + k))
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (S : Set V) (N + k))
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (T : Set V) (N + k))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (S : Set V) (N + k)))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (T : Set V) (N + k)))
    (P.bufferedSetBoundaryCylinder_antitone_from (S : Set V) N hS)
    (P.bufferedSetBoundaryCylinder_antitone_from (T : Set V) N hT)
  rw [show iInter A = P.setHitsInfinite (S : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (S : Set V) S.finite_toSet N hS,
      show iInter B = P.setHitsInfinite (T : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (T : Set V) T.finite_toSet N hT] at hfkg
  exact hfkg



def PeriodicGraph.finiteWitnessInfiniteEvent
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ (S : Set V), Q x ∩ {omega | (P.cluster omega x).Infinite}



def PeriodicGraph.finiteWitnessBoundaryApprox
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ (S : Set V), Q x ∩
    P.bufferedCylinder n (P.bufferedSetBoundaryEvent ({x} : Set V) n)

theorem PeriodicGraph.finiteWitnessBoundaryApprox_isClopen
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V)))
    (hQ : ∀ x ∈ S, IsClopen (Q x)) (n : Nat) :
    IsClopen (P.finiteWitnessBoundaryApprox S Q n) := by
  unfold PeriodicGraph.finiteWitnessBoundaryApprox
  apply Set.Finite.isClopen_biUnion S.finite_toSet
  intro x hx
  exact (hQ x hx).inter
    (P.bufferedSetBoundaryCylinder_isClopen ({x} : Set V) n)

theorem PeriodicGraph.finiteWitnessBoundaryApprox_isIncreasing
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V)))
    (hQ : ∀ x ∈ S, IsIncreasing (Q x)) (n : Nat) :
    IsIncreasing (P.finiteWitnessBoundaryApprox S Q n) := by
  intro omega eta home
  simp only [PeriodicGraph.finiteWitnessBoundaryApprox, Set.mem_iUnion,
    Set.mem_inter_iff]
  rintro ⟨x, hx, hQx, hboundary⟩
  exact ⟨x, hx, hQ x hx home hQx,
    P.bufferedCylinder_isIncreasing n
      (P.bufferedSetBoundaryEvent_isIncreasing ({x} : Set V) n)
      home hboundary⟩

theorem PeriodicGraph.finiteWitnessBoundaryApprox_antitone_from
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (N : Nat)
    (hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V)) :
    Antitone (fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) := by
  intro k l hkl omega
  simp only [PeriodicGraph.finiteWitnessBoundaryApprox, Set.mem_iUnion,
    Set.mem_inter_iff]
  rintro ⟨x, hx, hQx, hboundary⟩
  have hxsub : ({x} : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ hS hx
  exact ⟨x, hx, hQx,
    P.bufferedSetBoundaryCylinder_antitone_from ({x} : Set V) N hxsub
      hkl hboundary⟩



theorem PeriodicGraph.iInter_finiteWitnessBoundaryApprox
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (N : Nat)
    (hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V)) :
    (iInter fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) =
      P.finiteWitnessInfiniteEvent S Q := by
  classical
  ext omega
  simp only [Set.mem_iInter, PeriodicGraph.finiteWitnessBoundaryApprox,
    PeriodicGraph.finiteWitnessInfiniteEvent, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro hall
    by_contra hnot
    push Not at hnot
    let eligible : Set V := {x | x ∈ (S : Set V) ∧ omega ∈ Q x}
    have heligible : eligible.Finite := S.finite_toSet.subset fun x hx => hx.1
    let U : Set V := ⋃ x ∈ eligible, P.cluster omega x
    have hUfinite : U.Finite := by
      apply Set.Finite.biUnion heligible
      intro x hx
      exact hnot x hx.1 hx.2
    obtain ⟨M, hM⟩ := P.finite_subset_orbitBox hUfinite.toFinset
    obtain ⟨x, hxS, hxQ, xSource, hxSource, y, hybd, hxy⟩ :=
      hall (M + 1)
    have hxx : xSource.1 = x := by simpa using hxSource
    have hfull : (P.openSubgraph omega).Reachable x y.1 := by
      simpa only [hxx] using
        P.bufferedReachable_full (N + (M + 1)) omega hxy
    have hyU : y.1 ∈ U := by
      exact Set.mem_iUnion.2 ⟨x,
        Set.mem_iUnion.2 ⟨⟨hxS, hxQ⟩, hfull⟩⟩
    have hyM : y.1 ∈ P.orbitBox M := hM y.1 (by simpa using hyU)
    have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius M) :=
      P.bufferedBoundary_not_mem_of_lt (by omega : M < N + (M + 1)) y hybd
    exact hyout (P.orbitBox_mono (P.id_le_bufferedRadius M) hyM)
  · rintro ⟨x, hxS, hxQ, hxinf⟩ k
    have hxlevel : x ∈ P.orbitBox (P.bufferedRadius (N + k)) :=
      P.orbitBox_mono
        (P.bufferedRadius_strictMono.monotone (Nat.le_add_right N k))
        (hS hxS)
    have hout : ¬P.cluster omega x ⊆
        (P.orbitBox (P.bufferedRadius (N + k)) : Set V) := by
      intro hsub
      exact hxinf ((P.orbitBox (P.bufferedRadius (N + k))).finite_toSet.subset hsub)
    obtain ⟨z, hzcluster, hzout⟩ := Set.not_subset.mp hout
    obtain ⟨y, hybd, hxy⟩ :=
      P.bufferedBoundary_reachable_of_reachable_outside (N + k) omega
        hxlevel hzout hzcluster
    exact ⟨x, hxS, hxQ, ⟨x, hxlevel⟩, rfl, y, hybd, hxy⟩



theorem PeriodicGraph.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V)
    (Q R : V -> Set (ConfigSpace (Sym2 V)))
    (hQcl : ∀ x ∈ S, IsClopen (Q x))
    (hRcl : ∀ x ∈ T, IsClopen (R x))
    (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
    (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.finiteWitnessInfiniteEvent S Q) *
        mu.real (P.finiteWitnessInfiniteEvent T R) <=
      mu.real (P.finiteWitnessInfiniteEvent S Q ∩
        P.finiteWitnessInfiniteEvent T R) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox S Q (N + k)
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox T R (N + k)
  have hfkg := P.freeBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.finiteWitnessBoundaryApprox_isClopen S Q hQcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isClopen T R hRcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing S Q hQinc (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing T R hRinc (N + k))
    (P.finiteWitnessBoundaryApprox_antitone_from S Q N hS)
    (P.finiteWitnessBoundaryApprox_antitone_from T R N hT)
  rw [show iInter A = P.finiteWitnessInfiniteEvent S Q by
        exact P.iInter_finiteWitnessBoundaryApprox S Q N hS,
      show iInter B = P.finiteWitnessInfiniteEvent T R by
        exact P.iInter_finiteWitnessBoundaryApprox T R N hT] at hfkg
  exact hfkg



theorem PeriodicGraph.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V)
    (Q R : V -> Set (ConfigSpace (Sym2 V)))
    (hQcl : ∀ x ∈ S, IsClopen (Q x))
    (hRcl : ∀ x ∈ T, IsClopen (R x))
    (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
    (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.finiteWitnessInfiniteEvent S Q) *
        mu.real (P.finiteWitnessInfiniteEvent T R) <=
      mu.real (P.finiteWitnessInfiniteEvent S Q ∩
        P.finiteWitnessInfiniteEvent T R) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox S Q (N + k)
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox T R (N + k)
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.finiteWitnessBoundaryApprox_isClopen S Q hQcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isClopen T R hRcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing S Q hQinc (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing T R hRinc (N + k))
    (P.finiteWitnessBoundaryApprox_antitone_from S Q N hS)
    (P.finiteWitnessBoundaryApprox_antitone_from T R N hT)
  rw [show iInter A = P.finiteWitnessInfiniteEvent S Q by
        exact P.iInter_finiteWitnessBoundaryApprox S Q N hS,
      show iInter B = P.finiteWitnessInfiniteEvent T R by
        exact P.iInter_finiteWitnessBoundaryApprox T R N hT] at hfkg
  exact hfkg





def PeriodicPlaneEmbedding.finiteRectTargetConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    Set (ConfigSpace (Sym2 (E.RectVertex a b c d))) :=
  {eta | ∃ x' y : E.RectVertex a b c d, x'.1 = x ∧ y.1 ∈ T ∧
    (FK.openSub (E.rectGraph a b c d) eta).Reachable x' y}


def PeriodicPlaneEmbedding.rectTargetConnectionEvent
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectRestrict a b c d ⁻¹'
    E.finiteRectTargetConnection a b c d x T

theorem PeriodicPlaneEmbedding.finiteRectTargetConnection_isIncreasing
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsIncreasing (E.finiteRectTargetConnection a b c d x T) := by
  intro eta theta hle
  rintro ⟨x', y, hxx, hy, hreach⟩
  refine ⟨x', y, hxx, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨huv.1, Bool.eq_true_of_true_le (by simpa [huv.2] using hle s(u, v))⟩

theorem PeriodicPlaneEmbedding.rectTargetConnectionEvent_isClopen
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsClopen (E.rectTargetConnectionEvent a b c d x T) :=
  IsClopen.preimage (isClopen_discrete _)
    (E.continuous_rectRestrict a b c d)

theorem PeriodicPlaneEmbedding.rectTargetConnectionEvent_isIncreasing
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V) :
    IsIncreasing (E.rectTargetConnectionEvent a b c d x T) := by
  intro omega eta hle homega
  exact E.finiteRectTargetConnection_isIncreasing a b c d x T
    (E.rectRestrict_mono a b c d hle) homega



theorem PeriodicPlaneEmbedding.mem_rectTargetConnectionEvent_iff
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (x : V) (T : Set V)
    (omega : ConfigSpace (Sym2 V)) :
    omega ∈ E.rectTargetConnectionEvent a b c d x T ↔
      ∃ y ∈ T, omega ∈
        P.connectedWithinSet (E.rectVertices a b c d) x y := by
  constructor
  · rintro ⟨x', y, hxx, hy, hreach⟩
    subst x
    rw [E.openSub_rectRestrict_eq_induce] at hreach
    obtain ⟨p⟩ := hreach
    let inclusion :
        (P.openSubgraph omega).induce (E.rectVertices a b c d) →g
          P.openSubgraph omega :=
      { toFun := Subtype.val
        map_rel' := fun huv => huv }
    let q := p.map inclusion
    have hq : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
      intro v hv
      dsimp only [q] at hv
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      subst v
      exact u.2
    refine ⟨y.1, hy, ?_⟩
    simpa only [inclusion] using P.mem_connectedWithinSet_of_walk q hq
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨q, hq⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
    have hx : x ∈ E.rectVertices a b c d := hq x q.start_mem_support
    have hyRect : y ∈ E.rectVertices a b c d := hq y q.end_mem_support
    have hreach :
        (FK.openSub (E.rectGraph a b c d)
          (E.rectRestrict a b c d omega)).Reachable
            ⟨x, hx⟩ ⟨y, hyRect⟩ := by
      rw [E.openSub_rectRestrict_eq_induce]
      exact ⟨q.induce (E.rectVertices a b c d) hq⟩
    exact ⟨⟨x, hx⟩, ⟨y, hyRect⟩, rfl, hy, hreach⟩



theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_eq_finiteWitnessInfinite
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (a b c d : Real) (S : Finset V) (T : Set V) :
    E.rectSideConnectionEvent a b c d (S : Set V) T =
      P.finiteWitnessInfiniteEvent S
        (fun x => E.rectTargetConnectionEvent a b c d x T) := by
  ext omega
  constructor
  · rintro ⟨x, hx, hxinf, y, hy, hxy⟩
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx,
      ⟨(E.mem_rectTargetConnectionEvent_iff a b c d x T omega).2
        ⟨y, hy, hxy⟩, hxinf⟩⟩⟩
  · simp only [PeriodicGraph.finiteWitnessInfiniteEvent, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    rintro ⟨x, hx, hxT, hxinf⟩
    obtain ⟨y, hy, hxy⟩ :=
      (E.mem_rectTargetConnectionEvent_iff a b c d x T omega).1 hxT
    exact ⟨x, hx, hxinf, y, hy, hxy⟩



theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_fkg_rectSideConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b c d : Real)
    (S T : Finset V) (sideS sideT : Set V) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) *
        mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <=
      mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩
        E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
  let Q := fun x => E.rectTargetConnectionEvent a b c d x sideS
  let R := fun x => E.rectTargetConnectionEvent a b c d x sideT
  have hfkg := P.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    hp hp1 hq S T Q R
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideT)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideT)
  rw [← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d S sideS,
      ← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d T sideT] at hfkg
  exact hfkg



theorem PeriodicPlaneEmbedding.wiredBufferedInfiniteVolume_fkg_rectSideConnection
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (a b c d : Real)
    (S T : Finset V) (sideS sideT : Set V) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS) *
        mu.real (E.rectSideConnectionEvent a b c d (T : Set V) sideT) <=
      mu.real (E.rectSideConnectionEvent a b c d (S : Set V) sideS ∩
        E.rectSideConnectionEvent a b c d (T : Set V) sideT) := by
  let Q := fun x => E.rectTargetConnectionEvent a b c d x sideS
  let R := fun x => E.rectTargetConnectionEvent a b c d x sideT
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    hp hp1 hq S T Q R
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isClopen a b c d x sideT)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideS)
    (fun x _ => E.rectTargetConnectionEvent_isIncreasing a b c d x sideT)
  rw [← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d S sideS,
      ← E.rectSideConnectionEvent_eq_finiteWitnessInfinite
        a b c d T sideT] at hfkg
  exact hfkg

end StatMech.FK.PeriodicPlanar
