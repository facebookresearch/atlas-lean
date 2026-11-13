/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FK.PeriodicPlanarCanonicalFiniteEnergy

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

noncomputable def periodicVertexIndex (V : Type*) [Countable V] : V -> Nat :=
  (Countable.exists_injective_nat V).choose

theorem periodicVertexIndex_injective :
    Function.Injective (periodicVertexIndex V) :=
  (Countable.exists_injective_nat V).choose_spec

theorem PeriodicGraph.self_mem_cluster (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (x : V) : x ∈ P.cluster omega x :=
  by
    change (P.openSubgraph omega).Reachable x x
    exact SimpleGraph.Reachable.refl x

theorem PeriodicGraph.cluster_eq_of_reachable (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : (P.openSubgraph omega).Reachable x y) :
    P.cluster omega x = P.cluster omega y := by
  ext z
  constructor
  · intro hxz
    exact hxy.symm.trans hxz
  · intro hyz
    exact hxy.trans hyz


def PeriodicGraph.infiniteClusters (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = P.cluster omega x}


noncomputable def PeriodicGraph.numInfiniteClusters (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : ℕ∞ :=
  (P.infiniteClusters omega).encard

theorem PeriodicGraph.infiniteClusters_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.infiniteClusters (P.configTranslate z omega) =
      (fun C : Set V => P.shift z '' C) '' P.infiniteClusters omega := by
  ext C
  simp only [PeriodicGraph.infiniteClusters, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hinf, x, rfl⟩
    refine ⟨P.cluster omega (P.shift (-z) x), ⟨?_, _, rfl⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega
        (P.shift (-z) x)).mp (by simpa using hinf)
    · simpa using (P.cluster_configTranslate z omega (P.shift (-z) x)).symm
  · rintro ⟨C, ⟨hinf, x, rfl⟩, rfl⟩
    exact ⟨(Set.infinite_image_iff
      (Set.injOn_of_injective (P.shift z).injective)).2 hinf,
      P.shift z x, (P.cluster_configTranslate z omega x).symm⟩

theorem PeriodicGraph.numInfiniteClusters_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.numInfiniteClusters (P.configTranslate z omega) =
      P.numInfiniteClusters omega := by
  unfold PeriodicGraph.numInfiniteClusters
  rw [P.infiniteClusters_configTranslate]
  exact Set.InjOn.encard_image
    (Set.injOn_of_injective
      (Set.image_injective.mpr (P.shift z).injective))



def PeriodicGraph.infiniteClusterRepSet (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : Set V :=
  {x | (P.cluster omega x).Infinite ∧
    ∀ y, (P.openSubgraph omega).Reachable x y ->
      periodicVertexIndex V x <= periodicVertexIndex V y}

theorem exists_periodicVertexIndex_min (S : Set V) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S,
      periodicVertexIndex V x <= periodicVertexIndex V y := by
  obtain ⟨x0, hx0⟩ := hne
  have hmem : sInf (periodicVertexIndex V '' S) ∈
      periodicVertexIndex V '' S :=
    Nat.sInf_mem ⟨periodicVertexIndex V x0, x0, hx0, rfl⟩
  obtain ⟨x, hx, hxmin⟩ := hmem
  exact ⟨x, hx, fun y hy => hxmin ▸ Nat.sInf_le ⟨y, hy, rfl⟩⟩

theorem PeriodicGraph.image_cluster_infiniteClusterRepSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) :
    (fun x => P.cluster omega x) '' P.infiniteClusterRepSet omega =
      P.infiniteClusters omega := by
  ext C
  simp only [Set.mem_image, PeriodicGraph.infiniteClusterRepSet,
    Set.mem_setOf_eq, PeriodicGraph.infiniteClusters]
  constructor
  · rintro ⟨x, ⟨hinf, _⟩, rfl⟩
    exact ⟨hinf, x, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨y, hy, hymin⟩ :=
      exists_periodicVertexIndex_min (P.cluster omega x)
        ⟨x, P.self_mem_cluster omega x⟩
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · have heq := P.cluster_eq_of_reachable omega hy
      exact heq ▸ hinf
    · intro z hyz
      exact hymin z (hy.trans hyz)
    · exact (P.cluster_eq_of_reachable omega hy).symm

theorem PeriodicGraph.injOn_cluster_infiniteClusterRepSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) :
    Set.InjOn (fun x => P.cluster omega x) (P.infiniteClusterRepSet omega) := by
  intro x hx y hy hclusters
  change P.cluster omega x = P.cluster omega y at hclusters
  have hxy : (P.openSubgraph omega).Reachable x y := by
    have : y ∈ P.cluster omega x := by
      rw [hclusters]
      exact P.self_mem_cluster omega y
    exact this
  exact periodicVertexIndex_injective
    (le_antisymm (hx.2 y hxy) (hy.2 x hxy.symm))

theorem PeriodicGraph.numInfiniteClusters_eq_repSet_encard
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) :
    P.numInfiniteClusters omega = (P.infiniteClusterRepSet omega).encard := by
  unfold PeriodicGraph.numInfiniteClusters
  rw [← P.image_cluster_infiniteClusterRepSet omega,
    Set.InjOn.encard_image (P.injOn_cluster_infiniteClusterRepSet omega)]

theorem PeriodicGraph.measurableSet_infiniteClusterRepSet
    (P : PeriodicGraph V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      x ∈ P.infiniteClusterRepSet omega} := by
  let Lower : Set V :=
    {y | periodicVertexIndex V y < periodicVertexIndex V x}
  have hminimal : MeasurableSet {omega : ConfigSpace (Sym2 V) |
      ∀ y, (P.openSubgraph omega).Reachable x y ->
        periodicVertexIndex V x <= periodicVertexIndex V y} := by
    have heq : {omega : ConfigSpace (Sym2 V) |
          ∀ y, (P.openSubgraph omega).Reachable x y ->
            periodicVertexIndex V x <= periodicVertexIndex V y} =
        ⋂ y ∈ Lower, (P.twoPointEvent x y)ᶜ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff,
        Lower, Set.mem_setOf_eq, PeriodicGraph.twoPointEvent]
      constructor
      · intro h y hy hxy
        exact (not_lt_of_ge (h y hxy)) hy
      · intro h y hxy
        by_contra hle
        exact h y (lt_of_not_ge hle) hxy
    rw [heq]
    exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
      (P.measurableSet_twoPointEvent x y).compl
  have heq : {omega : ConfigSpace (Sym2 V) |
        x ∈ P.infiniteClusterRepSet omega} =
      {omega | (P.cluster omega x).Infinite} ∩
        {omega | ∀ y, (P.openSubgraph omega).Reachable x y ->
          periodicVertexIndex V x <= periodicVertexIndex V y} := by
    ext omega
    rfl
  rw [heq]
  exact (P.measurableSet_cluster_infinite x).inter hminimal

private theorem measurable_encard_setOf_periodic
    {Omega A : Type*} [MeasurableSpace Omega] [Countable A]
    (p : Omega -> A -> Prop) (hp : ∀ a, Measurable (fun omega => p omega a)) :
    Measurable (fun omega => Set.encard {a | p omega a}) := by
  have hpi : Measurable (fun omega => fun a => p omega a) := by
    rw [measurable_pi_iff]
    exact hp
  exact measurable_encard.comp (measurable_setOf.comp hpi)

theorem PeriodicGraph.measurable_numInfiniteClusters (P : PeriodicGraph V) :
    Measurable P.numInfiniteClusters := by
  have heq : P.numInfiniteClusters = fun omega =>
      Set.encard {x : V | x ∈ P.infiniteClusterRepSet omega} := by
    funext omega
    exact P.numInfiniteClusters_eq_repSet_encard omega
  rw [heq]
  apply measurable_encard_setOf_periodic
  intro x
  exact measurable_mem.mpr (P.measurableSet_infiniteClusterRepSet x)



theorem PeriodicGraph.numInfiniteClusters_eq_one_iff_hasUnique
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) :
    P.numInfiniteClusters omega = 1 ↔ P.HasUniqueInfiniteCluster omega := by
  constructor
  · intro hone
    have hset : ∃ C : Set V, P.infiniteClusters omega = {C} := by
      rw [PeriodicGraph.numInfiniteClusters, Set.encard_eq_one] at hone
      exact hone
    obtain ⟨C, hC⟩ := hset
    have hCmem : C ∈ P.infiniteClusters omega := by rw [hC]; simp
    obtain ⟨hCinf, x, hxC⟩ := hCmem
    refine ⟨⟨x, hxC ▸ hCinf⟩, ?_⟩
    intro y z hy hz
    have hyC : P.cluster omega y = C := by
      have : P.cluster omega y ∈ P.infiniteClusters omega := ⟨hy, y, rfl⟩
      rw [hC] at this
      simpa using this
    have hzC : P.cluster omega z = C := by
      have : P.cluster omega z ∈ P.infiniteClusters omega := ⟨hz, z, rfl⟩
      rw [hC] at this
      simpa using this
    have hzmem : z ∈ P.cluster omega y := by
      rw [hyC, ← hzC]
      exact P.self_mem_cluster omega z
    exact hzmem
  · rintro ⟨⟨x, hx⟩, hunique⟩
    have hset : P.infiniteClusters omega = {P.cluster omega x} := by
      ext C
      constructor
      · rintro ⟨hCinf, y, rfl⟩
        have hxy := hunique x y hx hCinf
        simpa using (P.cluster_eq_of_reachable omega hxy).symm
      · intro hC
        have heq : C = P.cluster omega x := by simpa using hC
        exact heq ▸ ⟨hx, x, rfl⟩
    unfold PeriodicGraph.numInfiniteClusters
    rw [hset, Set.encard_singleton]

theorem PeriodicGraph.numInfiniteClusters_eq_one_event
    (P : PeriodicGraph V) :
    {omega : ConfigSpace (Sym2 V) | P.numInfiniteClusters omega = 1} =
      {omega | P.HasUniqueInfiniteCluster omega} := by
  ext omega
  exact P.numInfiniteClusters_eq_one_iff_hasUnique omega



theorem PeriodicGraph.numInfiniteClusters_ae_const
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (herg : P.IsErgodic mu) :
    ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 := by
  classical
  have hmeas : ∀ k : ℕ∞, MeasurableSet
      {omega | P.numInfiniteClusters omega = k} := fun k =>
    P.measurable_numInfiniteClusters (measurableSet_singleton k)
  have hinv : ∀ k : ℕ∞, ∀ z : Site 2,
      P.configTranslate z ⁻¹' {omega | P.numInfiniteClusters omega = k} =
        {omega | P.numInfiniteClusters omega = k} := by
    intro k z
    ext omega
    simp only [Set.mem_preimage, Set.mem_setOf_eq,
      P.numInfiniteClusters_configTranslate]
  have hdich : ∀ k : ℕ∞,
      mu {omega | P.numInfiniteClusters omega = k} = 0 ∨
        mu {omega | P.numInfiniteClusters omega = k} = 1 := fun k =>
    herg.2 _ (hmeas k) (hinv k)
  by_contra h
  push Not at h
  have hall0 : ∀ k : ℕ∞,
      mu {omega | P.numInfiniteClusters omega = k} = 0 := by
    intro k
    rcases hdich k with hk | hk
    · exact hk
    · exact False.elim (h k hk)
  have huniv : (Set.univ : Set (ConfigSpace (Sym2 V))) =
      ⋃ k : ℕ∞, {omega | P.numInfiniteClusters omega = k} := by
    ext omega
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨P.numInfiniteClusters omega, rfl⟩
  have : mu (Set.univ : Set (ConfigSpace (Sym2 V))) = 0 := by
    rw [huniv]
    exact measure_iUnion_null hall0
  rw [measure_univ] at this
  exact one_ne_zero this

end StatMech.FK.PeriodicPlanar
