/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarBurtonKeanePattern

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type} [Countable V] [DecidableEq V]

def PeriodicGraph.threeDistinctInfiniteEvent (P : PeriodicGraph V)
    (x : Fin 3 → V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | (∀ i, (P.cluster omega (x i)).Infinite) ∧
    ∀ i j, i ≠ j → P.cluster omega (x i) ≠ P.cluster omega (x j)}

theorem PeriodicGraph.numInfiniteClusters_top_subset_threeDistinct
    (P : PeriodicGraph V) :
    {omega | P.numInfiniteClusters omega = ⊤} ⊆
      ⋃ x : Fin 3 → V, P.threeDistinctInfiniteEvent x := by
  classical
  intro omega htop
  have hrepInf : (P.infiniteClusterRepSet omega).Infinite := by
    rw [← Set.encard_eq_top_iff, ← P.numInfiniteClusters_eq_repSet_encard]
    exact htop
  obtain ⟨a, ha⟩ := hrepInf.nonempty
  obtain ⟨b, hb, hbnot⟩ := hrepInf.exists_notMem_finset {a}
  obtain ⟨c, hc, hcnot⟩ := hrepInf.exists_notMem_finset {a, b}
  have hba : b ≠ a := by simpa using hbnot
  have hcne : c ≠ a ∧ c ≠ b := by simpa using hcnot
  have hca : c ≠ a := hcne.1
  have hcb : c ≠ b := hcne.2
  have hab : a ≠ b := Ne.symm hba
  have hac : a ≠ c := Ne.symm hca
  have hbc : b ≠ c := Ne.symm hcb
  let x : Fin 3 → V := ![a, b, c]
  have hxrep : ∀ i, x i ∈ P.infiniteClusterRepSet omega := by
    intro i
    fin_cases i <;> assumption
  have hxinj : Function.Injective x := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [x, hab, hac, hbc, hba, hca, hcb]
  apply Set.mem_iUnion.mpr
  refine ⟨x, ?_, ?_⟩
  · exact fun i => (hxrep i).1
  · intro i j hij hcluster
    exact hij (hxinj (P.injOn_cluster_infiniteClusterRepSet omega
      (hxrep i) (hxrep j) hcluster))

private theorem exists_pos_of_countable_cover
    {Omega A : Type*} [MeasurableSpace Omega] [Countable A]
    (mu : Measure Omega) (S : Set Omega) (B : A → Set Omega)
    (hsub : S ⊆ ⋃ a, B a) (hpos : 0 < mu S) :
    ∃ a, 0 < mu (B a) := by
  by_contra h
  push Not at h
  have hz : ∀ a, mu (B a) = 0 := fun a => le_antisymm (h a) bot_le
  have hu : mu (⋃ a, B a) = 0 := measure_iUnion_null hz
  have hle : mu S ≤ mu (⋃ a, B a) := measure_mono hsub
  rw [hu] at hle
  exact (not_lt_of_ge hle) hpos

theorem PeriodicGraph.exists_threeDistinctInfinite_pos_of_top
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (htop : 0 < mu {omega | P.numInfiniteClusters omega = ⊤}) :
    ∃ x : Fin 3 → V, 0 < mu (P.threeDistinctInfiniteEvent x) :=
  exists_pos_of_countable_cover mu _ _
    P.numInfiniteClusters_top_subset_threeDistinct htop

theorem PeriodicGraph.threeDistinct_subset_pattern_trifurcations
    (P : PeriodicGraph V) (hconn : P.graph.Connected) (x : Fin 3 → V) :
    P.threeDistinctInfiniteEvent x ⊆
      ⋃ I : Finset (Sym2 V), ⋃ eta : ConfigSpace ↥I, ⋃ hub : V,
        setPattern I eta ⁻¹' {omega | P.IsTrifurcation omega hub} := by
  intro omega homega
  obtain ⟨I, eta, hub, htrif⟩ :=
    P.three_clusters_pattern_trifurcation hconn omega x homega.1 homega.2
  exact Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr ⟨eta,
    Set.mem_iUnion.mpr ⟨hub, htrif⟩⟩⟩

theorem PeriodicGraph.exists_trifurcation_pos_of_top
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | P.numInfiniteClusters omega = ⊤}) :
    ∃ hub : V, 0 < mu {omega | P.IsTrifurcation omega hub} := by
  classical
  obtain ⟨x, hxpos⟩ := P.exists_threeDistinctInfinite_pos_of_top mu htop
  have hcover := P.threeDistinct_subset_pattern_trifurcations hconn x
  obtain ⟨I, hI⟩ := exists_pos_of_countable_cover mu _ _ hcover hxpos
  obtain ⟨eta, heta⟩ := exists_pos_of_countable_cover mu _ _
    (fun _ h => h) hI
  obtain ⟨hub, hpre⟩ := exists_pos_of_countable_cover mu _ _
    (fun _ h => h) heta
  refine ⟨hub, ?_⟩
  by_contra hnot
  have hzero : mu {omega | P.IsTrifurcation omega hub} = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  have hmapzero := hpattern I eta hzero
  rw [Measure.map_apply (measurable_setPattern I eta)
    (P.measurableSet_isTrifurcation hub)] at hmapzero
  exact (ne_of_gt hpre) hmapzero



theorem PeriodicPlaneEmbedding.numInfiniteClusters_top_measure_zero
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu) :
    mu {omega | P.numInfiniteClusters omega = ⊤} = 0 := by
  by_contra hne
  have htop : 0 < mu {omega | P.numInfiniteClusters omega = ⊤} :=
    pos_iff_ne_zero.mpr hne
  obtain ⟨hub, hhub⟩ := P.exists_trifurcation_pos_of_top hconn mu hpattern htop
  obtain ⟨z, u, hu, hzu⟩ := P.covers hub
  have hzero : mu {omega | P.IsTrifurcation omega hub} = 0 := by
    rw [← hzu, P.trifurcation_measure_eq_orbit mu hTI z u]
    exact E.trifurcation_measure_eq_zero mu hTI u hu
  rw [hzero] at hhub
  exact (lt_irrefl 0) hhub



theorem PeriodicPlaneEmbedding.numInfiniteClusters_zero_or_one
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu) (hfe : HasFiniteEnergy mu)
    (hpattern : ∀ (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I),
      mu.map (setPattern I eta) ≪ mu) :
    ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧
      (k = 0 ∨ k = 1) := by
  obtain ⟨k, hk, hkcases⟩ := P.numInfiniteClusters_zero_one_or_top hconn mu herg hfe
  refine ⟨k, hk, ?_⟩
  rcases hkcases with hzero | hone | htop
  · exact Or.inl hzero
  · exact Or.inr hone
  · have htop0 := E.numInfiniteClusters_top_measure_zero hconn mu herg.1 hpattern
    rw [← htop, hk] at htop0
    exact False.elim (one_ne_zero htop0)


theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_numInfiniteClusters_zero_or_one
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (hconn : P.graph.Connected) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ∃ k : ℕ∞,
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | P.numInfiniteClusters omega = k} = 1 ∧
      (k = 0 ∨ k = 1) := by
  exact E.numInfiniteClusters_zero_or_one hconn _
    (E.freeBufferedInfiniteVolume_isErgodic hp hp1 hq)
    (P.freeBufferedInfiniteVolume_hasFiniteEnergy hp hp1 hq)
    (P.freeBufferedInfiniteVolume_setPattern_absolutelyContinuous hp hp1 hq)

end StatMech.FK.PeriodicPlanar
