/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FK.PeriodicPlanarBurtonKeaneCore

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]

@[simp] theorem forceOpenFinset_of_mem {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ F) (omega : ConfigSpace (Sym2 V)) :
    forceOpenFinset F omega e = true := by
  simp [forceOpenFinset, he]

@[simp] theorem forceOpenFinset_of_notMem {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∉ F) (omega : ConfigSpace (Sym2 V)) :
    forceOpenFinset F omega e = omega e := by
  simp [forceOpenFinset, he]

theorem forceOpenFinset_le (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) : omega <= forceOpenFinset F omega := by
  intro e
  by_cases he : e ∈ F <;> simp [forceOpenFinset, he]

omit [Countable V] in
theorem PeriodicGraph.openSubgraph_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) :
    P.openSubgraph omega <= P.openSubgraph eta := by
  intro x y hxy
  rw [P.openSubgraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have he := h s(x, y)
  rw [hxy.2] at he
  exact le_antisymm (by simp) he

omit [Countable V] in
theorem PeriodicGraph.reachable_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) {x y : V}
    (hxy : (P.openSubgraph omega).Reachable x y) :
    (P.openSubgraph eta).Reachable x y :=
  hxy.mono (P.openSubgraph_mono h)

omit [Countable V] in
theorem PeriodicGraph.cluster_mono (P : PeriodicGraph V)
    {omega eta : ConfigSpace (Sym2 V)} (h : omega <= eta) (x : V) :
    P.cluster omega x ⊆ P.cluster eta x := fun _ hxy => P.reachable_mono h hxy

theorem encard_image_lt_of_not_injOn_periodic
    {A B : Type*} {s : Set A} {f : A -> B}
    (hfin : s.Finite) (hni : ¬ Set.InjOn f s) :
    (f '' s).encard < s.encard := by
  rcases lt_or_eq_of_le (Set.encard_image_le f s) with h | h
  · exact h
  · exact False.elim (hni (hfin.injOn_of_encard_image_eq h))

def finiteOpenAnchors (F : Finset (Sym2 V)) : Set V :=
  {x | ∃ e ∈ F, x ∈ e}

theorem finiteOpenAnchors_finite (F : Finset (Sym2 V)) :
    (finiteOpenAnchors F).Finite := by
  have hsub : finiteOpenAnchors F ⊆ ⋃ e ∈ F, {x | x ∈ e} := by
    rintro x ⟨e, he, hxe⟩
    exact Set.mem_biUnion he hxe
  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion F.finite_toSet
  intro e _
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hsubxy : {z : V | z ∈ s(x, y)} ⊆ ({x, y} : Set V) := by
        intro z hz
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
          (Sym2.mem_iff.mp hz)
      exact Set.Finite.subset ((Set.finite_singleton y).insert x) hsubxy

theorem PeriodicGraph.adj_forceOpenFinset_cases (P : PeriodicGraph V)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) {x y : V}
    (h : (P.openSubgraph (forceOpenFinset F omega)).Adj x y) :
    (P.openSubgraph omega).Adj x y ∨ s(x, y) ∈ F := by
  rw [P.openSubgraph_adj] at h
  by_cases he : s(x, y) ∈ F
  · exact Or.inr he
  · left
    rw [P.openSubgraph_adj]
    exact ⟨h.1, by simpa [forceOpenFinset, he] using h.2⟩

theorem PeriodicGraph.forceOpen_reachable_anchor (P : PeriodicGraph V)
    (F : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) (x z : V)
    (h : (P.openSubgraph (forceOpenFinset F omega)).Reachable x z) :
    (P.openSubgraph omega).Reachable x z ∨
      ∃ a ∈ finiteOpenAnchors F, (P.openSubgraph omega).Reachable a z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl (SimpleGraph.Reachable.refl x)
  | @tail y z hxy hyz ih =>
      rcases P.adj_forceOpenFinset_cases F omega hyz with hadj | he
      · rcases ih with hxy' | ⟨a, ha, hay⟩
        · exact Or.inl (hxy'.trans hadj.reachable)
        · exact Or.inr ⟨a, ha, hay.trans hadj.reachable⟩
      · exact Or.inr ⟨z, ⟨s(y, z), he, Sym2.mem_mk_right y z⟩,
          SimpleGraph.Reachable.refl z⟩

theorem PeriodicGraph.exists_old_infinite_cluster_in_forceOpen
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster (forceOpenFinset F omega) x).Infinite) :
    ∃ a, a ∈ P.cluster (forceOpenFinset F omega) x ∧
      (P.cluster omega a).Infinite := by
  let omega' := forceOpenFinset F omega
  let D := P.cluster omega' x
  let A : Set V := insert x (finiteOpenAnchors F)
  have hAfin : A.Finite := (finiteOpenAnchors_finite F).insert x
  have hcover : D ⊆ ⋃ a ∈ A, P.cluster omega a := by
    intro z hz
    rcases P.forceOpen_reachable_anchor F omega x z hz with hxz | ⟨a, ha, haz⟩
    · exact Set.mem_biUnion (Set.mem_insert x _) hxz
    · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) haz
  have hcover' : D ⊆ ⋃ a ∈ A, (P.cluster omega a ∩ D) := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact Set.mem_iUnion₂.mpr ⟨a, ha, hza, hz⟩
  have hpiece : ∃ a ∈ A, (P.cluster omega a ∩ D).Infinite := by
    by_contra h
    simp only [not_exists, not_and, Set.not_infinite] at h
    exact hinf ((hAfin.biUnion h).subset hcover')
  obtain ⟨a, _, hainf⟩ := hpiece
  obtain ⟨w, hwa, hwD⟩ := hainf.nonempty
  refine ⟨w, hwD, ?_⟩
  have haInf : (P.cluster omega a).Infinite :=
    hainf.mono Set.inter_subset_left
  exact (P.cluster_eq_of_reachable omega hwa) ▸ haInf

theorem PeriodicGraph.forceOpen_image_repSet_eq
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) :
    (fun a => P.cluster (forceOpenFinset F omega) a) ''
        P.infiniteClusterRepSet omega =
      P.infiniteClusters (forceOpenFinset F omega) := by
  let omega' := forceOpenFinset F omega
  have hle : omega <= omega' := forceOpenFinset_le F omega
  ext D
  simp only [Set.mem_image, PeriodicGraph.infiniteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1.mono (P.cluster_mono hle a), a, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨w, hwD, hwInf⟩ :=
      P.exists_old_infinite_cluster_in_forceOpen F omega x hinf
    obtain ⟨r, hr, hrmin⟩ :=
      exists_periodicVertexIndex_min (P.cluster omega w)
        ⟨w, P.self_mem_cluster omega w⟩
    refine ⟨r, ⟨?_, ?_⟩, ?_⟩
    · exact (P.cluster_eq_of_reachable omega hr) ▸ hwInf
    · intro y hry
      exact hrmin y (hr.trans hry)
    · have hrw : (P.openSubgraph omega').Reachable r w :=
        P.reachable_mono hle hr.symm
      exact P.cluster_eq_of_reachable omega' (hrw.trans hwD.symm)

theorem PeriodicGraph.numInfiniteClusters_lt_of_merge
    (P : PeriodicGraph V) (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V))
    (hfin : P.numInfiniteClusters omega ≠ ⊤)
    (x y : V) (hx : (P.cluster omega x).Infinite)
    (hy : (P.cluster omega y).Infinite)
    (hne : P.cluster omega x ≠ P.cluster omega y)
    (hmerge : (P.openSubgraph (forceOpenFinset F omega)).Reachable x y) :
    P.numInfiniteClusters (forceOpenFinset F omega) <
      P.numInfiniteClusters omega := by
  let omega' := forceOpenFinset F omega
  have hle : omega <= omega' := forceOpenFinset_le F omega
  have hrepfin : (P.infiniteClusterRepSet omega).Finite := by
    rw [← Set.not_infinite]
    intro hInf
    apply hfin
    rw [P.numInfiniteClusters_eq_repSet_encard]
    exact hInf.encard_eq
  obtain ⟨rx, hrx, hrxmin⟩ :=
    exists_periodicVertexIndex_min (P.cluster omega x)
      ⟨x, P.self_mem_cluster omega x⟩
  obtain ⟨ry, hry, hrymin⟩ :=
    exists_periodicVertexIndex_min (P.cluster omega y)
      ⟨y, P.self_mem_cluster omega y⟩
  have hrxrep : rx ∈ P.infiniteClusterRepSet omega := by
    refine ⟨(P.cluster_eq_of_reachable omega hrx) ▸ hx, ?_⟩
    intro z hrxz
    exact hrxmin z (hrx.trans hrxz)
  have hryrep : ry ∈ P.infiniteClusterRepSet omega := by
    refine ⟨(P.cluster_eq_of_reachable omega hry) ▸ hy, ?_⟩
    intro z hryz
    exact hrymin z (hry.trans hryz)
  have hrxy : rx ≠ ry := by
    intro h
    apply hne
    rw [P.cluster_eq_of_reachable omega hrx,
      P.cluster_eq_of_reachable omega hry, h]
  have hsame : P.cluster omega' rx = P.cluster omega' ry := by
    have h1 : (P.openSubgraph omega').Reachable rx x :=
      P.reachable_mono hle hrx.symm
    have h2 : (P.openSubgraph omega').Reachable y ry :=
      P.reachable_mono hle hry
    exact P.cluster_eq_of_reachable omega' ((h1.trans hmerge).trans h2)
  have hni : ¬ Set.InjOn (fun a => P.cluster omega' a)
      (P.infiniteClusterRepSet omega) := fun hinj =>
    hrxy (hinj hrxrep hryrep hsame)
  have hlhs : P.numInfiniteClusters omega' =
      ((fun a => P.cluster omega' a) ''
        P.infiniteClusterRepSet omega).encard := by
    rw [show omega' = forceOpenFinset F omega from rfl,
      P.forceOpen_image_repSet_eq F omega]
    rfl
  rw [hlhs, P.numInfiniteClusters_eq_repSet_encard]
  exact encard_image_lt_of_not_injOn_periodic hrepfin hni

def PeriodicGraph.distinctInfinitePairEvent
    (P : PeriodicGraph V) (x y : V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.cluster omega x).Infinite ∧
    (P.cluster omega y).Infinite ∧
      P.cluster omega x ≠ P.cluster omega y}

theorem PeriodicGraph.exists_distinctInfinitePair_of_two_le
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    (h : 2 <= P.numInfiniteClusters omega) :
    ∃ x y, omega ∈ P.distinctInfinitePairEvent x y := by
  have hone : 1 < (P.infiniteClusters omega).encard := by
    change 2 <= (P.infiniteClusters omega).encard at h
    exact lt_of_lt_of_le (by norm_num) h
  obtain ⟨Cx, Cy, hCx, hCy, hne⟩ := Set.one_lt_encard_iff.mp hone
  obtain ⟨hxInf, x, rfl⟩ := hCx
  obtain ⟨hyInf, y, rfl⟩ := hCy
  exact ⟨x, y, hxInf, hyInf, hne⟩

theorem PeriodicGraph.exists_distinctInfinitePair_pos
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
    (hk2 : 2 <= k) :
    ∃ x y, 0 < mu (P.distinctInfinitePairEvent x y) := by
  by_contra h
  push Not at h
  have hzero : ∀ x y, mu (P.distinctInfinitePairEvent x y) = 0 := by
    intro x y
    exact le_antisymm (h x y) bot_le
  have hunion0 : mu (⋃ x, ⋃ y, P.distinctInfinitePairEvent x y) = 0 :=
    measure_iUnion_null fun x => measure_iUnion_null (hzero x)
  have hsub : {omega | P.numInfiniteClusters omega = k} ⊆
      ⋃ x, ⋃ y, P.distinctInfinitePairEvent x y := by
    intro omega homega
    obtain ⟨x, y, hxy⟩ := P.exists_distinctInfinitePair_of_two_le
      (show 2 <= P.numInfiniteClusters omega from homega.symm ▸ hk2)
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨y, hxy⟩⟩
  have hone : (1 : ENNReal) <= mu (⋃ x, ⋃ y, P.distinctInfinitePairEvent x y) := by
    rw [← hk]
    exact measure_mono hsub
  rw [hunion0] at hone
  exact one_ne_zero (le_antisymm hone bot_le)

theorem PeriodicGraph.exists_forceOpen_walk
    (P : PeriodicGraph V) (hconn : P.graph.Connected) (x y : V) :
    ∃ F : Finset (Sym2 V), ∀ omega,
      (P.openSubgraph (forceOpenFinset F omega)).Reachable x y := by
  obtain ⟨w⟩ := hconn.preconnected x y
  let F : Finset (Sym2 V) := w.edges.toFinset
  refine ⟨F, fun omega => ⟨w.transfer (P.openSubgraph (forceOpenFinset F omega)) ?_⟩⟩
  intro e he
  have heG := w.edges_subset_edgeSet he
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at heG ⊢
      rw [P.openSubgraph_adj]
      refine ⟨heG, ?_⟩
      exact forceOpenFinset_of_mem (by simpa [F] using he) omega

theorem PeriodicGraph.measurableSet_numInfiniteClusters_lt
    (P : PeriodicGraph V) (k : ℕ∞) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.numInfiniteClusters omega < k} :=
  P.measurable_numInfiniteClusters MeasurableSet.of_discrete

theorem PeriodicGraph.numInfiniteClusters_lt_null
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1) :
    mu {omega | P.numInfiniteClusters omega < k} = 0 := by
  have hsub : {omega | P.numInfiniteClusters omega = k} ⊆
      {omega | P.numInfiniteClusters omega < k}ᶜ := by
    intro omega homega
    simp only [Set.mem_setOf_eq] at homega
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, homega]
    exact lt_irrefl k
  have hfull : mu {omega | P.numInfiniteClusters omega < k}ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  exact (prob_compl_eq_one_iff (P.measurableSet_numInfiniteClusters_lt k)).mp hfull



theorem PeriodicGraph.numInfiniteClusters_const_ne_finite_two
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hfe : HasFiniteEnergy mu) {k : ℕ∞}
    (hk : mu {omega | P.numInfiniteClusters omega = k} = 1)
    (hk2 : 2 <= k) (hktop : k ≠ ⊤) : False := by
  obtain ⟨x, y, hpairPos⟩ := P.exists_distinctInfinitePair_pos mu hk hk2
  obtain ⟨F, hF⟩ := P.exists_forceOpen_walk hconn x y
  let K := {omega : ConfigSpace (Sym2 V) |
    P.numInfiniteClusters omega = k}
  let A := P.distinctInfinitePairEvent x y ∩ K
  let B := {omega : ConfigSpace (Sym2 V) |
    P.numInfiniteClusters omega < k}
  have hKmeas : MeasurableSet K :=
    P.measurable_numInfiniteClusters (measurableSet_singleton k)
  have hKcompl : mu Kᶜ = 0 := (prob_compl_eq_zero_iff hKmeas).2 hk
  have hApos : 0 < mu A := by
    by_contra hnot
    have hA0 : mu A = 0 := le_antisymm (not_lt.mp hnot) bot_le
    have hpairSub : P.distinctInfinitePairEvent x y ⊆ A ∪ Kᶜ := by
      intro omega homega
      by_cases hK : omega ∈ K
      · exact Or.inl ⟨homega, hK⟩
      · exact Or.inr hK
    have hpair0 : mu (P.distinctInfinitePairEvent x y) = 0 :=
      measure_mono_null hpairSub (measure_union_null hA0 hKcompl)
    rw [hpair0] at hpairPos
    exact (lt_irrefl 0) hpairPos
  have hsub : A ⊆ forceOpenFinset F ⁻¹' B := by
    intro omega homega
    have hcount : P.numInfiniteClusters omega = k := homega.2
    have hfinite : P.numInfiniteClusters omega ≠ ⊤ := by
      rw [hcount]
      exact hktop
    have hlt := P.numInfiniteClusters_lt_of_merge F omega hfinite x y
      homega.1.1 homega.1.2.1 homega.1.2.2 (hF omega)
    change P.numInfiniteClusters (forceOpenFinset F omega) < k
    rwa [hcount] at hlt
  have hnull := P.numInfiniteClusters_lt_null mu hk
  have hpush : (mu.map (forceOpenFinset F)) B = mu (forceOpenFinset F ⁻¹' B) :=
    Measure.map_apply (measurable_forceOpenFinset F)
      (P.measurableSet_numInfiniteClusters_lt k)
  have hpre0 : mu (forceOpenFinset F ⁻¹' B) = 0 := by
    rw [← hpush]
    exact hfe F hnull
  have hAle : mu A <= mu (forceOpenFinset F ⁻¹' B) := measure_mono hsub
  rw [hpre0] at hAle
  exact (not_lt_of_ge hAle) hApos




theorem PeriodicGraph.numInfiniteClusters_zero_one_or_top
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (herg : P.IsErgodic mu) (hfe : HasFiniteEnergy mu) :
    ∃ k : ℕ∞, mu {omega | P.numInfiniteClusters omega = k} = 1 ∧
      (k = 0 ∨ k = 1 ∨ k = ⊤) := by
  obtain ⟨k, hk⟩ := P.numInfiniteClusters_ae_const mu herg
  refine ⟨k, hk, ?_⟩
  by_cases htop : k = ⊤
  · exact Or.inr (Or.inr htop)
  have hnot2 : ¬ 2 <= k := by
    intro hk2
    exact P.numInfiniteClusters_const_ne_finite_two hconn mu hfe hk hk2 htop
  have hle : k <= 1 := StatMech.Percolation.enat_le_one_of_not_two hnot2
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hone)

end StatMech.FK.PeriodicPlanar
