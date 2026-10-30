/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.Ergodicity
public import MathlibExt.Probability.Percolation.SubcriticalDecay

/-!
# The number of infinite clusters is almost surely constant

For a probability measure on bond configurations of `ℤ^d` that is ergodic under lattice
translations, the number `N(ω) ∈ ℕ∪{∞}` of infinite open clusters is measurable and translation
invariant, hence almost surely equal to a constant in `ℕ∞`. This is the Newman–Schulman step,
which the Burton–Keane argument starts from. Nothing more is proved here: neither `N ∈ {0, 1, ∞}`
nor the Burton–Keane uniqueness `N ≤ 1` is proved anywhere in this library. Translation ergodicity
of Bernoulli product measures is proved in PhyslibExt (`RandomCluster/Ergodicity`,
`bernoulli_isErgodic`), not in MathlibExt.

## Main definitions

* `StatMech.Percolation.sym2Action`: translations of `ℤ^d` acting on edges.
* `StatMech.Percolation.infiniteClusters`, `StatMech.Percolation.numInfiniteClusters`: the set of
  infinite open clusters and their number `N(ω)`.

## Main results

* `StatMech.ConfigSpace.ergodic_ae_const_of_shiftInvariant`: a measurable, shift-invariant function
  with countable values is a.s. constant under an ergodic measure.
* `StatMech.Percolation.measurable_numInfiniteClusters`,
  `StatMech.Percolation.numInfiniteClusters_shift`.
* `StatMech.Percolation.numInfiniteClusters_ae_const`: `N` is a.s. constant.
* `StatMech.Percolation.measurableSet_connected`,
  `StatMech.Percolation.measurableSet_crossingEvent`: connection events and the one-arm event are
  measurable.

## References

* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
* C. M. Newman, L. S. Schulman, *Infinite clusters in percolation models*, J. Stat. Phys. 26 (1981),
  613–628.
-/

@[expose] public section

open MeasureTheory

namespace StatMech

namespace ConfigSpace

variable {E G : Type*} [Group G] [MulAction G E]
variable {μ : Measure (ConfigSpace E)}

/-- A measurable function with countable values that is invariant under all shifts is almost
surely constant under an ergodic probability measure. See also Mathlib's `ErgodicSMul` and
`aeconst_of_forall_preimage_smul_ae_eq`, which state ergodicity of a group action through
a.e.-invariant sets. -/
theorem ergodic_ae_const_of_shiftInvariant [IsProbabilityMeasure μ]
    {β : Type*} [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (herg : IsErgodic (G := G) μ)
    (f : ConfigSpace E → β) (hf : Measurable f)
    (hinv : ∀ (g : G) (ω : ConfigSpace E), f (shift g ω) = f ω) :
    ∃ k : β, μ {ω | f ω = k} = 1 := by
  classical
  have hmeas : ∀ k : β, MeasurableSet {ω | f ω = k} := fun k =>
    hf (measurableSet_singleton k)
  have hshiftinv : ∀ k : β, ∀ g : G,
      (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' {ω | f ω = k} = {ω | f ω = k} := by
    intro k g
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hinv g ω]
  have hdich : ∀ k : β, μ {ω | f ω = k} = 0 ∨ μ {ω | f ω = k} = 1 := by
    intro k
    rcases herg.2 _ (hmeas k) (hshiftinv k) with h | h
    · exact Or.inl h
    · exact Or.inr (by rwa [measure_univ] at h)
  by_contra hcon
  simp only [not_exists] at hcon
  have hall0 : ∀ k : β, μ {ω | f ω = k} = 0 := by
    intro k
    rcases hdich k with h | h
    · exact h
    · exact absurd h (hcon k)
  have huniv : (Set.univ : Set (ConfigSpace E)) = ⋃ k : β, {ω | f ω = k} := by
    ext ω
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨f ω, rfl⟩
  have hz : μ Set.univ = 0 := by
    rw [huniv]
    refine le_antisymm ?_ zero_le
    calc μ (⋃ k, {ω | f ω = k}) ≤ ∑' k, μ {ω | f ω = k} := measure_iUnion_le _
      _ = 0 := by simp [hall0]
  rw [measure_univ] at hz
  exact one_ne_zero hz

end ConfigSpace

namespace Percolation

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}

/-- Lattice translations `x ↦ x + g` acting on (unordered) edges of `ℤ^d`. -/
noncomputable instance sym2Action (d : ℕ) :
    MulAction (Multiplicative (Site d)) (Sym2 (Site d)) where
  smul g e := Sym2.map (fun x => g • x) e
  one_smul e := by
    change Sym2.map _ e = e
    have h : (fun x : Site d => (1 : Multiplicative (Site d)) • x) = id := by
      funext x; rw [one_smul]; rfl
    rw [h, Sym2.map_id]; rfl
  mul_smul g h e := by
    change Sym2.map _ e = Sym2.map _ (Sym2.map _ e)
    rw [Sym2.map_map]
    congr 1
    funext x
    change (g * h) • x = g • h • x
    rw [mul_smul]

lemma smul_sym2_mk (g : Multiplicative (Site d)) (x y : Site d) :
    g • s(x, y) = s(g • x, g • y) := by
  change Sym2.map _ _ = _
  rw [Sym2.map_mk]

lemma smul_site_apply (g : Multiplicative (Site d)) (x : Site d) (i : Fin d) :
    (g • x) i = Multiplicative.toAdd g i + x i := rfl

lemma hyper_adj_smul (g : Multiplicative (Site d)) (x y : Site d) :
    (hypercubicLattice d).Adj (g • x) (g • y) ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj]
  have key : ∀ i : Fin d, ((g • x) i - (g • y) i).natAbs = (x i - y i).natAbs := by
    intro i
    rw [smul_site_apply, smul_site_apply]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i)]

lemma shift_apply_smul (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) : (shift g ω) s(g • x, g • y) = ω s(x, y) := by
  rw [shift_apply]
  congr 1
  change g⁻¹ • s(g • x, g • y) = s(x, y)
  rw [smul_sym2_mk]
  congr 1 <;> rw [inv_smul_smul]

lemma openSubgraph_adj_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSubgraph d (shift g ω)).Adj (g • x) (g • y) ↔ (openSubgraph d ω).Adj x y := by
  simp only [openSubgraph_adj]
  rw [hyper_adj_smul, shift_apply_smul]

/-- Translation by `g` as a graph homomorphism between the open subgraphs of `ω` and of its
shift. -/
def translateHom (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d ω →g openSubgraph d (shift g ω) where
  toFun x := g • x
  map_rel' {x y} h := (openSubgraph_adj_shift g ω x y).mpr h

/-- The inverse of `translateHom`. -/
def translateHomInv (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (shift g ω) →g openSubgraph d ω where
  toFun a := g⁻¹ • a
  map_rel' {a b} h := by
    have h' := (openSubgraph_adj_shift g ω (g⁻¹ • a) (g⁻¹ • b)).mp
    simp only [smul_inv_smul] at h'
    exact h' h

@[simp] lemma translateHomInv_apply (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (a : Site d) : translateHomInv g ω a = g⁻¹ • a := rfl

lemma connected_shift (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) :
    Connected d (shift g ω) (g • x) (g • y) ↔ Connected d ω x y := by
  constructor
  · intro h
    have h2 := SimpleGraph.Reachable.map (translateHomInv g ω) h
    simp only [translateHomInv_apply, inv_smul_smul] at h2
    exact h2
  · intro h
    exact SimpleGraph.Reachable.map (translateHom g ω) h

lemma cluster_shift (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) :
    cluster d (shift g ω) (g • x) = (fun y => g • y) '' (cluster d ω x) := by
  ext z
  simp only [mem_cluster, Set.mem_image]
  constructor
  · intro h
    refine ⟨g⁻¹ • z, ?_, by rw [smul_inv_smul]⟩
    have hz : Connected d (shift g ω) (g • x) (g • (g⁻¹ • z)) := by rwa [smul_inv_smul]
    exact (connected_shift g ω x (g⁻¹ • z)).mp hz
  · rintro ⟨y, hy, rfl⟩
    exact (connected_shift g ω x y).mpr hy

/-- The set of infinite open clusters of `ω`. -/
def infiniteClusters (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Set (Site d)) :=
  {C | C.Infinite ∧ ∃ x, C = cluster d ω x}

/-- The number `N(ω) ∈ ℕ∞` of infinite open clusters of `ω`. -/
noncomputable def numInfiniteClusters (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : ℕ∞ :=
  (infiniteClusters d ω).encard

lemma smul_injective (g : Multiplicative (Site d)) :
    Function.Injective (fun y : Site d => g • y) := fun _ _ h => by simpa using h

lemma image_smul_injective (g : Multiplicative (Site d)) :
    Function.Injective (fun C : Set (Site d) => (fun y => g • y) '' C) := fun _ _ h =>
  (Set.image_injective.mpr (smul_injective g)) h

lemma infiniteClusters_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    infiniteClusters d (shift g ω)
      = (fun C => (fun y => g • y) '' C) '' (infiniteClusters d ω) := by
  ext C
  simp only [infiniteClusters, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hinf, x, rfl⟩
    refine ⟨cluster d ω (g⁻¹ • x), ⟨?_, g⁻¹ • x, rfl⟩, ?_⟩
    · have hc := cluster_shift g ω (g⁻¹ • x)
      rw [smul_inv_smul] at hc
      rw [hc] at hinf
      exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mp hinf
    · have hc := cluster_shift g ω (g⁻¹ • x)
      rw [smul_inv_smul] at hc
      exact hc.symm
  · rintro ⟨C, ⟨hinf, x, rfl⟩, rfl⟩
    refine ⟨?_, g • x, ?_⟩
    · exact (Set.infinite_image_iff (Set.injOn_of_injective (smul_injective g))).mpr hinf
    · exact (cluster_shift g ω x).symm

theorem numInfiniteClusters_shift (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    numInfiniteClusters d (shift g ω) = numInfiniteClusters d ω := by
  unfold numInfiniteClusters
  rw [infiniteClusters_shift]
  exact Set.InjOn.encard_image (Set.injOn_of_injective (image_smul_injective g))

lemma measurableSet_openAdj (x y : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y} := by
  by_cases h : (hypercubicLattice d).Adj x y
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y}
        = {ω | ω s(x, y) = true} := by
      ext ω
      rw [Set.mem_ofPred_eq, openSubgraph_adj]
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
    rw [heq]
    exact measurableSet_eq_fun (measurable_pi_apply s(x, y)) measurable_const
  · have heq : {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y} = ∅ := by
      ext ω
      rw [Set.mem_ofPred_eq, openSubgraph_adj]
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hh => h hh.1
    rw [heq]; exact MeasurableSet.empty

lemma measurableSet_isChain (l : List (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj l} := by
  induction l with
  | nil =>
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj []}
          = Set.univ := by ext ω; simp [List.IsChain.nil]
      rw [heq]; exact MeasurableSet.univ
  | cons a l ih =>
      cases l with
      | nil =>
          have heq : {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj [a]}
              = Set.univ := by ext ω; simp [List.IsChain.singleton]
          rw [heq]; exact MeasurableSet.univ
      | cons b l' =>
          have heq :
              {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj (a :: b :: l')}
                = {ω | (openSubgraph d ω).Adj a b}
                    ∩ {ω | List.IsChain (openSubgraph d ω).Adj (b :: l')} := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, List.isChain_cons_cons]
          rw [heq]
          exact (measurableSet_openAdj a b).inter ih

lemma connected_iff_chain (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    Connected d ω x y ↔
      ∃ l : List (Site d), ∃ h : (x :: l) ≠ [],
        List.IsChain (openSubgraph d ω).Adj (x :: l) ∧ (x :: l).getLast h = y := by
  unfold Connected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, List.cons_ne_nil _ _, hchain, hlast⟩
  · rintro ⟨l, _, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast

lemma measurableSet_connected (x y : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω x y} := by
  classical
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω x y}
      = ⋃ l : List (Site d), ({ω | List.IsChain (openSubgraph d ω).Adj (x :: l)}
            ∩ (if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅)) := by
    ext ω
    rw [Set.mem_ofPred_eq, connected_iff_chain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, _, hchain, hlast⟩
      exact ⟨l, hchain, by rw [ite_eq_left (by simpa using hlast)]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, List.cons_ne_nil _ _, hchain, ?_⟩
      by_cases hh : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact hh
      · rw [ite_eq_right hh] at hlast; exact absurd hlast (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply MeasurableSet.inter (measurableSet_isChain (x :: l))
  by_cases hh : (x :: l).getLast (List.cons_ne_nil _ _) = y
  · rw [ite_eq_left hh]; exact MeasurableSet.univ
  · rw [ite_eq_right hh]; exact MeasurableSet.empty

/-- The one-arm event `crossingEvent d n` (the origin is connected to a site outside
`box d (n - 1)`) is measurable. -/
theorem measurableSet_crossingEvent (n : ℕ) : MeasurableSet (crossingEvent d n) := by
  have hrw : crossingEvent d n
      = ⋃ v ∈ {v : Site d | v ∉ box d (n - 1)}, {ω | Connected d ω (origin d) v} := by
    ext ω
    simp only [mem_crossingEvent, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun ⟨v, hc, hb⟩ => ⟨v, hb, hc⟩, fun ⟨v, hb, hc⟩ => ⟨v, hc, hb⟩⟩
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun v _ => measurableSet_connected (origin d) v)

lemma cluster_infinite_iff (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    (cluster d ω x).Infinite ↔ ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d ω x y := by
  constructor
  · intro hinf n
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hsub : cluster d ω x ⊆ box d n := fun y hy => by
      by_contra hyb; exact (hcon y hyb) hy
    exact hinf ((box_finite d n).subset hsub)
  · intro h hfin
    obtain ⟨n, hn⟩ := Lattice.finite_subset_box _ hfin
    obtain ⟨y, hyb, hyc⟩ := h n
    exact hyb (hn hyc)

lemma measurableSet_clusterInfinite (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d ω x).Infinite} := by
  have heq : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d ω x).Infinite}
      = ⋂ n : ℕ, ⋃ y ∈ {y : Site d | y ∉ box d n}, {ω | Connected d ω x y} := by
    ext ω
    rw [Set.mem_ofPred_eq, cluster_infinite_iff]
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h n
      obtain ⟨y, hyb, hyc⟩ := h n
      exact ⟨y, hyb, hyc⟩
    · intro h n
      obtain ⟨y, hyb, hyc⟩ := h n
      exact ⟨y, hyb, hyc⟩
  rw [heq]
  apply MeasurableSet.iInter; intro n
  apply MeasurableSet.biUnion (Set.to_countable _); intro y _
  exact measurableSet_connected x y

lemma exists_encode_min (S : Set (Site d)) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, Encodable.encode x ≤ Encodable.encode y := by
  obtain ⟨x₀, hx₀⟩ := hne
  classical
  have hmT : sInf (Encodable.encode '' S) ∈ Encodable.encode '' S :=
    Nat.sInf_mem ⟨Encodable.encode x₀, x₀, hx₀, rfl⟩
  obtain ⟨x, hxS, hxm⟩ := hmT
  exact ⟨x, hxS, fun y hy => hxm ▸ Nat.sInf_le ⟨y, hy, rfl⟩⟩

/-- The set of sites `x` in an infinite cluster that are the `Encodable`-least site of their
cluster (one representative per infinite cluster). -/
def repSet (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Set (Site d) :=
  {x | (cluster d ω x).Infinite ∧
        ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y}

lemma image_cluster_repSet (ω : ConfigSpace (Sym2 (Site d))) :
    (fun x => cluster d ω x) '' (repSet d ω) = infiniteClusters d ω := by
  ext C
  simp only [Set.mem_image, repSet, Set.mem_ofPred_eq, infiniteClusters]
  constructor
  · rintro ⟨x, ⟨hinf, _⟩, rfl⟩
    exact ⟨hinf, x, rfl⟩
  · rintro ⟨hinf, x, rfl⟩
    obtain ⟨z, hz, hmin⟩ := exists_encode_min (cluster d ω x) ⟨x, self_mem_cluster ω x⟩
    rw [mem_cluster] at hz
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · rwa [← cluster_eq_of_connected hz]
    · intro y hzy
      exact hmin y (by rw [mem_cluster]; exact hz.trans hzy)
    · exact (cluster_eq_of_connected hz).symm

lemma injOn_cluster_repSet (ω : ConfigSpace (Sym2 (Site d))) :
    Set.InjOn (fun x => cluster d ω x) (repSet d ω) := by
  intro a ha b hb hab
  simp only at hab
  have hab' : b ∈ cluster d ω a := by rw [hab]; exact self_mem_cluster ω b
  rw [mem_cluster] at hab'
  have h1 := ha.2 b hab'
  have h2 := hb.2 a hab'.symm
  exact Encodable.encode_injective (le_antisymm h1 h2)

lemma numInfiniteClusters_eq_repSet_encard (ω : ConfigSpace (Sym2 (Site d))) :
    numInfiniteClusters d ω = (repSet d ω).encard := by
  unfold numInfiniteClusters
  rw [← image_cluster_repSet, Set.InjOn.encard_image (injOn_cluster_repSet ω)]

lemma measurableSet_repSet (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | x ∈ repSet d ω} := by
  classical
  have hpred : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) |
      ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y} := by
    have heq : {ω : ConfigSpace (Sym2 (Site d)) |
          ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y}
        = ⋂ y ∈ {y : Site d | Encodable.encode y < Encodable.encode x},
            {ω | ¬ Connected d ω x y} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h y hy hc; exact absurd (h y hc) (not_le.mpr hy)
      · intro h y hc; by_contra hlt; rw [not_le] at hlt; exact h y hlt hc
    rw [heq]
    apply MeasurableSet.biInter (Set.to_countable _); intro y _
    exact (measurableSet_connected x y).compl
  have : {ω : ConfigSpace (Sym2 (Site d)) | x ∈ repSet d ω}
      = {ω | (cluster d ω x).Infinite}
          ∩ {ω | ∀ y, Connected d ω x y → Encodable.encode x ≤ Encodable.encode y} := by
    ext ω; simp only [repSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  exact (measurableSet_clusterInfinite x).inter hpred

private lemma measurable_encard_setOf {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (p : Ω → α → Prop) (hp : ∀ a, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => Set.encard {a | p ω a}) := by
  have h1 : Measurable (fun ω => (fun a => p ω a)) := by
    rw [measurable_pi_iff]; exact hp
  exact measurable_encard.comp (measurable_setOfPred.comp h1)

theorem measurable_numInfiniteClusters :
    Measurable (numInfiniteClusters d) := by
  have heq : numInfiniteClusters d = fun ω => Set.encard {x : Site d | x ∈ repSet d ω} := by
    funext ω
    rw [numInfiniteClusters_eq_repSet_encard]
    rfl
  rw [heq]
  refine measurable_encard_setOf (fun ω x => x ∈ repSet d ω) (fun x => ?_)
  exact measurable_mem.mpr (measurableSet_repSet x)

/-- The number of infinite clusters is almost surely constant (Newman–Schulman 1981) for any
translation-ergodic probability measure on bond configurations of `ℤ^d`. -/
theorem numInfiniteClusters_ae_const
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
    ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 := by
  refine StatMech.ConfigSpace.ergodic_ae_const_of_shiftInvariant herg
    (numInfiniteClusters d) measurable_numInfiniteClusters ?_
  intro g ω
  exact numInfiniteClusters_shift g ω

end Percolation

end StatMech
