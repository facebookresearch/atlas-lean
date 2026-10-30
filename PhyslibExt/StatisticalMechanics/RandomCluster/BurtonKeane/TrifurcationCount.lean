/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneMergeGeom
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryVolumeRatio

/-!
# Counting trifurcations against the box boundary

Distinct boundary arm ends bound the trifurcation count by the boundary size; no such bound holds
for every configuration with the trifurcation notion `IsTrifurcation`.

## i. Overview

Every trifurcation of `B_n` reaches the boundary through an infinite cluster
(`tfc_trif_reaches_boundary`). An injective choice of connected boundary sites
(`tfc_DistinctArmEnds`) bounds `Tcount` by `|∂B_n|`, and under translation invariance and ergodicity
such a configuration-wide bound with `|∂B_n| = o(|B_n|)` would force `μ(0 is a trifurcation) = 0`
and, through finite-energy merging, uniqueness (`tfc_burton_keane_uniqueness_full`,
`tfc_burton_keane_bernoulli`).

These uniqueness statements are vacuous. `IsTrifurcation` lets the centre itself be one of the three
separated sites, so in `tfc_lineConfig` (all edges in one coordinate direction open) every site is a
trifurcation. Hence `tfc_DistinctArmEnds` fails for some configuration
(`tfc_not_forall_distinctArmEnds`), the bound `Tcount ≤ |∂B_n|` fails
(`tfc_not_forall_Tcount_le_boundary`), and no configuration-wide bound of order `o(|B_n|)` exists
(`tfc_not_hbound_hdens`), in every dimension `d ≥ 1`. The classical notion `bc89_GenuineTrif` does
not have this defect.

## ii. Key results

- `tfc_trif_reaches_boundary` : trifurcations reach the boundary
- `tfc_Tcount_le_boundary_of_distinctArmEnds` : distinct arm ends bound the count
- `tfc_line_isTrifurcation` : every site of `tfc_lineConfig` is a trifurcation
- `tfc_not_forall_distinctArmEnds` : distinct arm ends fail for some configuration
- `tfc_not_hbound_hdens` : no configuration-wide bound of order `o(|B_n|)` exists
- `tfc_burton_keane_bernoulli` : the conditional uniqueness statement, vacuous for `d ≥ 1`

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma tfc_boundary_cross_vertex (n : ℕ) (hn : 1 ≤ n) (z z' : Site d) (hz : z ∈ box d n)
    (hz' : z' ∉ box d n) (hadj : (hypercubicLattice d).Adj z z') :
    z ∈ vertexBoundary d n := by
  rw [mem_box] at hz; rw [mem_box] at hz'; push Not at hz'
  obtain ⟨i, hi⟩ := hz'
  rw [hypercubicLattice_adj] at hadj
  have hipos : 1 ≤ (z i - z' i).natAbs := by
    rcases Nat.eq_zero_or_pos (z i - z' i).natAbs with h0 | hpos
    · exfalso; rw [Int.natAbs_eq_zero, sub_eq_zero] at h0
      have := hz i; rw [h0] at this; omega
    · exact hpos
  have hterm : (z i - z' i).natAbs = 1 := by
    by_contra hne
    have hge2 : 2 ≤ (z i - z' i).natAbs := by omega
    have hle : (z i - z' i).natAbs ≤ ∑ j, (z j - z' j).natAbs :=
      Finset.single_le_sum (f := fun j => (z j - z' j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hzin : (z i).natAbs = n := by have h1 := hz i; omega
  refine ⟨fun j => hz j, ?_⟩
  rw [mem_box]; push Not
  exact ⟨i, by rw [hzin]; omega⟩

lemma tfc_walk_crossing {V : Type*} (G : SimpleGraph V) (p : V → Prop) [DecidablePred p] :
    ∀ {x y : V} (_w : G.Walk x y), p x → ¬ p y →
      ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧ G.Reachable x a := by
  intro x y w
  induction w with
  | nil => intro hx hy; exact absurd hx hy
  | @cons u v z hadj w' ih =>
    intro hu hz
    by_cases hv : p v
    · obtain ⟨a, b, hab, ha, hb, hr⟩ := ih hv hz
      exact ⟨a, b, hab, ha, hb, (hadj.reachable).trans hr⟩
    · exact ⟨u, v, hadj, hu, hv, Reachable.refl u⟩

lemma tfc_trif_cluster_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (htri : IsTrifurcation d ω x) : (cluster d ω x).Infinite := by
  obtain ⟨a₁, _, _, _, hconn, hinf, _⟩ := htri
  rw [cluster_eq_of_connected hconn.1]; exact hinf.1

lemma tfc_trif_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ z ∈ vertexBoundary d n, Connected d ω x z := by
  classical
  have hxinf : (cluster d ω x).Infinite := tfc_trif_cluster_infinite ω x htri
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω x).mp hxinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨a, b, hab, ha, hb, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω) (fun v => v ∈ box d n) w hxbox hybox
  have hablat : (hypercubicLattice d).Adj a b := (openSubgraph_le ω) hab
  exact ⟨a, tfc_boundary_cross_vertex n hn a b ha hb hablat, hr⟩


open Classical in
/-- The trifurcations in the box `B_n`. -/
noncomputable def tfc_trifFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) :=
  (boxFinsetBK d n).filter (fun x => IsTrifurcation d ω x)

lemma tfc_trifFinset_card (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (tfc_trifFinset ω n).card = Tcount d ω n := rfl

/-- The vertex boundary of `B_n` as a finite set. -/
noncomputable def tfc_boundaryFinset (d n : ℕ) : Finset (Site d) :=
  (vertexBoundary_finite d n).toFinset

lemma tfc_boundaryFinset_card (d n : ℕ) :
    (tfc_boundaryFinset d n).card = boxSV_boundaryCard d n := rfl

lemma tfc_mem_trifFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x : Site d} :
    x ∈ tfc_trifFinset ω n ↔ x ∈ box d n ∧ IsTrifurcation d ω x := by
  classical
  rw [tfc_trifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]

lemma tfc_mem_boundaryFinset {d n : ℕ} {x : Site d} :
    x ∈ tfc_boundaryFinset d n ↔ x ∈ vertexBoundary d n := by
  rw [tfc_boundaryFinset, Set.Finite.mem_toFinset]

lemma tfc_boundaryCard_zero (d : ℕ) : boxSV_boundaryCard d 0 = 0 := by
  unfold boxSV_boundaryCard
  rw [Set.Finite.toFinset_eq_empty.mpr, Finset.card_empty]
  rw [vertexBoundary]; norm_num

lemma tfc_Tcount_le_of_injOn (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : ∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmaps x hx.1 hx.2
  · intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    exact hinj x hx.1 hx.2 y hy.1 hy.2 hxy

lemma tfc_Tcount_le_card (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (φ : Site d → Site d)
    (hmaps : Set.MapsTo φ (tfc_trifFinset ω n) (tfc_boundaryFinset d n))
    (hinj : Set.InjOn φ (tfc_trifFinset ω n)) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  exact Finset.card_le_card_of_injOn φ hmaps hinj

/-- An injection from the trifurcations of `B_n` into the boundary of `B_n`. -/
def tfc_BoundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y)

lemma tfc_Tcount_le_boundary_of_residue (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tfc_BoundaryArmInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact tfc_Tcount_le_of_injOn ω n φ hmaps hinj

lemma tfc_Tcount_le_boundary_of_injection
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), tfc_BoundaryArmInjection ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n => tfc_Tcount_le_boundary_of_residue ω n (hres ω n)

/-- Distinct arm ends for `B_n`: each trifurcation is sent to a boundary site it is connected to,
injectively on trifurcations. -/
def tfc_DistinctArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ φ : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      φ x ∈ vertexBoundary d n ∧ Connected d ω x (φ x)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → φ x = φ y → x = y)

lemma tfc_boundaryArmInjection_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) : tfc_BoundaryArmInjection ω n := by
  obtain ⟨φ, hmaps, hinj⟩ := h
  exact ⟨φ, fun x hx htri => (hmaps x hx htri).1, hinj⟩

lemma tfc_Tcount_le_boundary_of_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : tfc_DistinctArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n (tfc_boundaryArmInjection_of_distinctArmEnds ω n h)

/-- The boundary sites of `B_n` connected to `x`. -/
def tfc_armEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) : Set (Site d) :=
  {z | z ∈ vertexBoundary d n ∧ Connected d ω x z}

lemma tfc_armEnds_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    (tfc_armEnds ω n x).Nonempty := by
  obtain ⟨z, hzb, hzc⟩ := tfc_trif_reaches_boundary ω n hn x hxbox htri
  exact ⟨z, hzb, hzc⟩

lemma tfc_distinctArmEnds_iff_injSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    tfc_DistinctArmEnds ω n ↔
      ∃ φ : Site d → Site d,
        (∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ tfc_armEnds ω n x) ∧
        (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
          IsTrifurcation d ω y → φ x = φ y → x = y) := by
  constructor
  · rintro ⟨φ, hmaps, hinj⟩
    exact ⟨φ, fun x hx htri => hmaps x hx htri, hinj⟩
  · rintro ⟨φ, hmaps, hinj⟩
    exact ⟨φ, fun x hx htri => hmaps x hx htri, hinj⟩

lemma tfc_distinctArmEnds_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    tfc_DistinctArmEnds ω n := by
  classical
  refine ⟨fun x => if hx : x ∈ box d n ∧ IsTrifurcation d ω x then
      (tfc_armEnds_nonempty ω n hn x hx.1 hx.2).choose else x, ?_, ?_⟩
  · intro x hxbox htri
    simp only [dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    have hspec := (tfc_armEnds_nonempty ω n hn x hxbox htri).choose_spec
    exact ⟨hspec.1, hspec.2⟩
  · intro x hxbox htri y hybox htriy _
    exact hsub x y hxbox htri hybox htriy

lemma tfc_residue_zero_iff_no_origin_trif (ω : ConfigSpace (Sym2 (Site d))) :
    tfc_BoundaryArmInjection ω 0 ↔ ¬ IsTrifurcation d ω 0 := by
  classical
  constructor
  · rintro ⟨φ, hmaps, _⟩ htri0
    have h0box : (0 : Site d) ∈ box d 0 := by
      rw [mem_box]; intro i; rw [show (0 : Site d) i = 0 from rfl]; simp
    have hmem := hmaps 0 h0box htri0
    rw [vertexBoundary] at hmem
    simp only [Nat.zero_sub, Set.mem_sdiff] at hmem
    exact hmem.2 hmem.1
  · intro h0
    have hx0 : ∀ x : Site d, x ∈ box d 0 → x = 0 := by
      intro x hxbox
      funext i; have := (mem_box.mp hxbox) i
      rw [show (0 : Site d) i = 0 from rfl]; omega
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro x hxbox htri
      exact absurd ((hx0 x hxbox) ▸ htri) h0
    · intro x hxbox htri y _ _ _
      exact absurd ((hx0 x hxbox) ▸ htri) h0

lemma tfc_Tcount_zero_le_boundary_iff (ω : ConfigSpace (Sym2 (Site d))) :
    Tcount d ω 0 ≤ boxSV_boundaryCard d 0 ↔ ¬ IsTrifurcation d ω 0 := by
  classical
  rw [tfc_boundaryCard_zero, Nat.le_zero, ← tfc_trifFinset_card, Finset.card_eq_zero,
    tfc_trifFinset, Finset.filter_eq_empty_iff]
  constructor
  · intro h htri0
    have h0box : (0 : Site d) ∈ boxFinsetBK d 0 := by
      rw [boxFinsetBK, Set.Finite.mem_toFinset, mem_box]; intro i
      rw [show (0 : Site d) i = 0 from rfl]; simp
    exact h h0box htri0
  · intro h0 x hxbox
    rw [boxFinsetBK, Set.Finite.mem_toFinset] at hxbox
    have hx0 : x = 0 := by
      funext i; have := (mem_box.mp hxbox) i
      rw [show (0 : Site d) i = 0 from rfl]; omega
    exact hx0 ▸ h0

lemma tfc_trifurcation_prob_eq_zero (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0)) :
    μ {ω | IsTrifurcation d ω 0} = 0 := by
  classical
  set p : ℝ≥0∞ := μ {ω | IsTrifurcation d ω 0} with hp
  have hkey : ∀ n, 1 ≤ n → ((boxFinsetBK d n).card : ℝ≥0∞) * p ≤ (bdry n : ℝ≥0∞) := by
    intro n hn
    have hexp := expected_Tcount μ hinv n
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ ≤ (bdry n : ℝ≥0∞) := by
      calc ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ
          ≤ ∫⁻ _ω, (bdry n : ℝ≥0∞) ∂μ := by
            apply lintegral_mono; intro ω; simp only
            exact_mod_cast hbound ω n hn
        _ = (bdry n : ℝ≥0∞) := by rw [lintegral_const]; simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := by rw [hp]; exact (measure_ne_top μ _)
  set pr : ℝ := p.toReal with hpr
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ n, 1 ≤ n → ((boxFinsetBK d n).card : ℝ) * pr ≤ (bdry n : ℝ) := by
    intro n hn
    have h := hkey n hn
    have h' : (((boxFinsetBK d n).card : ℝ≥0∞) * p).toReal ≤ (bdry n : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, hpr] using h'
  have hvolr : ∀ n, (0 : ℝ) < ((boxFinsetBK d n).card : ℝ) := by
    intro n; exact_mod_cast hvol n
  have hle : ∀ᶠ n in atTop, pr ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [le_div_iff₀ (hvolr n)]; linarith [hkeyr n hn]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hdens hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := by rw [← hpr]; exact hpreq
  have : p = 0 := (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  rw [hp] at this; exact this

lemma tfc_numInfiniteClusters_ae_const_ne_top
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
  have htri0 : μ {ω | IsTrifurcation d ω 0} = 0 :=
    tfc_trifurcation_prob_eq_zero μ herg.isTranslationInvariant bdry hbound hvol hdens
  have htop0 : μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
    by_contra h
    have hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤} := pos_iff_ne_zero.mpr h
    have := htrif hpos
    rw [htri0] at this
    exact (lt_irrefl 0) this
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  refine ⟨k, ?_, hk⟩
  intro hktop
  rw [hktop] at hk
  rw [hk] at htop0
  exact one_ne_zero htop0

open Classical in
/-- The configuration in which exactly the edges in coordinate direction `i₀` are open: `ℤ^d` is
cut into disjoint open lines parallel to the `i₀`-axis. Every site is a trifurcation in the sense
of `IsTrifurcation`, which is why configuration-wide trifurcation counting bounds fail. -/
noncomputable def tfc_lineConfig (i₀ : Fin d) : ConfigSpace (Sym2 (Site d)) :=
  fun e => decide (∃ z : Site d, e = s(z, z + Pi.single i₀ 1))

lemma tfc_line_adj (i₀ : Fin d) (z : Site d) :
    (openSubgraph d (tfc_lineConfig i₀)).Adj z (z + Pi.single i₀ 1) := by
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · simp only [tfc_lineConfig, decide_eq_true_eq]; exact ⟨z, rfl⟩

lemma tfc_line_connected (i₀ : Fin d) (x : Site d) (a b : ℤ) :
    Connected d (tfc_lineConfig i₀) (x + Pi.single i₀ a) (x + Pi.single i₀ b) := by
  suffices h : ∀ k : ℕ, ∀ a : ℤ, Connected d (tfc_lineConfig i₀) (x + Pi.single i₀ a)
      (x + Pi.single i₀ (a + k)) by
    rcases le_total a b with hab | hab
    · have := h (b - a).toNat a
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    · have := h (a - b).toNat b
      rw [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
      exact this.symm
  intro k
  induction k with
  | zero => intro a; simpa using connected_refl _ _
  | succ k ih =>
    intro a
    refine (ih a).trans ?_
    have : Connected d (tfc_lineConfig i₀) (x + Pi.single i₀ (a + k))
        (x + Pi.single i₀ (a + k) + Pi.single i₀ 1) := (tfc_line_adj i₀ _).reachable
    rw [add_assoc, ← Pi.single_add] at this
    convert this using 3
    push_cast; ring

lemma tfc_line_step {i₀ : Fin d} {x z v : Site d} {j : ℤ}
    (h : s(x + Pi.single i₀ j, v) = s(z, z + Pi.single i₀ 1)) :
    v = x + Pi.single i₀ (j + 1) ∨ v = x + Pi.single i₀ (j - 1) := by
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [h2, ← h1, add_assoc, ← Pi.single_add]
  · right
    rw [h2, eq_sub_of_add_eq h1.symm, add_sub_assoc, ← Pi.single_sub]

lemma tfc_line_on_line (i₀ : Fin d) (x : Site d) {m : ℤ} {y : Site d}
    (h : Connected d (tfc_lineConfig i₀) (x + Pi.single i₀ m) y) :
    ∃ j : ℤ, y = x + Pi.single i₀ j := by
  obtain ⟨w⟩ := h
  suffices ∀ {u v : Site d} (w : (openSubgraph d (tfc_lineConfig i₀)).Walk u v),
      (∃ j : ℤ, u = x + Pi.single i₀ j) → ∃ j : ℤ, v = x + Pi.single i₀ j from this w ⟨m, rfl⟩
  intro u v w
  induction w with
  | nil => exact id
  | cons hadj _ ih =>
    rintro ⟨j, rfl⟩
    apply ih
    obtain ⟨_, hopen⟩ := hadj
    simp only [tfc_lineConfig, decide_eq_true_eq] at hopen
    obtain ⟨z, hz⟩ := hopen
    rcases tfc_line_step hz with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

lemma tfc_line_point_injective (i₀ : Fin d) (x : Site d) :
    Function.Injective (fun j : ℤ => x + Pi.single i₀ j) :=
  (add_right_injective x).comp (Pi.single_injective i₀)

lemma tfc_line_ne (i₀ : Fin d) (x : Site d) {j : ℤ} (hj : j ≠ 0) :
    x + Pi.single i₀ j ≠ x := by
  intro h
  have := congrFun h i₀
  simp only [Pi.add_apply, Pi.single_eq_same, add_eq_left] at this
  exact hj this

lemma tfc_line_cluster_infinite (i₀ : Fin d) (x : Site d) (a : ℤ) :
    (cluster d (tfc_lineConfig i₀) (x + Pi.single i₀ a)).Infinite :=
  Set.infinite_of_injective_forall_mem (tfc_line_point_injective i₀ x)
    (fun b => tfc_line_connected i₀ x a b)

lemma tfc_removeSite_center_isolated (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : y ≠ x) : ¬ Connected d (removeSite x ω) x y := by
  rintro ⟨w⟩
  cases w with
  | nil => exact hxy rfl
  | cons hadj _ =>
    obtain ⟨_, hopen⟩ := hadj
    rw [removeSite_apply_of_mem (Sym2.mem_mk_left _ _)] at hopen
    exact Bool.false_ne_true hopen

lemma tfc_line_removeSite_sides (i₀ : Fin d) (x : Site d) :
    ¬ Connected d (removeSite x (tfc_lineConfig i₀))
      (x + Pi.single i₀ (-1)) (x + Pi.single i₀ 1) := by
  rintro ⟨w⟩
  suffices ∀ {u v : Site d}
      (w : (openSubgraph d (removeSite x (tfc_lineConfig i₀))).Walk u v),
      (∃ j < 0, u = x + Pi.single i₀ j) → ∃ j < 0, v = x + Pi.single i₀ j by
    obtain ⟨j, hj, hjeq⟩ := this w ⟨-1, by omega, rfl⟩
    have : (1 : ℤ) = j := tfc_line_point_injective i₀ x hjeq
    omega
  intro u v w
  induction w with
  | @cons a v' c hadj _ ih =>
    rintro ⟨j, hj, rfl⟩
    apply ih
    obtain ⟨_, hopen⟩ := hadj
    by_cases hmem : x ∈ s(x + Pi.single i₀ j, v')
    · rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen Bool.false_ne_true
    · rw [removeSite, ite_eq_right hmem] at hopen
      simp only [tfc_lineConfig, decide_eq_true_eq] at hopen
      obtain ⟨z, hz⟩ := hopen
      rcases tfc_line_step hz with h | h
      · refine ⟨j + 1, ?_, h⟩
        have : j + 1 ≠ 0 := by
          intro h0; apply hmem; rw [h, h0, Pi.single_zero, add_zero]
          exact Sym2.mem_mk_right _ _
        omega
      · exact ⟨j - 1, by omega, h⟩
  | nil => exact id

/-- In `tfc_lineConfig i₀` every site is a trifurcation in the sense of `IsTrifurcation`: the
site itself and its two neighbours on its line are separated once the site is removed. -/
lemma tfc_line_isTrifurcation (i₀ : Fin d) (x : Site d) :
    IsTrifurcation d (tfc_lineConfig i₀) x := by
  have hinj := tfc_line_point_injective i₀ x
  refine ⟨x, x + Pi.single i₀ (-1), x + Pi.single i₀ 1,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (tfc_line_ne i₀ x (by norm_num)).symm
  · exact (tfc_line_ne i₀ x (by norm_num)).symm
  · intro h; have : (-1 : ℤ) = 1 := hinj h; omega
  · exact connected_refl _ _
  · simpa using tfc_line_connected i₀ x 0 (-1)
  · simpa using tfc_line_connected i₀ x 0 1
  · simpa using tfc_line_cluster_infinite i₀ x 0
  · exact tfc_line_cluster_infinite i₀ x _
  · exact tfc_line_cluster_infinite i₀ x _
  · exact tfc_removeSite_center_isolated _ (tfc_line_ne i₀ x (by norm_num))
  · exact tfc_removeSite_center_isolated _ (tfc_line_ne i₀ x (by norm_num))
  · exact tfc_line_removeSite_sides i₀ x

lemma tfc_axis_mem_box (i₀ : Fin d) {j : ℤ} {n : ℕ} (hj : j.natAbs ≤ n) :
    (0 : Site d) + Pi.single i₀ j ∈ box d n := by
  intro i
  by_cases hi : i = i₀
  · subst hi; simpa using hj
  · simp [hi]

lemma tfc_axis_mem_vertexBoundary (i₀ : Fin d) {j : ℤ} {n : ℕ}
    (h : (0 : Site d) + Pi.single i₀ j ∈ vertexBoundary d n) : j.natAbs = n := by
  obtain ⟨h1, h2⟩ := h
  have hle : j.natAbs ≤ n := by simpa using h1 i₀
  by_contra hne
  exact h2 (tfc_axis_mem_box i₀ (by omega))

/-- `tfc_DistinctArmEnds` fails for `tfc_lineConfig` and every `n ≥ 1`: the three trifurcations
`-e, 0, e` on the `i₀`-axis can only reach the two boundary sites `±n e` of that axis. -/
lemma tfc_line_not_distinctArmEnds (i₀ : Fin d) {n : ℕ} (hn : 1 ≤ n) :
    ¬ tfc_DistinctArmEnds (tfc_lineConfig i₀) n := by
  rintro ⟨φ, hφ, hinj⟩
  have hpt := tfc_line_point_injective i₀ (0 : Site d)
  have hbox : ∀ m : ℤ, m.natAbs ≤ 1 → (0 : Site d) + Pi.single i₀ m ∈ box d n :=
    fun m hm => tfc_axis_mem_box i₀ (by omega)
  have key : ∀ m : ℤ, m.natAbs ≤ 1 → ∃ j : ℤ,
      φ ((0 : Site d) + Pi.single i₀ m) = (0 : Site d) + Pi.single i₀ j ∧ j.natAbs = n := by
    intro m hm
    obtain ⟨hb, hc⟩ := hφ _ (hbox m hm) (tfc_line_isTrifurcation i₀ _)
    obtain ⟨j, hj⟩ := tfc_line_on_line i₀ 0 hc
    exact ⟨j, hj, tfc_axis_mem_vertexBoundary i₀ (hj ▸ hb)⟩
  have hne : ∀ a b : ℤ, a.natAbs ≤ 1 → b.natAbs ≤ 1 → a ≠ b →
      φ ((0 : Site d) + Pi.single i₀ a) ≠ φ ((0 : Site d) + Pi.single i₀ b) :=
    fun a b ha hb hab h => hab (hpt (hinj _ (hbox a ha) (tfc_line_isTrifurcation i₀ _) _
      (hbox b hb) (tfc_line_isTrifurcation i₀ _) h))
  obtain ⟨j₁, h₁, a₁⟩ := key (-1) (by decide)
  obtain ⟨j₂, h₂, a₂⟩ := key 0 (by decide)
  obtain ⟨j₃, h₃, a₃⟩ := key 1 (by decide)
  have n12 := hne (-1) 0 (by decide) (by decide) (by decide)
  have n13 := hne (-1) 1 (by decide) (by decide) (by decide)
  have n23 := hne 0 1 (by decide) (by decide) (by decide)
  rw [h₁, h₂] at n12; rw [h₁, h₃] at n13; rw [h₂, h₃] at n23
  have e12 : j₁ ≠ j₂ := fun h => n12 (by rw [h])
  have e13 : j₁ ≠ j₃ := fun h => n13 (by rw [h])
  have e23 : j₂ ≠ j₃ := fun h => n23 (by rw [h])
  omega

/-- The configuration-wide hypothesis `∀ ω n, 1 ≤ n → tfc_DistinctArmEnds ω n` is false in every
dimension `d ≥ 1`, so every statement that assumes it is vacuous. -/
lemma tfc_not_forall_distinctArmEnds (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfc_DistinctArmEnds ω n :=
  fun h => tfc_line_not_distinctArmEnds ⟨0, hd⟩ le_rfl (h _ 1 le_rfl)

/-- In `tfc_lineConfig` every site of the box is a trifurcation, so `Tcount` is the volume. -/
lemma tfc_line_Tcount (i₀ : Fin d) (n : ℕ) :
    Tcount d (tfc_lineConfig i₀) n = (boxFinsetBK d n).card := by
  classical
  unfold Tcount
  congr 1
  exact Finset.filter_true_of_mem (fun x _ => tfc_line_isTrifurcation i₀ x)

/-- A configuration-wide trifurcation bound by the boundary size is false in every dimension
`d ≥ 1`: in `tfc_lineConfig` every site of `B_n` is a trifurcation, and the boundary of `B_n` is a
proper subset of the box (it misses the origin). -/
lemma tfc_not_forall_Tcount_le_boundary (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      Tcount d ω n ≤ boxSV_boundaryCard d n := by
  intro h
  have h1 := h (tfc_lineConfig ⟨0, hd⟩) 1 le_rfl
  rw [tfc_line_Tcount] at h1
  refine absurd h1 (not_le.mpr (Finset.card_lt_card ?_))
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨0, ?_, ?_⟩
    · simp only [boxFinsetBK, Set.Finite.mem_toFinset]; intro i; simp
    · simp only [Set.Finite.mem_toFinset, vertexBoundary, Set.mem_sdiff, not_and, not_not]
      intro _ i; simp
  · intro x hx
    simp only [Set.Finite.mem_toFinset, vertexBoundary, Set.mem_sdiff] at hx
    simp only [boxFinsetBK, Set.Finite.mem_toFinset]; exact hx.1

/-- A configuration-wide trifurcation bound `Tcount d ω n ≤ bdry n` (for all `ω` and `n ≥ 1`)
cannot hold with `bdry n / |box d n| → 0` when `d ≥ 1`: `tfc_lineConfig` has `Tcount` equal to
the volume. So the hypotheses `hbound` and `hdens` of the counting form of Burton–Keane are
jointly unsatisfiable in every dimension `d ≥ 1`. -/
lemma tfc_not_hbound_hdens (hd : 1 ≤ d) (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0)) :
    False := by
  have hlt : ∀ᶠ n in atTop, (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) < 1 :=
    hdens.eventually (gt_mem_nhds (by norm_num))
  have hge : ∀ᶠ n in atTop, 1 ≤ (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h := hbound (tfc_lineConfig ⟨0, hd⟩) n hn
    rw [tfc_line_Tcount] at h
    rw [one_le_div (by exact_mod_cast hvol n)]
    exact_mod_cast h
  obtain ⟨n, h1, h2⟩ := (hlt.and hge).exists
  linarith

/-- The counting form of the Burton–Keane theorem (Burton and Keane, *Density and uniqueness in
percolation*, 1989): an ergodic measure with finite-energy merging, a configuration-wide
trifurcation bound `hbound` with `bdry n = o(|B_n|)` and the trifurcation input `htrif` has at
most one infinite cluster. For `d ≥ 1` the hypotheses `hbound` and `hdens` contradict each other
(`tfc_not_hbound_hdens`), so the statement is vacuous. -/
theorem tfc_burton_keane_uniqueness_full
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ :=
      tfc_numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top
      (fun k hk2 hktop hk => hmergeGeom_discharged μ k hk2 hktop hk)
  exact ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

/-- Burton–Keane uniqueness for Bernoulli bond percolation from distinct arm ends in every box. The
hypothesis `hres` is false (`tfc_not_forall_distinctArmEnds`), so the statement is vacuous. -/
theorem tfc_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      tfc_DistinctArmEnds ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (fun ω n hn => tfc_Tcount_le_boundary_of_distinctArmEnds ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
