/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Theta
import MathlibExt.Probability.Percolation.Susceptibility
import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology

/-!
# Exponential decay of the subcritical cluster volume

`cluster_volume_exp_decay` bounds the volume tail of the origin cluster by an exponential.
Choose well-separated sites in the cluster until their enlarged boxes cover it. A short tour
encodes the chosen centers, and the one-arm events in their disjoint boxes are independent.
-/

public section

namespace MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted

open MeasureTheory StatMech StatMech.Lattice StatMech.Percolation SimpleGraph
open scoped NNReal

variable {d : ℕ}

private noncomputable def window (r : ℕ) (x : Site d) : Finset (Site d) :=
  (boxFinset d r).map (Equiv.addRight x).toEmbedding

private lemma mem_window {r : ℕ} {x y : Site d} :
    y ∈ window r x ↔ y - x ∈ box d r := by
  simp only [window, Finset.mem_map, mem_boxFinset, Equiv.toEmbedding_apply,
    Equiv.coe_addRight]
  exact ⟨fun ⟨z, hz, h⟩ => by simpa [← h] using hz, fun h => ⟨y - x, h, sub_add_cancel ..⟩⟩

private lemma card_window (r : ℕ) (x : Site d) :
    (window r x).card = (2 * r + 1) ^ d := by
  rw [window, Finset.card_map, card_boxFinset]

private lemma self_mem_window (r : ℕ) (x : Site d) : x ∈ window r x := by
  simp [mem_window]

private lemma window_symm {r : ℕ} {x y : Site d} (h : y ∈ window r x) :
    x ∈ window r y := by
  rw [mem_window] at h ⊢
  intro i
  simpa only [Pi.sub_apply, ← Int.natAbs_neg (x i - y i), neg_sub] using h i

private lemma window_add {r s : ℕ} {x y z : Site d}
    (hy : y ∈ window r x) (hz : z ∈ window s y) : z ∈ window (r + s) x := by
  rw [mem_window] at hy hz ⊢
  intro i
  calc ((z - x) i).natAbs = ((y - x) i + (z - y) i).natAbs := by
          simp only [Pi.sub_apply]; congr 1; abel
    _ ≤ _ := Int.natAbs_add_le _ _
    _ ≤ r + s := Nat.add_le_add (hy i) (hz i)

private lemma disjoint_windows {r : ℕ} {x y : Site d} (h : y ∉ window (2 * r) x) :
    Disjoint (window r x) (window r y) := by
  refine Finset.disjoint_left.mpr fun z hx hy => h ?_
  simpa [two_mul] using window_add hx (window_symm hy)

private lemma neighbor_mem_window {x y : Site d} (h : (hypercubicLattice d).Adj x y) :
    y ∈ window 1 x := by
  rw [mem_window]
  intro i
  rw [hypercubicLattice_adj] at h
  simpa only [Pi.sub_apply, ← Int.natAbs_neg (y i - x i), neg_sub, h] using
    (Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))

/-! ### The one-arm events at the centers -/

private noncomputable def arm (r : ℕ) (x : Site d) : Set (ConfigSpace (Sym2 (Site d))) :=
  (ConfigSpace.shift (Multiplicative.ofAdd (-x))) ⁻¹' crossingEvent d r

private lemma arm_prob (p : ℝ≥0) (hp : p ≤ 1) (r : ℕ) (x : Site d) :
    (bernoulliProductMeasure p hp).real (arm r x) = crossProb d p hp r :=
  (bernoulli_translationInvariant p hp (Multiplicative.ofAdd (-x))).measureReal_preimage
    (measurableSet_crossingEvent r).nullMeasurableSet

private lemma arm_of_connection {r : ℕ} {x y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hxy : Connected d ω x y) (hy : y ∉ window (r - 1) x) : ω ∈ arm r x := by
  let g := Multiplicative.ofAdd (-x)
  have htrans (z : Site d) : g • z = z - x := by
    funext i
    change -x i + z i = z i - x i
    abel
  have h := (connected_shift g ω x y).2 hxy
  rw [htrans, sub_self] at h
  exact ⟨g • y, h, by rwa [htrans, ← mem_window]⟩

private lemma arm_congr {r : ℕ} (hr : 1 ≤ r) (x : Site d) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ edgesWithinFinset (window r x), ω e = ω' e) :
    ω ∈ arm r x ↔ ω' ∈ arm r x := by
  unfold arm
  rw [crossingEvent_eq_boxCrossingEvent r hr]
  apply boxCrossingEvent_congr
  intro e he
  obtain ⟨u, v, hu, hv, rfl⟩ := mem_boxEdgeFinset.mp he
  rw [ConfigSpace.shift_apply, ConfigSpace.shift_apply, smul_sym2_mk]
  apply h
  have hmem (z : Site d) (hz : z ∈ box d r) :
      (Multiplicative.ofAdd (-x))⁻¹ • z ∈ window r x := by
    rw [mem_window]
    change - -x + z - x ∈ box d r
    simpa using hz
  exact mem_edgesWithinFinset.mpr ⟨_, hmem _ hu, _, hmem _ hv, rfl⟩

private noncomputable def arms (r : ℕ) (S : Finset (Site d)) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∀ x ∈ S, ω ∈ arm r x}

private lemma arms_dependsOn {r : ℕ} (hr : 1 ≤ r) (S : Finset (Site d)) :
    _root_.DependsOn ((arms r S).indicator fun _ => (1 : ℝ))
      (S.biUnion (fun x => edgesWithinFinset (window r x)) : Finset _) := by
  intro ω ω' h
  have heq (x) (hx : x ∈ S) : ω ∈ arm r x ↔ ω' ∈ arm r x :=
    arm_congr hr x fun e he => h e (Finset.mem_biUnion.mpr ⟨x, hx, he⟩)
  have iff_mem : ω ∈ arms r S ↔ ω' ∈ arms r S :=
    ⟨fun hω x hx => (heq x hx).mp (hω x hx), fun hω x hx => (heq x hx).mpr (hω x hx)⟩
  by_cases ha : ω ∈ arms r S
  · simp [Set.indicator_of_mem, ha, iff_mem.mp ha]
  · simp [Set.indicator_of_notMem, ha, iff_mem.not.mp ha]

private lemma disjoint_edges {S T : Finset (Site d)} (h : Disjoint S T) :
    Disjoint (edgesWithinFinset S) (edgesWithinFinset T) := by
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  obtain ⟨a, ha, b, _, rfl⟩ := mem_edgesWithinFinset.mp he
  obtain ⟨u, hu, v, hv, huv⟩ := mem_edgesWithinFinset.mp he'
  have hab : a ∈ s(u, v) := huv ▸ Sym2.mem_mk_left a b
  rcases Sym2.mem_iff.mp hab with rfl | rfl
  · exact Finset.disjoint_left.mp h ha hu
  · exact Finset.disjoint_left.mp h ha hv

private lemma arms_prob (p : ℝ≥0) (hp : p ≤ 1) {r : ℕ} (hr : 1 ≤ r) (S : Finset (Site d))
    (hsep : (S : Set (Site d)).PairwiseDisjoint (window r)) :
    (bernoulliProductMeasure p hp).real (arms r S) = crossProb d p hp r ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [arms]
  | insert x S hx ih =>
    have hsep' := hsep.subset (Finset.coe_subset.mpr (Finset.subset_insert x S))
    have hdis : Disjoint (edgesWithinFinset (window r x))
        (S.biUnion fun y => edgesWithinFinset (window r y)) := by
      rw [Finset.disjoint_biUnion_right]
      intro y hy
      exact disjoint_edges (hsep (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem hy)
        (fun h => hx (h ▸ hy)))
    have harm : arms r {x} = arm r x := by ext; simp [arms]
    have hA := arms_dependsOn hr ({x} : Finset (Site d))
    simp only [harm, Finset.singleton_biUnion] at hA
    have hinter : arms r (insert x S) = arm r x ∩ arms r S := by
      ext; simp [arms]
    rw [hinter, indep_cylinder_inf p hp _ _ _ _ hdis hA (arms_dependsOn hr S),
      arm_prob, ih hsep', Finset.card_insert_of_notMem hx, pow_succ, mul_comm]

/-! ### A tour through well-separated sites of a large cluster -/

/-- A coarse step can reach any other site in a box of radius `2r + 1`. -/
private def stepGraph (d r : ℕ) : SimpleGraph (Site d) where
  Adj x y := x ≠ y ∧ y ∈ window (2 * r + 1) x
  symm := ⟨fun _ _ h => ⟨h.1.symm, window_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private noncomputable local instance stepLocallyFinite (r : ℕ) :
    (stepGraph d r).LocallyFinite := fun x =>
  ((window (2 * r + 1) x).finite_toSet.subset
    (show (stepGraph d r).neighborSet x ⊆ _ from fun _ h => h.2)).fintype

private lemma degree_stepGraph_le (r : ℕ) (x : Site d) :
    (stepGraph d r).degree x ≤ (2 * (2 * r + 1) + 1) ^ d := by
  classical
  rw [← card_window _ x]
  exact Finset.card_le_card (fun y hy =>
    (show (stepGraph d r).Adj x y from (SimpleGraph.mem_neighborFinset ..).mp hy).2)

private lemma exists_uncovered {ω : ConfigSpace (Sym2 (Site d))} (r : ℕ) (S : Finset (Site d))
    (h : ((S.card * (2 * r + 1) ^ d : ℕ) : ℕ∞) < (cluster d ω (origin d)).encard) :
    ∃ y ∈ cluster d ω (origin d), y ∉ S.biUnion (window r) := by
  by_contra! hall
  have hsub : cluster d ω (origin d) ⊆ ↑(S.biUnion (window r)) := hall
  have hc : (S.biUnion (window r)).card ≤ S.card * (2 * r + 1) ^ d := by
    refine Finset.card_biUnion_le.trans ?_
    simp [card_window]
  have hle := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  exact h.not_ge (hle.trans (by exact_mod_cast hc))

private lemma extend_tour {V : Type*} [DecidableEq V] {G : SimpleGraph V} {o x y : V}
    (w : G.Walk o o) (hx : x ∈ w.support) (hxy : G.Adj x y) :
    ∃ w' : G.Walk o o, w'.length = w.length + 2 ∧
      w'.support.toFinset = insert y w.support.toFinset := by
  let a := w.takeUntil x hx
  let b := w.dropUntil x hx
  have hab : a.append b = w := w.take_spec hx
  refine ⟨a.append (.cons hxy (.cons hxy.symm b)), ?_, ?_⟩
  · have hlen := congrArg Walk.length hab
    simp only [Walk.length_append, Walk.length_cons] at *
    omega
  · ext z
    rw [← hab]
    simp only [List.mem_toFinset, Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      Finset.mem_insert]
    by_cases hz : z = x
    · subst z; simp [a.end_mem_support]
    · tauto

-- Each extension follows an open path to its first exit from the union of radius-2r boxes.
-- A two-step detour visits the new center and returns to the previous tour.
private lemma exists_tour (r k : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hvol : ((k * (2 * (2 * r) + 1) ^ d : ℕ) : ℕ∞) < (cluster d ω (origin d)).encard) :
    ∃ w : (stepGraph d r).Walk (origin d) (origin d), w.length = 2 * k ∧
      w.support.toFinset.card = k + 1 ∧
      (w.support.toFinset : Set (Site d)).PairwiseDisjoint (window r) ∧
      ∀ x ∈ w.support, x ∈ cluster d ω (origin d) := by
  classical
  induction k with
  | zero =>
    refine ⟨.nil, rfl, by simp, by simp, ?_⟩
    simpa using self_mem_cluster ω (origin d)
  | succ k ih =>
    obtain ⟨w, hw, hcard, hsep, hcluster⟩ := ih (lt_of_le_of_lt
      (Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.le_succ k))) hvol)
    let S := w.support.toFinset
    have ho : origin d ∈ S := List.mem_toFinset.mpr w.start_mem_support
    obtain ⟨v, hv, hvout⟩ := exists_uncovered (2 * r) S (by simpa [S, hcard] using hvol)
    obtain ⟨path⟩ := hv
    let U := S.biUnion (window (2 * r))
    have hoU : origin d ∈ U := Finset.mem_biUnion.mpr ⟨_, ho, self_mem_window ..⟩
    obtain ⟨a, y, ha, hy, hadj, hpath⟩ := firstExit path (U : Set _) hoU hvout
    obtain ⟨x, hx, hax⟩ := Finset.mem_biUnion.mp (show a ∈ U from ha)
    have hout (z : Site d) (hz : z ∈ S) : y ∉ window (2 * r) z :=
      fun hyz => hy (Finset.mem_biUnion.mpr ⟨z, hz, hyz⟩)
    have hnew : y ∉ S := fun h => hout y h (self_mem_window ..)
    have hxy : (stepGraph d r).Adj x y :=
      ⟨fun heq => hnew (heq ▸ hx), window_add hax (neighbor_mem_window hadj.1)⟩
    obtain ⟨w', hw', hs'⟩ := extend_tour w (List.mem_toFinset.mp hx) hxy
    refine ⟨w', by omega, ?_, ?_, ?_⟩
    · rw [hs', Finset.card_insert_of_notMem hnew, hcard]
    · rw [hs', Finset.coe_insert]
      exact hsep.insert (fun z hz _ => (disjoint_windows (hout z hz)).symm)
    · intro z hz
      have hz' := List.mem_toFinset.mpr hz
      rw [hs', Finset.mem_insert] at hz'
      rcases hz' with rfl | hz'
      · exact (SimpleGraph.Reachable.map (SimpleGraph.Embedding.induce _).toHom hpath).trans
          hadj.reachable
      · exact hcluster z (List.mem_toFinset.mp hz')

/-! ### Counting tours and choosing the scale -/

private abbrev volumeEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (n : ℕ∞) ≤ (cluster d ω (origin d)).encard}

-- Each tour costs at most two coarse steps per new center. Each center requires a crossing
-- of its own radius-r box, and these boxes are pairwise disjoint.
private lemma tour_bound (p : ℝ≥0) (hp : p ≤ 1) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    (bernoulliProductMeasure p hp).real (volumeEvent d (k * ((2 * (2 * r) + 1) ^ d + 1))) ≤
      (((2 * (2 * r + 1) + 1 : ℕ) : ℝ) ^ (2 * d) * crossProb d p hp r) ^ k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  let μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let V := (2 * (2 * r) + 1) ^ d
  let D := (2 * (2 * r + 1) + 1) ^ d
  let walks := (stepGraph d r).finsetWalkLength (2 * k) (origin d) (origin d)
  let tours := walks.filter fun w => w.support.toFinset.card = k + 1 ∧
    (w.support.toFinset : Set (Site d)).PairwiseDisjoint (window r)
  let event := fun w : (stepGraph d r).Walk (origin d) (origin d) => arms r w.support.toFinset
  have hsub : volumeEvent d (k * (V + 1)) ⊆ ⋃ w ∈ tours, event w := by
    intro ω hω
    have hvol : ((k * V : ℕ) : ℕ∞) < (cluster d ω (origin d)).encard :=
      lt_of_lt_of_le (Nat.cast_lt.mpr (by rw [Nat.mul_add, Nat.mul_one]; omega)) hω
    obtain ⟨w, hw, hcard, hsep, hconn⟩ := exists_tour r k hvol
    refine Set.mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_finsetWalkLength_iff.mpr hw, hcard, hsep⟩, ?_⟩
    intro x hx
    have hone : (({x} : Finset (Site d)).card * V : ℕ) ≤ k * V := by
      simp only [Finset.card_singleton]
      exact Nat.mul_le_mul_right V hk
    obtain ⟨y, hy, hout⟩ := exists_uncovered (2 * r) {x}
      (lt_of_le_of_lt (Nat.cast_le.mpr hone) hvol)
    simp only [Finset.singleton_biUnion] at hout
    refine arm_of_connection ((hconn x (List.mem_toFinset.mp hx)).symm.trans hy) ?_
    exact fun hy' => hout (mem_window.mpr (box_mono d (by omega) (mem_window.mp hy')))
  have hcount : tours.card ≤ D ^ (2 * k) := (Finset.card_filter_le ..).trans
    (card_finsetWalkLength_le _ (degree_stepGraph_le r) ..)
  calc μ.real (volumeEvent d (k * (V + 1))) ≤ μ.real (⋃ w ∈ tours, event w) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ w ∈ tours, μ.real (event w) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ tours, crossProb d p hp r ^ k := by
      refine Finset.sum_le_sum fun w hw => ?_
      obtain ⟨_, hcard, hsep⟩ := Finset.mem_filter.mp hw
      rw [show μ.real (event w) = _ from arms_prob p hp hr _ hsep, hcard, pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg (crossProb_nonneg ..) _) (crossProb_le_one ..)
    _ ≤ (D : ℝ) ^ (2 * k) * crossProb d p hp r ^ k := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
        (pow_nonneg (crossProb_nonneg ..) _)
    _ = _ := by push_cast [D]; rw [mul_pow]; ring

-- The polynomial number of choices for two steps is dominated by the one-arm decay.
private lemma exists_scale (p : ℝ≥0) (hp : p ≤ 1) (hd : 0 < d) (hlt : p < pc d) :
    ∃ r : ℕ, 1 ≤ r ∧ ((2 * (2 * r + 1) + 1 : ℕ) : ℝ) ^ (2 * d) * crossProb d p hp r ≤ 1 / 2 := by
  obtain ⟨c, hc, C, hC, hdec⟩ := crossProb_exp_decay_of_lt_pc hd hp hlt
  have hlim := ((summable_card_mul_exp hc (2 * d)).mul_left (3 ^ (2 * d) * C)).tendsto_atTop_zero
  obtain ⟨r, hr, hsmall⟩ := ((Filter.eventually_ge_atTop 1).and
    (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))).exists
  refine ⟨r, hr, le_trans ?_ hsmall.le⟩
  calc ((2 * (2 * r + 1) + 1 : ℕ) : ℝ) ^ (2 * d) * crossProb d p hp r
      ≤ (3 * ((2 * r + 1 : ℕ) : ℝ)) ^ (2 * d) * (C * Real.exp (-c * r)) := by
        apply mul_le_mul _ (hdec r) (crossProb_nonneg ..) (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith
    _ = _ := by rw [mul_pow]; ring

/-- **Exponential decay of the cluster volume.** For Bernoulli bond percolation on `ℤ^d`,
`d ≥ 2`, and every `p < p_c(d)`, there are `c, C > 0` such that for every `n`, the probability that
the cluster `C(0)` of the origin has at least `n` sites is at most `C e^{-cn}`; an infinite cluster
counts as having at least `n` sites. Source: H. Duminil-Copin, *Introduction to Bernoulli
percolation*, lecture notes (2018), Theorem 3.7, proved there by coarse graining from exponential
decay of the radius (Theorem 3.3). The notes write the bound as `exp(-c'_p n)` for every `n`; at
`n = 1` the left side is `1`, so this version carries a prefactor `C`. -/
public theorem cluster_volume_exp_decay (d : ℕ) (hd : 2 ≤ d) (p : ℝ≥0) (hp : p ≤ 1)
    (hlt : p < pc d) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          {ω | (n : ℕ∞) ≤ (cluster d ω (origin d)).encard} ≤ C * Real.exp (-c * n) := by
  obtain ⟨r, hr, hsmall⟩ := exists_scale p hp (by omega : 0 < d) hlt
  apply geometric_subseq_antitone_decay (f := fun n =>
    (bernoulliProductMeasure p hp).real (volumeEvent d n))
    (L := (2 * (2 * r) + 1) ^ d + 1) (r := (1 / 2 : ℝ)) (by omega) (by norm_num) (by norm_num)
  · intro m n h
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    exact (show (m : ℕ∞) ≤ n from Nat.cast_le.mpr h).trans hω
  · intro k
    exact (tour_bound p hp hr k).trans (pow_le_pow_left₀
      (mul_nonneg (by positivity) (crossProb_nonneg ..)) hsmall k)

end MathlibExt.Probability.Percolation.ClusterVolumeDecayWanted
