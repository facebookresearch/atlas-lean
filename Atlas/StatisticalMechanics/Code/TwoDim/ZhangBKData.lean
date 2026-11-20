/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.TwoDim.ZhangRotSymmetry
import Code.Walls.binsclosure
import Code.Universality.BXPAllAspect

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_atLeastTwo_halfMeasure_zero :
    halfMeasure (atLeastTwoInfinite 2) = 0 := by
  simpa [halfMeasure] using
    (bins_bk_unconditional (2⁻¹ : ℝ≥0) half_le_one (by norm_num) (by norm_num)).2.1


def zbd_boxHitsInfinite (n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | ∃ x : Site 2, x ∈ box 2 n ∧ (cluster 2 ω x).Infinite}

theorem zbd_boxHitsInfinite_isIncreasing (n : ℕ) : IsIncreasing (zbd_boxHitsInfinite n) := by
  intro ω ω' hle
  rintro ⟨x, hx, hinf⟩
  exact ⟨x, hx, hinf.mono (cluster_mono hle x)⟩

theorem zbd_boxHitsInfinite_measurableSet (n : ℕ) :
    MeasurableSet (zbd_boxHitsInfinite n) := by
  have heq : zbd_boxHitsInfinite n = ⋃ x : Site 2,
      if x ∈ box 2 n then {ω | (cluster 2 ω x).Infinite} else ∅ := by
    ext ω
    simp only [zbd_boxHitsInfinite, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ box 2 n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ box 2 n
  · simpa [hx] using (measurableSet_clusterInfinite (d := 2) x)
  · simp [hx]

theorem zbd_boxHitsInfinite_mono : Monotone zbd_boxHitsInfinite := by
  intro n m hnm ω
  rintro ⟨x, hx, hinf⟩
  refine ⟨x, ?_, hinf⟩
  rw [mem_box] at hx ⊢
  intro i
  exact le_trans (hx i) hnm


theorem zbd_iUnion_boxHitsInfinite :
    (⋃ n, zbd_boxHitsInfinite n) =
      {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} := by
  ext ω
  simp only [Set.mem_iUnion, zbd_boxHitsInfinite, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, x, _hx, hinf⟩
    exact ⟨x, hinf⟩
  · rintro ⟨x, hinf⟩
    have hxall : x ∈ ⋃ n, box 2 n := by rw [iUnion_box]; trivial
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hxall
    exact ⟨n, x, hx, hinf⟩



theorem zbd_existsInfinite_halfMeasure_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    halfMeasure {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2,
      (cluster 2 ω x).Infinite} = 1 := by
  have hbk := (bins_bk_unconditional (2⁻¹ : ℝ≥0) half_le_one
    (by norm_num) (by norm_num)).1
  rcases hbk with hzero | hone
  · have hsub : Universality.percolationEvent 2 ⊆
        {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = 0}ᶜ := by
      intro ω hω hcount
      have hmem : cluster 2 ω 0 ∈ infiniteClusters 2 ω := ⟨hω, 0, rfl⟩
      have hempty : infiniteClusters 2 ω = ∅ := by
        apply (Set.encard_eq_zero.mp ?_)
        simpa [numInfiniteClusters] using hcount
      simpa [hempty] using hmem
    have hnull : halfMeasure (Universality.percolationEvent 2) = 0 := by
      apply measure_mono_null hsub
      exact (prob_compl_eq_zero_iff (measurable_numInfiniteClusters
        (MeasurableSet.singleton 0))).2 hzero
    simp [Measure.real, hnull] at hpos
  · have hsub : {ω : ConfigSpace (Sym2 (Site 2)) | numInfiniteClusters 2 ω = 1} ⊆
        {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} := by
      intro ω hcount
      have hne : infiniteClusters 2 ω ≠ ∅ := by
        intro hempty
        have : numInfiniteClusters 2 ω = 0 := by simp [numInfiniteClusters, hempty]
        rw [hcount] at this
        norm_num at this
      obtain ⟨C, hC⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact ⟨hC.2.choose, hC.2.choose_spec ▸ hC.1⟩
    exact le_antisymm prob_le_one (hone ▸ measure_mono hsub)



theorem zbd_boxHit_rotated_union_tendsto
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n =>
      halfMeasure.real (zrs_sideFamily (zbd_boxHitsInfinite n) 0
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 1
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 2
        ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 3)) atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := halfMeasure) zbd_boxHitsInfinite_mono
  rw [zbd_iUnion_boxHitsInfinite, zbd_existsInfinite_halfMeasure_one hpos] at hmeasure
  have hreal : Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) := by
    exact (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).comp hmeasure
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hreal tendsto_const_nhds
  · intro n
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro ω hω
    exact Or.inl (Or.inl (Or.inl hω))
  · intro n
    exact measureReal_le_one











theorem zbd_connectedWithin_box_of_connected {d : ℕ}
    (omega : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hxy : Connected d omega x y) :
    ∃ n, ∃ (hx : x ∈ box d n) (hy : y ∈ box d n),
      ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩ := by
  rcases hxy with ⟨w⟩
  obtain ⟨n, hn⟩ := StatMech.Percolation.finite_subset_box
    ({z : Site d | z ∈ w.support}) w.support.finite_toSet
  have hx : x ∈ box d n := hn w.start_mem_support
  have hy : y ∈ box d n := hn w.end_mem_support
  exact ⟨n, hx, hy, ⟨w.induce (box d n) hn⟩⟩



def zbd_connectedWithinBox {d : ℕ} (x y : Site d) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | ∃ (hx : x ∈ box d n) (hy : y ∈ box d n),
    ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩}


theorem zbd_connectedWithinBox_subset_connected {d : ℕ} (x y : Site d) (n : ℕ) :
    zbd_connectedWithinBox x y n ⊆ {omega | Connected d omega x y} := by
  rintro omega ⟨_hx, _hy, hxy⟩
  exact hxy.connected


theorem zbd_iUnion_connectedWithinBox {d : ℕ} (x y : Site d) :
    (⋃ n, zbd_connectedWithinBox x y n) = {omega | Connected d omega x y} := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun n => zbd_connectedWithinBox_subset_connected x y n
  · intro omega hxy
    obtain ⟨n, hx, hy, hwithin⟩ := zbd_connectedWithin_box_of_connected omega hxy
    exact Set.mem_iUnion.mpr ⟨n, hx, hy, hwithin⟩


theorem zbd_measurableSet_connectedWithin {d : ℕ} (S : Set (Site d)) (x y : S) :
    MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) |
      ConnectedWithin d omega S x y} := by
  classical
  have hchain : ∀ l : List S,
      MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) |
        List.IsChain (openSubgraphInduce d omega S).Adj l} := by
    intro l
    induction l with
    | nil => simpa using (MeasurableSet.univ : MeasurableSet
        (Set.univ : Set (ConfigSpace (Sym2 (Site d)))))
    | cons a l ih =>
        cases l with
        | nil => simpa using (MeasurableSet.univ : MeasurableSet
            (Set.univ : Set (ConfigSpace (Sym2 (Site d)))))
        | cons b l' =>
            have heq :
                {omega : ConfigSpace (Sym2 (Site d)) |
                    List.IsChain (openSubgraphInduce d omega S).Adj (a :: b :: l')}
                  = {omega | (openSubgraph d omega).Adj (a : Site d) (b : Site d)} ∩
                    {omega | List.IsChain (openSubgraphInduce d omega S).Adj (b :: l')} := by
              ext omega
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.isChain_cons_cons,
                openSubgraphInduce_adj]
            rw [heq]
            exact (measurableSet_openAdj (a : Site d) (b : Site d)).inter ih
  have heq :
      {omega : ConfigSpace (Sym2 (Site d)) | ConnectedWithin d omega S x y} =
        ⋃ l : List S,
          ({omega | List.IsChain (openSubgraphInduce d omega S).Adj (x :: l)} ∩
            if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    unfold ConnectedWithin
    rw [SimpleGraph.reachable_iff_reflTransGen]
    constructor
    · intro h
      obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
      exact ⟨l, hl, by simp [hlast]⟩
    · rintro ⟨l, hl, hlast⟩
      have heqLast : (x :: l).getLast (List.cons_ne_nil _ _) = y := by
        by_contra hne
        simp [hne] at hlast
      exact List.relationReflTransGen_of_exists_isChain_cons l hl heqLast
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply (hchain (x :: l)).inter
  split_ifs
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

theorem zbd_connectedWithinBox_measurableSet {d : ℕ} (x y : Site d) (n : ℕ) :
    MeasurableSet (zbd_connectedWithinBox x y n) := by
  classical
  by_cases hx : x ∈ box d n
  · by_cases hy : y ∈ box d n
    · have heq : zbd_connectedWithinBox x y n =
          {omega | ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩} := by
        ext omega
        simp only [zbd_connectedWithinBox, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hx', hy', h⟩
          simpa using h
        · intro h
          exact ⟨hx, hy, h⟩
      rw [heq]
      exact zbd_measurableSet_connectedWithin (box d n) ⟨x, hx⟩ ⟨y, hy⟩
    · have : zbd_connectedWithinBox x y n = ∅ := by
        ext omega
        simp [zbd_connectedWithinBox, hy]
      rw [this]
      exact MeasurableSet.empty
  · have : zbd_connectedWithinBox x y n = ∅ := by
      ext omega
      simp [zbd_connectedWithinBox, hx]
    rw [this]
    exact MeasurableSet.empty


def zbd_sideHasInfinite {d : ℕ} (S : Set (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | ∃ x ∈ S, (cluster d omega x).Infinite}

theorem zbd_sideHasInfinite_measurableSet {d : ℕ} (S : Set (Site d)) :
    MeasurableSet (zbd_sideHasInfinite S) := by
  have heq : zbd_sideHasInfinite S =
      ⋃ x : Site d, ⋃ (_hx : x ∈ S), {omega | (cluster d omega x).Infinite} := by
    ext omega
    simp [zbd_sideHasInfinite]
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  exact measurableSet_clusterInfinite x

theorem zbd_sideHasInfinite_isIncreasing {d : ℕ} (S : Set (Site d)) :
    IsIncreasing (zbd_sideHasInfinite S) := by
  intro omega omega' hle
  rintro ⟨x, hxS, hxinf⟩
  exact ⟨x, hxS, hxinf.mono (cluster_mono hle x)⟩


def zbd_twoScaleMerge {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | ∃ x ∈ L, ∃ y ∈ R,
    (cluster d omega x).Infinite ∧ (cluster d omega y).Infinite ∧
      omega ∈ zbd_connectedWithinBox x y n}



def zbd_twoScaleError {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  (zbd_sideHasInfinite L ∩ zbd_sideHasInfinite R) \ zbd_twoScaleMerge L R n

theorem zbd_twoScaleMerge_measurableSet {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    MeasurableSet (zbd_twoScaleMerge L R n) := by
  have heq : zbd_twoScaleMerge L R n = ⋃ x : Site d, ⋃ (_hx : x ∈ L),
      ⋃ y : Site d, ⋃ (_hy : y ∈ R),
        ({omega | (cluster d omega x).Infinite} ∩
          {omega | (cluster d omega y).Infinite}) ∩ zbd_connectedWithinBox x y n := by
    ext omega
    constructor
    · rintro ⟨x, hxL, y, hyR, hxinf, hyinf, hconn⟩
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxL,
        Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyR, ⟨⟨hxinf, hyinf⟩, hconn⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
      obtain ⟨hxL, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyR, hrest⟩ := Set.mem_iUnion.mp hy
      exact ⟨x, hxL, y, hyR, hrest.1.1, hrest.1.2, hrest.2⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.iUnion
  intro hy
  exact ((measurableSet_clusterInfinite x).inter
    (measurableSet_clusterInfinite y)).inter (zbd_connectedWithinBox_measurableSet x y n)

theorem zbd_twoScaleError_measurableSet {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    MeasurableSet (zbd_twoScaleError L R n) :=
  ((zbd_sideHasInfinite_measurableSet L).inter
    (zbd_sideHasInfinite_measurableSet R)).diff
      (zbd_twoScaleMerge_measurableSet L R n)

theorem zbd_connectedWithinBox_mono {d : ℕ} (x y : Site d) :
    Monotone (zbd_connectedWithinBox x y) := by
  intro n m hnm omega
  rintro ⟨hx, hy, hxy⟩
  have hbox : box d n ⊆ box d m := by
    intro z hz
    rw [mem_box] at hz ⊢
    exact fun i => le_trans (hz i) hnm
  exact ⟨hbox hx, hbox hy,
    StatMech.RSW.Strip.connectedWithin_mono_set omega hbox hxy⟩

theorem zbd_twoScaleMerge_mono {d : ℕ} (L R : Set (Site d)) :
    Monotone (zbd_twoScaleMerge L R) := by
  intro n m hnm omega
  rintro ⟨x, hx, y, hy, hxinf, hyinf, hconn⟩
  exact ⟨x, hx, y, hy, hxinf, hyinf, zbd_connectedWithinBox_mono x y hnm hconn⟩

theorem zbd_twoScaleError_antitone {d : ℕ} (L R : Set (Site d)) :
    Antitone (zbd_twoScaleError L R) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm => herror.2 (zbd_twoScaleMerge_mono L R hnm hm)⟩



theorem zbd_iInter_twoScaleError_subset_atLeastTwo {d : ℕ} (L R : Set (Site d)) :
    (⋂ n, zbd_twoScaleError L R n) ⊆ atLeastTwoInfinite d := by
  intro omega herror
  have hcap := (Set.mem_iInter.mp herror 0).1
  obtain ⟨x, hxL, hxinf⟩ := hcap.1
  obtain ⟨y, hyR, hyinf⟩ := hcap.2
  have hnconn : ¬ Connected d omega x y := by
    intro hconn
    obtain ⟨n, hx, hy, hwithin⟩ := zbd_connectedWithin_box_of_connected omega hconn
    exact (Set.mem_iInter.mp herror n).2
      ⟨x, hxL, y, hyR, hxinf, hyinf, hx, hy, hwithin⟩
  have hcx : cluster d omega x ∈ infiniteClusters d omega := ⟨hxinf, x, rfl⟩
  have hcy : cluster d omega y ∈ infiniteClusters d omega := ⟨hyinf, y, rfl⟩
  have hcne : cluster d omega x ≠ cluster d omega y := by
    intro heq
    have : y ∈ cluster d omega x := heq ▸ self_mem_cluster omega y
    exact hnconn this
  have hnt : (infiniteClusters d omega).Nontrivial := ⟨_, hcx, _, hcy, hcne⟩
  have hone : (1 : ℕ∞) < (infiniteClusters d omega).encard :=
    Set.one_lt_encard_iff_nontrivial.mpr hnt
  show 2 ≤ numInfiniteClusters d omega
  rw [numInfiniteClusters, ← one_add_one_eq_two,
    ENat.add_one_le_iff ENat.one_ne_top]
  exact hone



theorem zbd_twoScaleError_tendsto_zero (L R : Set (Site 2)) :
    Tendsto (fun n => halfMeasure.real (zbd_twoScaleError L R n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => halfMeasure (zbd_twoScaleError L R n)) atTop
      (nhds (halfMeasure (⋂ n, zbd_twoScaleError L R n))) := tendsto_measure_iInter_atTop
    (μ := halfMeasure)
    (fun n => (zbd_twoScaleError_measurableSet L R n).nullMeasurableSet)
    (zbd_twoScaleError_antitone L R)
    ⟨0, measure_ne_top halfMeasure _⟩
  have hinter : halfMeasure (⋂ n, zbd_twoScaleError L R n) = 0 :=
    measure_mono_null (zbd_iInter_twoScaleError_subset_atLeastTwo L R)
      zbd_atLeastTwo_halfMeasure_zero
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim




theorem zbd_exists_diagonal_outerRadius
    (L R : ℕ → Set (Site 2)) :
    ∃ M : ℕ → ℕ, (∀ n, n + 1 ≤ M n) ∧
      Tendsto (fun n => halfMeasure.real (zbd_twoScaleError (L n) (R n) (M n)))
        atTop (nhds 0) := by
  have hex : ∀ n : ℕ, ∃ m : ℕ, n + 1 ≤ m ∧
      halfMeasure.real (zbd_twoScaleError (L n) (R n) m) <
        1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsmall : ∀ᶠ m : ℕ in atTop,
        halfMeasure.real (zbd_twoScaleError (L n) (R n) m) <
          1 / ((n : ℝ) + 1) :=
      (zbd_twoScaleError_tendsto_zero (L n) (R n)).eventually_lt_const hpos
    have hlarge : ∀ᶠ m : ℕ in atTop, n + 1 ≤ m := eventually_ge_atTop (n + 1)
    obtain ⟨m, hm, hmn⟩ := (hsmall.and hlarge).exists
    exact ⟨m, hmn, hm⟩
  choose M hMge hMsmall using hex
  refine ⟨M, hMge, ?_⟩
  have hupper : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => measureReal_nonneg) (fun n => (hMsmall n).le)


theorem zbd_twoScale_merge_cover {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    zbd_sideHasInfinite L ∩ zbd_sideHasInfinite R ⊆
      zbd_twoScaleMerge L R n ∪ zbd_twoScaleError L R n := by
  intro omega hcap
  by_cases hmerge : omega ∈ zbd_twoScaleMerge L R n
  · exact Or.inl hmerge
  · exact Or.inr ⟨hcap, hmerge⟩




theorem zbd_walk_first_hit_fn {omega : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 omega).Walk x y) (f : Site 2 → ℤ) (t : ℤ)
    (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
    (hx : f x < t) (hy : t ≤ f y) :
    ∃ j ≤ p.length, f (p.getVert j) = t ∧ ∀ m < j, f (p.getVert m) < t := by
  have hlen : t ≤ f (p.getVert p.length) := by rw [p.getVert_length]; exact hy
  classical
  let P : ℕ → Prop := fun m => t ≤ f (p.getVert m)
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : t ≤ f (p.getVert j) := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have hbelow : ∀ m < j, f (p.getVert m) < t := by
    intro m hm
    have hnot := Nat.find_min hPex hm
    simpa [P, not_le] using hnot
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : f (p.getVert k) < t := hbelow k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  rw [hk] at hjP
  have hdiff := hstep hadj.1
  have hle : f (p.getVert (k + 1)) ≤ t := by
    have habs : |f (p.getVert k) - f (p.getVert (k + 1))| ≤ 1 := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hdiff
    rw [abs_le] at habs
    omega
  refine ⟨k + 1, by omega, le_antisymm hle hjP, ?_⟩
  intro m hm
  exact hbelow m (by omega)



theorem zbd_connectedWithin_restrict_fn {omega : ConfigSpace (Sym2 (Site 2))}
    {S T : Set (Site 2)} {x y : Site 2} (hxS : x ∈ S) (hyS : y ∈ S)
    (h : ConnectedWithin 2 omega S ⟨x, hxS⟩ ⟨y, hyS⟩)
    (f : Site 2 → ℤ) (t : ℤ)
    (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
    (hx : f x < t) (hy : t ≤ f y)
    (hslab : ∀ z ∈ S, f z ≤ t → z ∈ T) :
    ∃ (u : Site 2) (_ : u ∈ S), f u = t ∧
      ∃ (huT : u ∈ T) (hxT : x ∈ T),
        ConnectedWithin 2 omega T ⟨x, hxT⟩ ⟨u, huT⟩ := by
  classical
  obtain ⟨w⟩ := h
  let p : (openSubgraph 2 omega).Walk x y :=
    w.map (SimpleGraph.Embedding.induce S).toHom
  have hpsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce S).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, _ha, rfl⟩ := hz'
    exact a.2
  obtain ⟨j, hjle, hju, hjbelow⟩ :=
    zbd_walk_first_hit_fn p f t hstep hx hy
  let u : Site 2 := p.getVert j
  have huS : u ∈ S := hpsupp u (p.getVert_mem_support j)
  let q : (openSubgraph 2 omega).Walk x u := p.take j
  have hcoord : ∀ n ≤ j, f (p.getVert n) ≤ t := by
    intro n hn
    rcases lt_or_eq_of_le hn with hnj | rfl
    · exact le_of_lt (hjbelow n hnj)
    · exact le_of_eq hju
  have hqsupp : ∀ z ∈ q.support, z ∈ T := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS : z ∈ S := hpsupp z hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hzm : z = p.getVert m := by
      have hmp : m ≤ p.length := le_trans hmle hjle
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmp]
    apply hslab z hzS
    rw [hzm]
    exact hcoord m hmle
  have hxT : x ∈ T := hqsupp x q.start_mem_support
  have huT : u ∈ T := hqsupp u q.end_mem_support
  exact ⟨u, huS, hju, huT, hxT, ⟨q.induce T hqsupp⟩⟩


def zbd_centeredLeftSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 0 = -(n : ℤ)}

def zbd_centeredRightSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 0 = (n : ℤ)}

def zbd_centeredBottomSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 1 = -(n : ℤ)}

def zbd_centeredTopSide (n : ℕ) : Set (Site 2) :=
  {x | x ∈ box 2 n ∧ x 1 = (n : ℤ)}



noncomputable def zbd_rotOpenIso (omega : ConfigSpace (Sym2 (Site 2))) :
    openSubgraph 2 (kdi_rotConfig omega) ≃g openSubgraph 2 omega where
  toEquiv := rot90Equiv.symm
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hadj, hopen⟩
      refine ⟨(rot90Iso.symm.map_rel_iff (a := x) (b := y)).mp hadj, ?_⟩
      simpa [zrs_rotConfig_apply, kdi_rotEdgeEquiv, StatMech.Lattice.sym2Congr] using hopen
    · rintro ⟨hadj, hopen⟩
      refine ⟨(rot90Iso.symm.map_rel_iff (a := x) (b := y)).mpr hadj, ?_⟩
      simpa [zrs_rotConfig_apply, kdi_rotEdgeEquiv, StatMech.Lattice.sym2Congr] using hopen

theorem zbd_rot_connected_iff (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    Connected 2 (kdi_rotConfig omega) x y ↔
      Connected 2 omega (rot90Inv x) (rot90Inv y) := by
  exact (zbd_rotOpenIso omega).reachable_iff.symm

theorem zbd_rot_clusterInfinite_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (x : Site 2) :
    (cluster 2 (kdi_rotConfig omega) x).Infinite ↔
      (cluster 2 omega (rot90Inv x)).Infinite := by
  let e : Site 2 ≃ Site 2 := rot90Equiv.symm
  have himage : e '' cluster 2 (kdi_rotConfig omega) x = cluster 2 omega (e x) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (zbd_rot_connected_iff omega x y).mp hy
    · intro hz
      refine ⟨rot90Equiv z, ?_, ?_⟩
      · apply (zbd_rot_connected_iff omega x (rot90Equiv z)).mpr
        have hez : e (rot90Equiv z) = z := Equiv.symm_apply_apply rot90Equiv z
        change Connected 2 omega (e x) (e (rot90Equiv z))
        rw [hez]
        exact hz
      · exact Equiv.symm_apply_apply rot90Equiv z
  change (cluster 2 (kdi_rotConfig omega) x).Infinite ↔
    (cluster 2 omega (e x)).Infinite
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem zbd_rotInv_sq (x : Site 2) : rot90Inv (rot90Inv x) = -x := by
  funext i
  fin_cases i <;> simp [rot90Inv]

theorem zbd_rotFun_sq (x : Site 2) : rot90Fun (rot90Fun x) = -x := by
  funext i
  fin_cases i <;> simp [rot90Fun]

theorem zbd_neg_mem_box (n : ℕ) {x : Site 2} (h : x ∈ box 2 n) : -x ∈ box 2 n := by
  rw [mem_box] at h ⊢
  intro i
  simpa using h i



theorem zbd_centered_opposite_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 =
      zbd_sideHasInfinite (zbd_centeredRightSide n) := by
  ext omega
  change kdi_rotConfig (kdi_rotConfig omega) ∈
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv (rot90Inv x), ?_, ?_⟩
    · rw [zbd_rotInv_sq]
      exact ⟨zbd_neg_mem_box n hx.1, by rw [Pi.neg_apply, hx.2]; simp⟩
    · exact (zbd_rot_clusterInfinite_iff omega (rot90Inv x)).mp
        ((zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) x).mp hinf)
  · rintro ⟨y, hy, hinf⟩
    let x := rot90Fun (rot90Fun y)
    have hix : rot90Inv (rot90Inv x) = y := by
      rw [zbd_rotInv_sq]
      dsimp [x]
      rw [zbd_rotFun_sq]
      simp
    refine ⟨x, ?_, ?_⟩
    · dsimp [x]
      rw [zbd_rotFun_sq]
      exact ⟨zbd_neg_mem_box n hy.1, by rw [Pi.neg_apply, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) x).mpr
      apply (zbd_rot_clusterInfinite_iff omega (rot90Inv x)).mpr
      rw [hix]
      exact hinf

theorem zbd_rotInv_cube (x : Site 2) :
    rot90Inv (rot90Inv (rot90Inv x)) = rot90Fun x := by
  funext i
  fin_cases i <;> simp [rot90Inv, rot90Fun]

theorem zbd_rotFun_cube (x : Site 2) :
    rot90Fun (rot90Fun (rot90Fun x)) = rot90Inv x := by
  funext i
  fin_cases i <;> simp [rot90Inv, rot90Fun]

theorem zbd_centered_top_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 =
      zbd_sideHasInfinite (zbd_centeredTopSide n) := by
  ext omega
  change kdi_rotConfig omega ∈ zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv x, ?_, (zbd_rot_clusterInfinite_iff omega x).mp hinf⟩
    exact ⟨rot90Inv_mem_box n hx.1, by simp [rot90Inv, hx.2]⟩
  · rintro ⟨y, hy, hinf⟩
    refine ⟨rot90Fun y, ?_, ?_⟩
    · exact ⟨rot90Fun_mem_box n hy.1, by simp [rot90Fun, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff omega (rot90Fun y)).mpr
      have hiy : rot90Inv (rot90Fun y) = y := Equiv.symm_apply_apply rot90Equiv y
      rw [hiy]
      exact hinf

theorem zbd_centered_bottom_rotation (n : ℕ) :
    zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3 =
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  ext omega
  change kdi_rotConfig (kdi_rotConfig (kdi_rotConfig omega)) ∈
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ↔ _
  constructor
  · rintro ⟨x, hx, hinf⟩
    refine ⟨rot90Inv (rot90Inv (rot90Inv x)), ?_, ?_⟩
    · rw [zbd_rotInv_cube]
      exact ⟨rot90Fun_mem_box n hx.1, by simp [rot90Fun, hx.2]⟩
    · exact (zbd_rot_clusterInfinite_iff omega (rot90Inv (rot90Inv x))).mp
        ((zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) (rot90Inv x)).mp
          ((zbd_rot_clusterInfinite_iff (kdi_rotConfig (kdi_rotConfig omega)) x).mp hinf))
  · rintro ⟨y, hy, hinf⟩
    let x := rot90Fun (rot90Fun (rot90Fun y))
    have hix : rot90Inv (rot90Inv (rot90Inv x)) = y := by
      rw [zbd_rotInv_cube]
      dsimp [x]
      rw [zbd_rotFun_cube]
      exact Equiv.symm_apply_apply rot90Equiv y
    refine ⟨x, ?_, ?_⟩
    · dsimp [x]
      rw [zbd_rotFun_cube]
      exact ⟨rot90Inv_mem_box n hy.1, by simp [rot90Inv, hy.2]⟩
    · apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig (kdi_rotConfig omega)) x).mpr
      apply (zbd_rot_clusterInfinite_iff (kdi_rotConfig omega) (rot90Inv x)).mpr
      apply (zbd_rot_clusterInfinite_iff omega (rot90Inv (rot90Inv x))).mpr
      rw [hix]
      exact hinf

theorem zbd_boundaryInfinite_mem_sideUnion (n : ℕ)
    {omega : ConfigSpace (Sym2 (Site 2))} {z : Site 2}
    (hzbox : z ∈ box 2 n) (hzinf : (cluster 2 omega z).Infinite)
    (hbd : ∃ i : Fin 2, (z i).natAbs = n) :
    omega ∈ zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪
      zbd_sideHasInfinite (zbd_centeredRightSide n) ∪
      zbd_sideHasInfinite (zbd_centeredTopSide n) ∪
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  obtain ⟨i, hi⟩ := hbd
  have hsign := Int.natAbs_eq (z i)
  fin_cases i
  · rcases hsign with hpos | hneg
    · change (z 0).natAbs = n at hi
      change z 0 = ((z 0).natAbs : ℤ) at hpos
      exact Or.inl (Or.inl (Or.inr ⟨z, ⟨hzbox, by rw [hpos, hi]⟩, hzinf⟩))
    · change (z 0).natAbs = n at hi
      change z 0 = -((z 0).natAbs : ℤ) at hneg
      exact Or.inl (Or.inl (Or.inl ⟨z, ⟨hzbox, by rw [hneg, hi]⟩, hzinf⟩))
  · rcases hsign with hpos | hneg
    · change (z 1).natAbs = n at hi
      change z 1 = ((z 1).natAbs : ℤ) at hpos
      exact Or.inl (Or.inr ⟨z, ⟨hzbox, by rw [hpos, hi]⟩, hzinf⟩)
    · change (z 1).natAbs = n at hi
      change z 1 = -((z 1).natAbs : ℤ) at hneg
      exact Or.inr ⟨z, ⟨hzbox, by rw [hneg, hi]⟩, hzinf⟩



theorem zbd_boxHitsInfinite_subset_centeredSideUnion (n : ℕ) :
    zbd_boxHitsInfinite n ⊆
      zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪
      zbd_sideHasInfinite (zbd_centeredRightSide n) ∪
      zbd_sideHasInfinite (zbd_centeredTopSide n) ∪
      zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
  intro omega
  rintro ⟨x, hxbox, hxinf⟩
  by_cases hxBoundary : ∃ i : Fin 2, (x i).natAbs = n
  · exact zbd_boundaryInfinite_mem_sideUnion n hxbox hxinf hxBoundary
  obtain ⟨y, hybox, hxy⟩ := (cluster_infinite_iff omega x).mp hxinf n
  rcases hxy with ⟨w⟩
  classical
  let P : ℕ → Prop := fun m => w.getVert m ∉ box 2 n
  have hPend : P w.length := by simpa [P] using hybox
  let j := Nat.find ⟨w.length, hPend⟩
  have hjP : w.getVert j ∉ box 2 n := Nat.find_spec ⟨w.length, hPend⟩
  have hjle : j ≤ w.length := Nat.find_le hPend
  have hj0 : j ≠ 0 := by
    intro hj
    rw [hj, w.getVert_zero] at hjP
    exact hjP hxbox
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hklt : k < w.length := by omega
  have hknotP : ¬ P k := Nat.find_min ⟨w.length, hPend⟩ (by omega)
  have hkbox : w.getVert k ∈ box 2 n := by simpa [P] using hknotP
  have hnextOutside : w.getVert (k + 1) ∉ box 2 n := by simpa [hk] using hjP
  have hadj := w.adj_getVert_succ hklt
  rw [mem_box] at hnextOutside
  push Not at hnextOutside
  obtain ⟨i, hiOutside⟩ := hnextOutside
  have hpredLe : ((w.getVert k) i).natAbs ≤ n := by
    rw [mem_box] at hkbox
    exact hkbox i
  have hdiff : (((w.getVert (k + 1)) i) - ((w.getVert k) i)).natAbs ≤ 1 := by
    have h := bxa_adj_coord_diff_le hadj.1 i
    rw [show (w.getVert (k + 1)) i - (w.getVert k) i =
      -((w.getVert k) i - (w.getVert (k + 1)) i) by ring, Int.natAbs_neg]
    exact h
  have htri : ((w.getVert (k + 1)) i).natAbs ≤
      (((w.getVert (k + 1)) i) - ((w.getVert k) i)).natAbs +
        ((w.getVert k) i).natAbs := by
    have h := Int.natAbs_add_le
      (((w.getVert (k + 1)) i) - ((w.getVert k) i)) ((w.getVert k) i)
    rw [show ((w.getVert (k + 1)) i - (w.getVert k) i) + (w.getVert k) i =
      (w.getVert (k + 1)) i by ring] at h
    exact h
  have hpredEq : ((w.getVert k) i).natAbs = n := by omega
  have hxz : Connected 2 omega x (w.getVert k) := ⟨w.take k⟩
  have hzinf : (cluster 2 omega (w.getVert k)).Infinite := by
    rw [← cluster_eq_of_connected hxz]
    exact hxinf
  exact zbd_boundaryInfinite_mem_sideUnion n hkbox hzinf ⟨i, hpredEq⟩

theorem zbd_boxHitsInfinite_tendsto_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := halfMeasure) zbd_boxHitsInfinite_mono
  rw [zbd_iUnion_boxHitsInfinite, zbd_existsInfinite_halfMeasure_one hpos] at hmeasure
  exact (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).comp hmeasure



theorem zbd_centeredSide_union_tendsto
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto (fun n =>
      halfMeasure.real
        (zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 0 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 ∪
          zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3))
      atTop (nhds 1) := by
  have hlower := zbd_boxHitsInfinite_tendsto_one hpos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    apply measureReal_mono (h₂ := measure_ne_top halfMeasure _)
    simpa [zbd_centered_opposite_rotation n, zbd_centered_top_rotation n,
      zbd_centered_bottom_rotation n] using
        (zbd_boxHitsInfinite_subset_centeredSideUnion n)
  · intro n
    exact measureReal_le_one

theorem zbd_natAbs_le_iff (x : ℤ) (n : ℕ) :
    x.natAbs ≤ n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
  rw [show x.natAbs ≤ n ↔ |x| ≤ (n : ℤ) from by
    rw [Int.abs_eq_natAbs]
    exact Int.ofNat_le.symm]
  exact abs_le

theorem zbd_mem_box_iff_rect (n : ℕ) (x : Site 2) :
    x ∈ box 2 n ↔ x ∈ StatMech.RSW.Box.rect (-(n : ℤ)) n (-(n : ℤ)) n := by
  rw [mem_box, StatMech.RSW.Box.mem_rect]
  constructor
  · intro h
    have h0 : -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n := (zbd_natAbs_le_iff (x 0) n).mp (h 0)
    have h1 : -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := (zbd_natAbs_le_iff (x 1) n).mp (h 1)
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  · rintro ⟨h0l, h0r, h1l, h1r⟩ i
    fin_cases i
    · exact (zbd_natAbs_le_iff (x 0) n).mpr ⟨h0l, h0r⟩
    · exact (zbd_natAbs_le_iff (x 1) n).mpr ⟨h1l, h1r⟩



theorem zbd_horizontalCrossing_of_centeredSide_connection
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M)
    {omega : ConfigSpace (Sym2 (Site 2))}
    {x y : Site 2} (hx : x ∈ zbd_centeredLeftSide n)
    (hy : y ∈ zbd_centeredRightSide n)
    (hconn : ConnectedWithin 2 omega (box 2 M)
      ⟨x, by exact box_mono 2 hnM hx.1⟩ ⟨y, by exact box_mono 2 hnM hy.1⟩) :
    StatMech.RSW.Box.HorizontalCrossing omega (-(n : ℤ)) n (-(M : ℤ)) M := by
  let S : Set (Site 2) := box 2 M
  let T1 : Set (Site 2) := {z | z ∈ S ∧ z 0 ≤ (n : ℤ)}
  have hxS : x ∈ S := box_mono 2 hnM hx.1
  have hyS : y ∈ S := box_mono 2 hnM hy.1
  obtain ⟨u, huS, hu0, huT1, hxT1, hxu⟩ :=
    bxa_connectedWithin_restrict (S := S) (T := T1) hxS hyS hconn 0 (n : ℤ)
      (by rw [hx.2]; omega) (by rw [hy.2])
      (fun z hz hzn => ⟨hz, hzn⟩)
  let T : Set (Site 2) := StatMech.RSW.Box.rect (-(n : ℤ)) n (-(M : ℤ)) M
  have hnegStep : ∀ {a b : Site 2}, (hypercubicLattice 2).Adj a b →
      ((-a 0) - (-b 0)).natAbs ≤ 1 := by
    intro a b hab
    rw [show (-a 0) - (-b 0) = -(a 0 - b 0) by ring, Int.natAbs_neg]
    exact bxa_adj_coord_diff_le hab 0
  obtain ⟨v, hvT1, hv0, hvT, huT, huv⟩ :=
    zbd_connectedWithin_restrict_fn (S := T1) (T := T) huT1 hxT1 hxu.symm
      (fun z => -z 0) (n : ℤ) hnegStep
      (by change -u 0 < (n : ℤ); rw [hu0]; omega)
      (by change (n : ℤ) ≤ -x 0; rw [hx.2]; omega)
      (fun z hz hza => by
        have hzbox : z ∈ box 2 M := hz.1
        have hzrect := (zbd_mem_box_iff_rect M z).mp hzbox
        rw [StatMech.RSW.Box.mem_rect] at hzrect ⊢
        constructor
        · change -z 0 ≤ (n : ℤ) at hza
          omega
        · exact ⟨hz.2, hzrect.2.2.1, hzrect.2.2.2⟩)
  refine ⟨⟨v, ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hvT, by change v 0 = -(n : ℤ); omega⟩
  · exact ⟨huT, hu0⟩
  · simpa [T] using huv.symm



theorem zbd_centeredMerge_subset_horizontalCrossing
    (n M : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
    zbd_twoScaleMerge (zbd_centeredLeftSide n) (zbd_centeredRightSide n) M ⊆
      StatMech.RSW.Box.horizontalCrossingEvent (-(n : ℤ)) n (-(M : ℤ)) M := by
  rintro omega ⟨x, hx, y, hy, _hxinf, _hyinf, hconn⟩
  obtain ⟨hxM, hyM, hwithin⟩ := hconn
  apply zbd_horizontalCrossing_of_centeredSide_connection n M hn hnM hx hy
  simpa using hwithin






def zbd_geometricData_of_twoScale
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (L R : ℕ → Set (Site 2)) (M : ℕ → ℕ)
    (hbaseInc : ∀ n, IsIncreasing (zbd_sideHasInfinite (L n)))
    (hbaseM : ∀ n, MeasurableSet (zbd_sideHasInfinite (L n)))
    (hopp : ∀ n,
      zrs_sideFamily (zbd_sideHasInfinite (L n)) 1 = zbd_sideHasInfinite (R n))
    (herr : Tendsto (fun n =>
      halfMeasure.real (zbd_twoScaleError (L n) (R n) (M n))) atTop (nhds 0))
    (hunion : Tendsto (fun n =>
      halfMeasure.real
        (zrs_sideFamily (zbd_sideHasInfinite (L n)) 0 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 1 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 2 ∪
          zrs_sideFamily (zbd_sideHasInfinite (L n)) 3)) atTop (nhds 1))
    (hcross : ∀ n, zbd_twoScaleMerge (L n) (R n) (M n) ⊆ A n ∪ B n) :
    ZhangGeometricData halfMeasure A B := by
  apply zrs_geometricData_of_remaining
    (fun n => zbd_sideHasInfinite (L n))
    (fun n => zbd_twoScaleError (L n) (R n) (M n))
    hbaseInc hbaseM herr hunion
  intro n omega hcap
  have hcap' : omega ∈ zbd_sideHasInfinite (L n) ∩ zbd_sideHasInfinite (R n) := by
    simpa [hopp n] using hcap
  rcases zbd_twoScale_merge_cover (L n) (R n) (M n) hcap' with hmerge | herror
  · exact Or.inl (hcross n hmerge)
  · exact Or.inr herror

end StatMech.TwoDim
