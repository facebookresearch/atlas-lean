/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.BXPFromRSW
public import MathlibExt.Probability.Percolation.Universality.CrossingReflection

/-!
# The box-crossing property at `p = 1/2` for every aspect ratio

Crossing a wider rectangle left–right forces crossing every narrower one with the same left side
(`bxa_horizontalCrossing_mono_width`; similarly for heights), so the bound for the integer aspect
ratio `k₀ = max 2 ⌈ρ⌉` gives the box-crossing property for every real `ρ > 1`.

`bxa_boxCrossingProperty_all_of_rsw` is the version with measurability, reflection and the square
bound discharged. Its remaining hypotheses are positive association of `ℙ_{1/2}` (`hpa`; not proved
in Atlas for the infinite product measure), the Russo–Seymour–Welsh bound `γ` on crossings of
`[0, 2n] × [0, n]` (`h2box`), and the bound `1/2` on vertical crossings of `n × n` squares
(`hband`; true by self-duality, not proved here).

## Main results

* `StatMech.Universality.bxa_connectedWithin_restrict`: an open path from `{x_i < t}` to
  `{x_i ≥ t}` first hits `{x_i = t}` along a path staying in `{x_i ≤ t}`.
* `StatMech.Universality.bxa_horizontalCrossing_mono_width`,
  `StatMech.Universality.bxa_verticalCrossing_mono_height`.
* `StatMech.Universality.bxa_boxCrossingProperty_all`,
  `StatMech.Universality.bxa_boxCrossingProperty_all_of_rsw`.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
-/

@[expose] public section

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip

/-- Lattice neighbours differ by at most `1` in every coordinate. -/
theorem bxa_adj_coord_diff_le {d : ℕ} {x y : Site d}
    (h : (hypercubicLattice d).Adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  rw [hypercubicLattice_adj] at h
  calc (x i - y i).natAbs
      ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = 1 := h

/-- An open walk from `x_i < t` to `y_i ≥ t` has a first vertex with `i`-th coordinate `t`. -/
theorem bxa_walk_first_hit {ω : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 ω).Walk x y) (i : Fin 2) (t : ℤ)
    (hx : x i < t) (hy : t ≤ y i) :
    ∃ j ≤ p.length, (p.getVert j) i = t ∧ ∀ m < j, (p.getVert m) i < t := by
  have hlen : t ≤ (p.getVert p.length) i := by rw [p.getVert_length]; exact hy
  classical
  let P : ℕ → Prop := fun m => t ≤ (p.getVert m) i
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : t ≤ (p.getVert j) i := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have hbelow : ∀ m < j, (p.getVert m) i < t := by
    intro m hm
    have := Nat.find_min hPex hm
    simpa [P, not_le] using this
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact absurd hjP (not_le.2 hx)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : (p.getVert k) i < t := hbelow k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  rw [hk] at hjP
  have hadj' : (hypercubicLattice 2).Adj (p.getVert k) (p.getVert (k + 1)) := hadj.1
  have hdiff := bxa_adj_coord_diff_le hadj' i
  have hle : (p.getVert (k + 1)) i ≤ t := by
    have habs : ((p.getVert k) i - (p.getVert (k + 1)) i).natAbs ≤ 1 := hdiff
    have hb : |(p.getVert k) i - (p.getVert (k + 1)) i| ≤ 1 := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast habs
    rw [abs_le] at hb
    omega
  have hjP' : t ≤ (p.getVert (k + 1)) i := hjP
  refine ⟨k + 1, by omega, le_antisymm hle hjP', ?_⟩
  intro m hm
  exact hbelow m (by omega)

/-- If `x` and `y` are connected inside `S` with `x_i < t ≤ y_i`, then `x` is connected inside `T`
to a vertex `u ∈ S` with `u_i = t`, provided `T` contains the points of `S` with `i`-th
coordinate at most `t`. -/
theorem bxa_connectedWithin_restrict {ω : ConfigSpace (Sym2 (Site 2))}
    {S T : Set (Site 2)} {x y : Site 2} (hxS : x ∈ S) (hyS : y ∈ S)
    (h : ConnectedWithin 2 ω S ⟨x, hxS⟩ ⟨y, hyS⟩)
    (i : Fin 2) (t : ℤ) (hx : x i < t) (hy : t ≤ y i)
    (hslab : ∀ z ∈ S, z i ≤ t → z ∈ T) :
    ∃ (u : Site 2) (_ : u ∈ S), u i = t ∧
      ∃ (huT : u ∈ T) (hxT : x ∈ T),
        ConnectedWithin 2 ω T ⟨x, hxT⟩ ⟨u, huT⟩ := by
  classical
  obtain ⟨w⟩ := h
  let p : (openSubgraph 2 ω).Walk x y :=
    (w.map (SimpleGraph.Embedding.induce S).toHom)
  have hpsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce S).toHom).support := hz
    erw [SimpleGraph.Walk.support_map] at hz'; simp only [List.mem_map] at hz'
    obtain ⟨a, _, rfl⟩ := hz'
    exact a.2
  obtain ⟨j, hjle, hju, hjbelow⟩ := bxa_walk_first_hit p i t hx hy
  set u : Site 2 := p.getVert j with hu_def
  have huS : u ∈ S := hpsupp u (p.getVert_mem_support j)
  let q : (openSubgraph 2 ω).Walk x u := p.take j
  have hcoord : ∀ n ≤ j, (p.getVert n) i ≤ t := by
    intro n hn
    rcases lt_or_eq_of_le hn with hnj | hnj
    · exact le_of_lt (hjbelow n hnj)
    · rw [hnj]; exact le_of_eq hju
  have hqsupp : ∀ z ∈ q.support, z ∈ T := by
    intro z hz
    rw [SimpleGraph.Walk.support_take] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS : z ∈ S := hpsupp z hzp
    obtain ⟨n, hzn, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hzm : z = p.getVert m := by
      have hjm : m ≤ p.length := le_trans hmle hjle
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hjm]
    have hzi : z i ≤ t := by rw [hzm]; exact hcoord m hmle
    exact hslab z hzS hzi
  have hxT : x ∈ T := hqsupp x q.start_mem_support
  have huT : u ∈ T := hqsupp u q.end_mem_support
  refine ⟨u, huS, hju, huT, hxT, ?_⟩
  exact ⟨q.induce T hqsupp⟩

/-- A left–right crossing of `[0, a'] × [0, b]` contains one of `[0, a] × [0, b]` for `0 < a ≤ a'`.
-/
theorem bxa_horizontalCrossing_mono_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a')
    {ω : ConfigSpace (Sym2 (Site 2))} (h : HorizontalCrossing ω 0 a' 0 b) :
    HorizontalCrossing ω 0 a 0 b := by
  obtain ⟨xl, yr, hconn⟩ := h
  have hxl0 : (xl : Site 2) 0 = 0 := xl.2.2
  have hyr0 : (yr : Site 2) 0 = a' := yr.2.2
  have hxlS : (xl : Site 2) ∈ rect 0 a' 0 b := leftSide_subset xl.2
  have hyrS : (yr : Site 2) ∈ rect 0 a' 0 b := rightSide_subset yr.2
  obtain ⟨u, _, hu0, huT, hxT, hconn'⟩ :=
    bxa_connectedWithin_restrict hxlS hyrS hconn 0 a (by rw [hxl0]; exact ha)
      (by rw [hyr0]; exact haa')
      (fun z hz hzle => by
        rw [mem_rect] at hz ⊢
        exact ⟨hz.1, hzle, hz.2.2.1, hz.2.2.2⟩)
  refine ⟨⟨(xl : Site 2), ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hxT, hxl0⟩
  · exact ⟨huT, hu0⟩
  · exact hconn'

/-- A bottom–top crossing of `[0, a] × [0, d']` contains one of `[0, a] × [0, d]` for `0 < d ≤ d'`.
-/
theorem bxa_verticalCrossing_mono_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d')
    {ω : ConfigSpace (Sym2 (Site 2))} (h : VerticalCrossing ω 0 a 0 d') :
    VerticalCrossing ω 0 a 0 d := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxb1 : (xb : Site 2) 1 = 0 := xb.2.2
  have hyt1 : (yt : Site 2) 1 = d' := yt.2.2
  have hxbS : (xb : Site 2) ∈ rect 0 a 0 d' := bottomSide_subset xb.2
  have hytS : (yt : Site 2) ∈ rect 0 a 0 d' := topSide_subset yt.2
  obtain ⟨u, _, hu1, huT, hxT, hconn'⟩ :=
    bxa_connectedWithin_restrict hxbS hytS hconn 1 d (by rw [hxb1]; exact hd)
      (by rw [hyt1]; exact hdd')
      (fun z hz hzle => by
        rw [mem_rect] at hz ⊢
        exact ⟨hz.1, hz.2.1, hz.2.2.1, hzle⟩)
  refine ⟨⟨(xb : Site 2), ?_⟩, ⟨u, ?_⟩, ?_⟩
  · exact ⟨hxT, hxb1⟩
  · exact ⟨huT, hu1⟩
  · exact hconn'

/-- Event form of `bxa_horizontalCrossing_mono_width`. -/
theorem bxa_horizontalCrossingEvent_subset_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a') :
    horizontalCrossingEvent 0 a' 0 b ⊆ horizontalCrossingEvent 0 a 0 b :=
  fun _ hω => bxa_horizontalCrossing_mono_width ha haa' hω

/-- Event form of `bxa_verticalCrossing_mono_height`. -/
theorem bxa_verticalCrossingEvent_subset_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d') :
    verticalCrossingEvent 0 a 0 d' ⊆ verticalCrossingEvent 0 a 0 d :=
  fun _ hω => bxa_verticalCrossing_mono_height hd hdd' hω

/-- Probability form of `bxa_horizontalCrossing_mono_width` under `ℙ_{1/2}`. -/
theorem bxa_horizontalCrossing_real_mono_width {a a' b : ℤ} (ha : 0 < a) (haa' : a ≤ a') :
    halfMeasure.real (horizontalCrossingEvent 0 a' 0 b)
      ≤ halfMeasure.real (horizontalCrossingEvent 0 a 0 b) :=
  measureReal_mono (bxa_horizontalCrossingEvent_subset_width ha haa')

/-- Probability form of `bxa_verticalCrossing_mono_height` under `ℙ_{1/2}`. -/
theorem bxa_verticalCrossing_real_mono_height {a d d' : ℤ} (hd : 0 < d) (hdd' : d ≤ d') :
    halfMeasure.real (verticalCrossingEvent 0 a 0 d')
      ≤ halfMeasure.real (verticalCrossingEvent 0 a 0 d) :=
  measureReal_mono (bxa_verticalCrossingEvent_subset_height hd hdd')

/-- `⌊ρn⌋ ≤ k₀ n` when `ρ ≤ k₀`. -/
theorem bxa_floor_le_natMul {ρ : ℝ} {k0 : ℕ} (hρk0 : ρ ≤ (k0 : ℝ)) (n : ℕ) :
    ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := by
  have hmul : ρ * (n : ℝ) ≤ (k0 : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hρk0 (by positivity)
  calc ⌊ρ * (n : ℝ)⌋ ≤ ⌊(k0 : ℝ) * (n : ℝ)⌋ := Int.floor_le_floor hmul
    _ = (k0 : ℤ) * (n : ℤ) := bxr_floor_natMul k0 n

/-- `0 < ⌊ρn⌋` when `ρ > 1` and `n ≥ 1`. -/
theorem bxa_zero_lt_floor {ρ : ℝ} (hρ : 1 < ρ) {n : ℕ} (hn : 1 ≤ n) :
    (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ ρ * (n : ℝ) := by nlinarith [le_of_lt hρ]
  have : (1 : ℤ) ≤ ⌊ρ * (n : ℝ)⌋ := by
    rw [Int.le_floor]; exact_mod_cast h1
  omega

/-- The box-crossing property of `ℙ_{1/2}` for every aspect ratio `ρ > 1`, conditional on positive
association, a square bound `β`, the RSW bound `γ` on `2n × n` crossings, the band bound `1/2`,
measurability and the reflection identity. See `bxa_boxCrossingProperty_all_of_rsw` for the form
with the provable hypotheses discharged. -/
theorem bxa_boxCrossingProperty_all
    (hpa : PositivelyAssociated halfMeasure)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross halfMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      halfMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty halfMeasure ρ := by
  intro ρ hρ
  set k0 : ℕ := max 2 ⌈ρ⌉₊ with hk0_def
  have hk0 : 2 ≤ k0 := Nat.le_max_left 2 ⌈ρ⌉₊
  have hρk0 : ρ ≤ (k0 : ℝ) := by
    have h1 : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
    have h2 : (⌈ρ⌉₊ : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast Nat.le_max_right 2 ⌈ρ⌉₊
    linarith
  have hk1 : 1 ≤ k0 := le_trans (by norm_num) hk0
  set c : ℝ := β * ((1 / 2) * γ) ^ (k0 - 1) with hc_def
  have hc : (0 : ℝ) < c := by rw [hc_def]; positivity
  have hbase : ∀ n : ℤ, 0 < n →
      c ≤ halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) := by
    intro n hn
    have := rai_cross_lb halfMeasure hpa hn hβ hγ (hseed n hn)
      (cti_h2box_discharge (hmeas2box n hn) (h2box n hn))
      (cti_hband_discharge (hmeasband n hn) (hband n hn)) k0 hk1
    rwa [rai_cross_def] at this
  refine rba_bxp_of_uniform_seed halfMeasure ρ hρ 1 c hc ?_ ?_
  · intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfloor_pos : (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := bxa_zero_lt_floor hρ hn1
    have hfloor_le : ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := bxa_floor_le_natMul hρk0 n
    rw [bxr_translatedHorizontalCrossing_invariant τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)
        (hmeasGenH ⌊ρ * (n : ℝ)⌋ (n : ℤ) hfloor_pos hn)]
    calc c ≤ halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
          hbase (n : ℤ) hn
      _ ≤ halfMeasure.real (horizontalCrossingEvent 0 ⌊ρ * (n : ℝ)⌋ 0 (n : ℤ)) :=
          bxa_horizontalCrossing_real_mono_width hfloor_pos hfloor_le
  · intro n τ hn1
    have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
    have hfloor_pos : (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := bxa_zero_lt_floor hρ hn1
    have hfloor_le : ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := bxa_floor_le_natMul hρk0 n
    rw [bxr_translatedVerticalCrossing_invariant τ (n : ℤ) ⌊ρ * (n : ℝ)⌋
        (hmeasGenV (n : ℤ) ⌊ρ * (n : ℝ)⌋ hn hfloor_pos)]
    calc c ≤ halfMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
          hbase (n : ℤ) hn
      _ = halfMeasure.real (verticalCrossingEvent 0 (n : ℤ) 0 ((k0 : ℤ) * n)) :=
          (hrefl k0 hk0 (n : ℤ) hn).symm
      _ ≤ halfMeasure.real (verticalCrossingEvent 0 (n : ℤ) 0 ⌊ρ * (n : ℝ)⌋) :=
          bxa_verticalCrossing_real_mono_height hfloor_pos hfloor_le

/-- The box-crossing property of `ℙ_{1/2}` for every aspect ratio `ρ > 1` from positive association,
the Russo–Seymour–Welsh bound `γ ≤ ℙ_{1/2}(H[0, 2n] × [0, n])` for all `n > 0`, and the bound
`1/2 ≤ ℙ_{1/2}(V[0, n]²)`. These three are hypotheses; measurability, reflection and the square
bound are discharged. -/
theorem bxa_boxCrossingProperty_all_of_rsw
    (hpa : PositivelyAssociated halfMeasure) {γ : ℝ} (hγ : 0 < γ)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ halfMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ halfMeasure.real (verticalCrossingEvent 0 n 0 n)) :
    ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty halfMeasure ρ := by
  have hseed : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rai_cross halfMeasure n 1 := by
    intro n hn
    rw [rai_cross_def, Nat.cast_one, one_mul,
      ← crf_verticalCrossing_eq_horizontal_swap 0 n 0 n
        (measurableSet_horizontalCrossingEvent 0 n 0 n)]
    exact hband n hn
  exact bxa_boxCrossingProperty_all hpa (by norm_num) hγ
    (fun n _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun n _ => measurableSet_verticalCrossingEvent _ _ _ _)
    (fun a b _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)
    (fun a b _ _ => measurableSet_verticalCrossingEvent _ _ _ _)
    hseed h2box hband
    (crf_hrefl fun _ _ _ _ => measurableSet_horizontalCrossingEvent _ _ _ _)

end Universality

end StatMech
