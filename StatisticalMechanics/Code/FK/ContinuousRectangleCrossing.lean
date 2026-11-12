/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.StraightWalk

open Set SimpleGraph Topology
open scoped unitInterval

namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


noncomputable def gridEmbed (n : ℕ) (z : Site 2) : Fin 2 → ℝ :=
  fun i => (z i : ℝ) / n


noncomputable def gridFloor (n : ℕ) (p : Fin 2 → ℝ) : Site 2 :=
  fun i => ⌊(n : ℝ) * p i⌋

theorem site_eq_vec (z : Site 2) : z = ![z 0, z 1] := by
  funext i
  fin_cases i <;> rfl


noncomputable def gridConnector (x y : Site 2) :
    (hypercubicLattice 2).Walk x y :=
  (sw_lshape (x 0) (x 1) (y 0) (y 1)).copy
    (site_eq_vec x).symm (site_eq_vec y).symm

theorem gridConnector_mem_support (x y z : Site 2) :
    z ∈ (gridConnector x y).support ↔
      (∃ t : ℤ, t ∈ Set.uIcc (x 0) (y 0) ∧ z = ![t, x 1]) ∨
      (∃ t : ℤ, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![y 0, t]) := by
  rw [gridConnector, Walk.support_copy, sw_lshape_support_eq]


noncomputable def gridWalk (g : ℕ → Site 2) :
    (n : ℕ) → (hypercubicLattice 2).Walk (g 0) (g n)
  | 0 => Walk.nil
  | n + 1 => (gridWalk g n).append (gridConnector (g n) (g (n + 1)))

@[simp] theorem gridWalk_zero (g : ℕ → Site 2) :
    gridWalk g 0 = Walk.nil := rfl

@[simp] theorem gridWalk_succ (g : ℕ → Site 2) (n : ℕ) :
    gridWalk g (n + 1) =
      (gridWalk g n).append (gridConnector (g n) (g (n + 1))) := rfl



theorem gridWalk_mem_support_cases (g : ℕ → Site 2) (n : ℕ) (z : Site 2)
    (hz : z ∈ (gridWalk g n).support) :
    z = g 0 ∨ ∃ k < n, z ∈ (gridConnector (g k) (g (k + 1))).support := by
  induction n with
  | zero =>
      left
      simpa using hz
  | succ n ih =>
      rw [gridWalk_succ, Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · rcases ih hz with h | ⟨k, hk, hzk⟩
        · exact Or.inl h
        · exact Or.inr ⟨k, hk.trans (Nat.lt_succ_self n), hzk⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hz⟩


noncomputable def sampleTime (N k : ℕ) (hk : k ≤ N) (hN : 0 < N) : unitInterval :=
  ⟨(k : ℝ) / N, by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 (by exact_mod_cast hk)⟩

@[simp] theorem sampleTime_zero (N : ℕ) (hN : 0 < N) :
    sampleTime N 0 (Nat.zero_le N) hN = 0 := by
  ext
  simp [sampleTime]

@[simp] theorem sampleTime_self (N : ℕ) (hN : 0 < N) :
    sampleTime N N (le_refl N) hN = 1 := by
  ext
  simp [sampleTime, hN.ne']

theorem dist_sampleTime_succ (N k : ℕ) (hk : k < N) (hN : 0 < N) :
    dist (sampleTime N k hk.le hN)
        (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN) = 1 / (N : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp only [sampleTime]
  rw [abs_of_nonpos]
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    push_cast
    ring
  · have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [sub_nonpos, div_le_div_iff_of_pos_right hNr]
    exact_mod_cast Nat.le_succ k


def InUnitSquare (p : Fin 2 → ℝ) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ 1

theorem gridFloor_coord_nonneg {n : ℕ} {p : Fin 2 → ℝ}
    (hp : InUnitSquare p) (i : Fin 2) :
    0 ≤ gridFloor n p i := by
  rw [gridFloor, Int.floor_nonneg]
  exact mul_nonneg (Nat.cast_nonneg _) (hp i).1

theorem gridFloor_coord_le {n : ℕ} {p : Fin 2 → ℝ}
    (hp : InUnitSquare p) (i : Fin 2) :
    gridFloor n p i ≤ (n : ℤ) := by
  change ⌊(n : ℝ) * p i⌋ ≤ (n : ℤ)
  rw [Int.floor_le_iff]
  have := mul_le_mul_of_nonneg_left (hp i).2 (Nat.cast_nonneg n)
  norm_num at this ⊢
  linarith


theorem gridFloor_error {n : ℕ} (hn : 0 < n) (p : Fin 2 → ℝ) (i : Fin 2) :
    |gridEmbed n (gridFloor n p) i - p i| < 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : ((gridFloor n p i : ℤ) : ℝ) ≤ (n : ℝ) * p i := by
    exact Int.floor_le _
  have hhi : (n : ℝ) * p i < ((gridFloor n p i : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hpdiv : p i = ((n : ℝ) * p i) / n := by
    field_simp
  rw [abs_lt]
  simp only [gridEmbed]
  rw [hpdiv, ← sub_div]
  constructor
  · rw [← neg_div, div_lt_div_iff_of_pos_right hnR]
    linarith
  · rw [div_lt_div_iff_of_pos_right hnR]
    linarith

theorem abs_lt_of_mem_uIcc {a b t x e : ℝ} (ht : t ∈ Set.uIcc a b)
    (ha : |a - x| < e) (hb : |b - x| < e) : |t - x| < e := by
  rw [Set.mem_uIcc] at ht
  rw [abs_lt] at ha hb ⊢
  rcases ht with ht | ht <;> constructor <;> linarith

theorem div_mem_uIcc_of_int_mem {n : ℕ} (hn : 0 < n) {a b t : ℤ}
    (ht : t ∈ Set.uIcc a b) :
    (t : ℝ) / n ∈ Set.uIcc ((a : ℝ) / n) ((b : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Set.mem_uIcc] at ht ⊢
  rcases ht with ht | ht
  · left
    constructor
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.1
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.2
  · right
    constructor
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.1
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.2

theorem gridFloor_other_error {n : ℕ} (hn : 0 < n)
    {p q : Fin 2 → ℝ} {i : Fin 2}
    (hpq : |p i - q i| < 1 / (n : ℝ)) :
    |gridEmbed n (gridFloor n q) i - p i| < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := gridFloor_error hn q i
  rw [abs_lt] at hpq hq
  rw [abs_lt]
  constructor <;> rw [div_eq_mul_inv] at hpq hq ⊢ <;>
    linarith [inv_pos.mpr hnR]



theorem gridConnector_near {n : ℕ} (hn : 0 < n)
    {p q : Fin 2 → ℝ}
    (hpq : dist p q < 1 / (n : ℝ))
    {z : Site 2} (hz : z ∈ (gridConnector (gridFloor n p) (gridFloor n q)).support) :
    dist (gridEmbed n z) p < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heps : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  have hpqi : |p i - q i| < 1 / (n : ℝ) := by
    rw [dist_pi_lt_iff heps] at hpq
    simpa [Real.dist_eq] using hpq i
  have hpp (j : Fin 2) := gridFloor_error hn p j
  have hqq (j : Fin 2) := gridFloor_error hn q j
  rw [gridConnector_mem_support] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · fin_cases i
    · apply (abs_lt_of_mem_uIcc
          (a := ((gridFloor n p 0 : ℤ) : ℝ) / n)
          (b := ((gridFloor n q 0 : ℤ) : ℝ) / n)
          (t := (t : ℝ) / n) (x := p 0) (e := 3 / (n : ℝ)))
      · exact div_mem_uIcc_of_int_mem hn ht
      · simpa [gridEmbed] using (hpp 0).trans
          ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
      · simpa [gridEmbed] using gridFloor_other_error hn hpqi
    · simpa [gridEmbed, Real.dist_eq] using (hpp 1).trans
        ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
  · fin_cases i
    · simpa [gridEmbed, Real.dist_eq] using gridFloor_other_error hn hpqi
    · apply (abs_lt_of_mem_uIcc
          (a := ((gridFloor n p 1 : ℤ) : ℝ) / n)
          (b := ((gridFloor n q 1 : ℤ) : ℝ) / n)
          (t := (t : ℝ) / n) (x := p 1) (e := 3 / (n : ℝ)))
      · exact div_mem_uIcc_of_int_mem hn ht
      · simpa [gridEmbed] using (hpp 1).trans
          ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
      · simpa [gridEmbed] using gridFloor_other_error hn hpqi

theorem gridFloor_near {n : ℕ} (hn : 0 < n) (p : Fin 2 → ℝ) :
    dist (gridEmbed n (gridFloor n p)) p < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  simpa [Real.dist_eq] using (gridFloor_error hn p i).trans
    ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))

theorem coord_bounds_of_mem_uIcc {a b t lo hi : ℤ}
    (ht : t ∈ Set.uIcc a b) (ha0 : lo ≤ a) (ha1 : a ≤ hi)
    (hb0 : lo ≤ b) (hb1 : b ≤ hi) : lo ≤ t ∧ t ≤ hi := by
  rw [Set.mem_uIcc] at ht
  rcases ht with ht | ht <;> omega

theorem gridConnector_mem_rect {n : ℕ} {x y z : Site 2}
    (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    (hy : y ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    (hz : z ∈ (gridConnector x y).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  rw [mem_rect] at hx hy ⊢
  rw [gridConnector_mem_support] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hb := coord_bounds_of_mem_uIcc ht hx.1 hx.2.1 hy.1 hy.2.1
    simpa using ⟨hb.1, hb.2, hx.2.2.1, hx.2.2.2⟩
  · have hb := coord_bounds_of_mem_uIcc ht hx.2.2.1 hx.2.2.2 hy.2.2.1 hy.2.2.2
    simpa using ⟨hy.1, hy.2.1, hb.1, hb.2⟩

theorem gridWalk_mem_rect {n N : ℕ} {g : ℕ → Site 2}
    (hg : ∀ k ≤ N, g k ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    {z : Site 2} (hz : z ∈ (gridWalk g N).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  rcases gridWalk_mem_support_cases g N z hz with rfl | ⟨k, hk, hzk⟩
  · exact hg 0 (Nat.zero_le _)
  · exact gridConnector_mem_rect (hg k hk.le) (hg (k + 1) hk) hzk



noncomputable def sampledGrid {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) (k : ℕ) : Site 2 :=
  gridFloor n (gamma (sampleTime N (min k N) (min_le_right k N) hN))

theorem sampledGrid_eq {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) {k : ℕ} (hk : k ≤ N) :
    sampledGrid n N hN gamma k = gridFloor n (gamma (sampleTime N k hk hN)) := by
  simp [sampledGrid, Nat.min_eq_left hk]

theorem sampledGrid_zero {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) : sampledGrid n N hN gamma 0 = gridFloor n p := by
  rw [sampledGrid_eq n N hN gamma (Nat.zero_le N), sampleTime_zero, Path.source]

theorem sampledGrid_self {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) : sampledGrid n N hN gamma N = gridFloor n q := by
  rw [sampledGrid_eq n N hN gamma (le_refl N), sampleTime_self, Path.target]



theorem exists_fine_sampling {p q : Fin 2 → ℝ} (gamma : Path p q)
    {n : ℕ} (hn : 0 < n) :
    ∃ N : ℕ, ∃ hN : 0 < N, ∀ (k : ℕ) (hk : k < N),
      dist (gamma (sampleTime N k hk.le hN))
        (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ) := by
  have heps : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨delta, hdelta, hgamma⟩ :=
    (Metric.uniformContinuous_iff.mp gamma.uniformContinuous) _ heps
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hdelta
  let N := m + 1
  have hN : 0 < N := by simp [N]
  refine ⟨N, hN, ?_⟩
  intro k hk
  apply hgamma
  rw [dist_sampleTime_succ N k hk hN]
  simpa [N] using hm



theorem sampledGrid_walk_near {p q : Fin 2 → ℝ} (gamma : Path p q)
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hfine : ∀ (k : ℕ) (hk : k < N),
      dist (gamma (sampleTime N k hk.le hN))
        (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ))
    {z : Site 2} (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
    ∃ t : unitInterval, dist (gridEmbed n z) (gamma t) < 3 / (n : ℝ) := by
  rcases gridWalk_mem_support_cases (sampledGrid n N hN gamma) N z hz with h | ⟨k, hk, hzk⟩
  · refine ⟨0, ?_⟩
    rw [h, sampledGrid_zero, Path.source]
    exact gridFloor_near hn p
  · let tk := sampleTime N k hk.le hN
    let tk1 := sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN
    have hgk : sampledGrid n N hN gamma k = gridFloor n (gamma tk) :=
      sampledGrid_eq n N hN gamma hk.le
    have hgk1 : sampledGrid n N hN gamma (k + 1) = gridFloor n (gamma tk1) :=
      sampledGrid_eq n N hN gamma (Nat.succ_le_iff.2 hk)
    refine ⟨tk, ?_⟩
    rw [hgk, hgk1] at hzk
    exact gridConnector_near hn (hfine k hk) hzk

theorem sampledGrid_walk_mem_rect {p q : Fin 2 → ℝ} (gamma : Path p q)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    {n N : ℕ} (hN : 0 < N) {z : Site 2}
    (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  apply gridWalk_mem_rect (N := N) (g := sampledGrid n N hN gamma) _ hz
  intro k hk
  rw [sampledGrid_eq n N hN gamma hk]
  rw [mem_rect]
  have hp : InUnitSquare (gamma (sampleTime N k hk hN)) :=
    hgamma ⟨_, rfl⟩
  exact ⟨gridFloor_coord_nonneg hp 0,
    gridFloor_coord_le hp 0,
    gridFloor_coord_nonneg hp 1,
    gridFloor_coord_le hp 1⟩

theorem gridFloor_coord_eq_zero {n : ℕ} {p : Fin 2 → ℝ} {i : Fin 2}
    (h : p i = 0) : gridFloor n p i = 0 := by
  simp [gridFloor, h]

theorem gridFloor_coord_eq_nat {n : ℕ} {p : Fin 2 → ℝ} {i : Fin 2}
    (h : p i = 1) : gridFloor n p i = (n : ℤ) := by
  simp [gridFloor, h]



theorem sampled_grid_walks_intersect
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    (heta : Set.range eta ⊆ {x | InUnitSquare x})
    (hl0 : hl 0 = 0) (hr0 : hr 0 = 1)
    (vb1 : vb 1 = 0) (vt1 : vt 1 = 1)
    {n NH NV : ℕ} (hn : 0 < n) (hNH : 0 < NH) (hNV : 0 < NV) :
    ∃ z : Site 2,
      z ∈ (gridWalk (sampledGrid n NH hNH gamma) NH).support ∧
      z ∈ (gridWalk (sampledGrid n NV hNV eta) NV).support := by
  let H := gridWalk (sampledGrid n NH hNH gamma) NH
  let V0 := gridWalk (sampledGrid n NV hNV eta) NV
  let a0 := gridFloor n vb 0
  let b0 := gridFloor n vt 0
  have hVsrc : sampledGrid n NV hNV eta 0 = ![a0, 0] := by
    rw [sampledGrid_zero]
    funext i
    fin_cases i
    · rfl
    · simpa using gridFloor_coord_eq_zero (n := n) vb1
  have hVtgt : sampledGrid n NV hNV eta NV = ![b0, (n : ℤ)] := by
    rw [sampledGrid_self]
    funext i
    fin_cases i
    · rfl
    · simpa using gridFloor_coord_eq_nat (n := n) vt1
  let V : (hypercubicLattice 2).Walk ![a0, 0] ![b0, (n : ℤ)] :=
    V0.copy hVsrc hVtgt
  have hVBox0 : ∀ z ∈ V0.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact sampledGrid_walk_mem_rect eta heta hNV hz
  have hVBox : ∀ z ∈ V.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact hVBox0 z (by simpa [V] using hz)
  have ha0lo : 0 ≤ a0 := gridFloor_coord_nonneg (heta ⟨0, by simp⟩) 0
  have ha0hi : a0 ≤ (n : ℤ) := gridFloor_coord_le (heta ⟨0, by simp⟩) 0
  have hb0lo : 0 ≤ b0 := gridFloor_coord_nonneg (heta ⟨1, by simp⟩) 0
  have hb0hi : b0 ≤ (n : ℤ) := gridFloor_coord_le (heta ⟨1, by simp⟩) 0
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hsep : ArcSeparatingSet {z : Site 2 | z ∈ V.support}
      0 (n : ℤ) 0 (n : ℤ) :=
    jec_arcSeparatingSet 0 (n : ℤ) 0 (n : ℤ) a0 b0 hnZ hnZ.le
      ha0lo ha0hi hb0lo hb0hi V hVBox _ (fun _ h ↦ h)
  have hHBox : ∀ z ∈ H.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact sampledGrid_walk_mem_rect gamma hgamma hNH hz
  have hHsrc : (sampledGrid n NH hNH gamma 0) 0 = 0 := by
    rw [sampledGrid_zero]
    exact gridFloor_coord_eq_zero hl0
  have hHtgt : (sampledGrid n NH hNH gamma NH) 0 = (n : ℤ) := by
    rw [sampledGrid_self]
    exact gridFloor_coord_eq_nat hr0
  obtain ⟨z, hzH, hzV⟩ := tpc_two_paths_cross_of_sep hsep
    (hHBox _ H.start_mem_support) (hHBox _ H.end_mem_support)
    hHsrc hHtgt H hHBox
  refine ⟨z, ?_, ?_⟩
  · exact hzH
  · simpa [V] using hzV




theorem unitSquare_paths_intersect
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    (heta : Set.range eta ⊆ {x | InUnitSquare x})
    (hl0 : hl 0 = 0) (hr0 : hr 0 = 1)
    (vb1 : vb 1 = 0) (vt1 : vt 1 = 1) :
    ∃ t s : unitInterval, gamma t = eta s := by
  by_contra hdisj
  have hgammaCompact : IsCompact (Set.range gamma) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image gamma.continuous)
  have hetaCompact : IsCompact (Set.range eta) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image eta.continuous)
  have hrangeDisj : Disjoint (Set.range gamma) (Set.range eta) := by
    rw [Set.disjoint_left]
    intro x hx hxeta
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨s, hs⟩ := hxeta
    exact hdisj ⟨t, s, hs.symm⟩
  obtain ⟨rho, hrho, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hgammaCompact hetaCompact.isClosed hrangeDisj
  have hrhoR : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hrho
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos hrhoR (by norm_num : (0 : ℝ) < 6))
  let n := m + 1
  have hn : 0 < n := by simp [n]
  have hmesh : 6 / (n : ℝ) < (rho : ℝ) := by
    calc
      6 / (n : ℝ) = 6 * (1 / (n : ℝ)) := by ring
      _ < 6 * ((rho : ℝ) / 6) := mul_lt_mul_of_pos_left (by simpa [n] using hm) (by norm_num)
      _ = (rho : ℝ) := by ring
  obtain ⟨NH, hNH, hfineH⟩ := exists_fine_sampling gamma hn
  obtain ⟨NV, hNV, hfineV⟩ := exists_fine_sampling eta hn
  obtain ⟨z, hzH, hzV⟩ := sampled_grid_walks_intersect gamma eta hgamma heta
    hl0 hr0 vb1 vt1 hn hNH hNV
  obtain ⟨t, ht⟩ := sampledGrid_walk_near gamma hn hNH hfineH hzH
  obtain ⟨s, hs⟩ := sampledGrid_walk_near eta hn hNV hfineV hzV
  have hrtsE : (rho : ENNReal) < edist (gamma t) (eta s) :=
    hsep (gamma t) ⟨t, rfl⟩ (eta s) ⟨s, rfl⟩
  have hrts : (rho : ℝ) < dist (gamma t) (eta s) := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top
      (edist_ne_top (gamma t) (eta s))).2 hrtsE
    simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
  have hclose : dist (gamma t) (eta s) < 6 / (n : ℝ) := by
    calc
      dist (gamma t) (eta s) ≤
          dist (gamma t) (gridEmbed n z) + dist (gridEmbed n z) (eta s) :=
        dist_triangle _ _ _
      _ < 3 / (n : ℝ) + 3 / (n : ℝ) :=
        add_lt_add (by rw [_root_.dist_comm]; exact ht) hs
      _ = 6 / (n : ℝ) := by ring
  linarith


def InRectangle (a b c d : ℝ) (p : Fin 2 → ℝ) : Prop :=
  a ≤ p 0 ∧ p 0 ≤ b ∧ c ≤ p 1 ∧ p 1 ≤ d


noncomputable def normalizeRectangle (a b c d : ℝ) (p : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  fun i => if i = 0 then (p 0 - a) / (b - a) else (p 1 - c) / (d - c)

theorem continuous_normalizeRectangle (a b c d : ℝ) :
    Continuous (normalizeRectangle a b c d) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [normalizeRectangle] <;> fun_prop

theorem normalizeRectangle_injective {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Function.Injective (normalizeRectangle a b c d) := by
  intro p q hpq
  funext i
  have hi := congrFun hpq i
  fin_cases i
  · simp [normalizeRectangle] at hi
    field_simp [ne_of_gt (sub_pos.mpr hab)] at hi
    simpa using (sub_left_inj.mp hi)
  · simp [normalizeRectangle] at hi
    field_simp [ne_of_gt (sub_pos.mpr hcd)] at hi
    simpa using (sub_left_inj.mp hi)

theorem normalizeRectangle_mem_unitSquare {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) {p : Fin 2 → ℝ}
    (hp : InRectangle a b c d p) :
    InUnitSquare (normalizeRectangle a b c d p) := by
  intro i
  fin_cases i
  · change 0 ≤ (p 0 - a) / (b - a) ∧ (p 0 - a) / (b - a) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hp.1) (sub_pos.mpr hab).le
    · rw [div_le_one (sub_pos.mpr hab)]
      linarith [hp.2.1]
  · change 0 ≤ (p 1 - c) / (d - c) ∧ (p 1 - c) / (d - c) ≤ 1
    constructor
    · exact div_nonneg (sub_nonneg.mpr hp.2.2.1) (sub_pos.mpr hcd).le
    · rw [div_le_one (sub_pos.mpr hcd)]
      linarith [hp.2.2.2]


theorem rectangle_paths_intersect
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InRectangle a b c d x})
    (heta : Set.range eta ⊆ {x | InRectangle a b c d x})
    (hl0 : hl 0 = a) (hr0 : hr 0 = b)
    (vb1 : vb 1 = c) (vt1 : vt 1 = d) :
    ∃ t s : unitInterval, gamma t = eta s := by
  let ngamma := gamma.map (continuous_normalizeRectangle a b c d)
  let neta := eta.map (continuous_normalizeRectangle a b c d)
  have hngamma : Set.range ngamma ⊆ {x | InUnitSquare x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact normalizeRectangle_mem_unitSquare hab hcd (hgamma ⟨t, rfl⟩)
  have hneta : Set.range neta ⊆ {x | InUnitSquare x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    exact normalizeRectangle_mem_unitSquare hab hcd (heta ⟨t, rfl⟩)
  have hnl : (normalizeRectangle a b c d hl) 0 = 0 := by
    simp [normalizeRectangle, hl0]
  have hnr : (normalizeRectangle a b c d hr) 0 = 1 := by
    simp [normalizeRectangle, hr0, ne_of_gt (sub_pos.mpr hab)]
  have hnb : (normalizeRectangle a b c d vb) 1 = 0 := by
    simp [normalizeRectangle, vb1]
  have hnt : (normalizeRectangle a b c d vt) 1 = 1 := by
    simp [normalizeRectangle, vt1, ne_of_gt (sub_pos.mpr hcd)]
  obtain ⟨t, s, hts⟩ := unitSquare_paths_intersect ngamma neta
    hngamma hneta hnl hnr hnb hnt
  refine ⟨t, s, ?_⟩
  exact normalizeRectangle_injective hab hcd hts


def clampCoord (a b x : ℝ) : ℝ := max a (min b x)

theorem clampCoord_bounds {a b x : ℝ} (hab : a ≤ b) :
    a ≤ clampCoord a b x ∧ clampCoord a b x ≤ b := by
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampCoord_of_mem {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    clampCoord a b x = x := by
  rw [clampCoord, min_eq_right hxb, max_eq_right hax]

theorem clampCoord_of_le_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    clampCoord a b x = a := by
  rw [clampCoord, min_eq_right (hx.trans hab), max_eq_left hx]

theorem clampCoord_of_right_le {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    clampCoord a b x = b := by
  rw [clampCoord, min_eq_left hx, max_eq_right hab]


theorem eq_of_clampCoord_eq_interior {a b x y : ℝ} (hab : a < b)
    (hay : a < y) (hyb : y < b) (h : clampCoord a b x = y) : x = y := by
  by_cases hxa : x ≤ a
  · rw [clampCoord_of_le_left hab.le hxa] at h
    linarith
  by_cases hbx : b ≤ x
  · rw [clampCoord_of_right_le hab.le hbx] at h
    linarith
  rw [clampCoord_of_mem (le_of_not_ge hxa) (le_of_not_ge hbx)] at h
  exact h


def clampX (a b : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then clampCoord a b (p 0) else p 1


def clampY (c d : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 1 then clampCoord c d (p 1) else p 0

theorem continuous_clampX (a b : ℝ) : Continuous (clampX a b) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [clampX, clampCoord] <;> fun_prop

theorem continuous_clampY (c d : ℝ) : Continuous (clampY c d) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [clampY, clampCoord] <;> fun_prop






theorem strip_paths_intersect
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hl0 : hl 0 < a) (hr0 : b < hr 0)
    (vb1 : vb 1 < c) (vt1 : d < vt 1)
    (hgammaY : ∀ t : unitInterval, c < gamma t 1 ∧ gamma t 1 < d)
    (hetaX : ∀ t : unitInterval, a < eta t 0 ∧ eta t 0 < b) :
    ∃ t s : unitInterval, gamma t = eta s := by
  let gamma' := gamma.map (continuous_clampX a b)
  let eta' := eta.map (continuous_clampY c d)
  have hgammaRect : Set.range gamma' ⊆ {x | InRectangle a b c d x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    have hb := clampCoord_bounds (x := gamma t 0) hab.le
    have hy := hgammaY t
    exact ⟨hb.1, hb.2, hy.1.le, hy.2.le⟩
  have hetaRect : Set.range eta' ⊆ {x | InRectangle a b c d x} := by
    intro x hx
    obtain ⟨t, rfl⟩ := hx
    have hb := clampCoord_bounds (x := eta t 1) hcd.le
    have hx' := hetaX t
    exact ⟨hx'.1.le, hx'.2.le, hb.1, hb.2⟩
  have hgl : (clampX a b hl) 0 = a := by
    simp [clampX, clampCoord_of_le_left hab.le hl0.le]
  have hgr : (clampX a b hr) 0 = b := by
    simp [clampX, clampCoord_of_right_le hab.le hr0.le]
  have hev : (clampY c d vb) 1 = c := by
    simp [clampY, clampCoord_of_le_left hcd.le vb1.le]
  have het : (clampY c d vt) 1 = d := by
    simp [clampY, clampCoord_of_right_le hcd.le vt1.le]
  obtain ⟨t, s, hts⟩ := rectangle_paths_intersect hab hcd gamma' eta'
    hgammaRect hetaRect hgl hgr hev het
  have hxClamp : clampCoord a b (gamma t 0) = eta s 0 := by
    simpa [gamma', eta', clampX, clampY] using congrFun hts 0
  have hyClamp : clampCoord c d (eta s 1) = gamma t 1 := by
    symm
    simpa [gamma', eta', clampX, clampY] using congrFun hts 1
  have hx : gamma t 0 = eta s 0 :=
    eq_of_clampCoord_eq_interior hab (hetaX s).1 (hetaX s).2 hxClamp
  have hy : gamma t 1 = eta s 1 :=
    (eq_of_clampCoord_eq_interior hcd (hgammaY t).1 (hgammaY t).2 hyClamp).symm
  refine ⟨t, s, ?_⟩
  funext i
  fin_cases i
  · simpa using hx
  · simpa using hy

end ContinuousRectangleCrossing

end StatMech
