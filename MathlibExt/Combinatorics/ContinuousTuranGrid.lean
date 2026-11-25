/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ContinuousTuran
import all MathlibExt.Combinatorics.ContinuousTuran
import Mathlib.Data.Finset.Sort
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.Bertrand

/-!
# Continuous Turán numbers of three-column grids

A grid with three columns and at least three rows has continuous Turán number of order
$n^{5/3}$. The upper bound thickens a planar set to a cylinder and uses the bound for three
stacked plus signs. For the lower bound, open squares on the edges of Brown's graph avoid
every grid of this size when their width is smaller than the coordinate gaps.
-/

namespace MetaMathlibExt
namespace opx_grid_three_columns_isTheta

open MeasureTheory Set opxD_plus_stack_isTheta
open scoped ENNReal

-- Use the third coordinate for the columns and the first coordinate for the rows.
private theorem measurePreserving_rotatedCoords :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ![q.1.2, q.2, q.1.1]) volume volume :=
  measurePreserving_vec3.comp (Measure.measurePreserving_swap.comp
    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)))

private abbrev stack (r c : ℝ) : Set (Fin 3 → ℝ) :=
  {v | |v 0| ≤ r ∧ |v 1| ≤ r ∧ (v 0 = 0 ∨ v 1 = 0) ∧
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 3 ∧ v 2 = i * c}

private theorem cylinder_free {X Y : Finset ℝ} (hX : X.card = 3) {r c : ℝ}
    (hr : 0 ≤ r) (hY : ∀ y ∈ Y, |y| ≤ r) (hc : 0 < c)
    (hgap : ∀ x ∈ X, ∀ x' ∈ X, x' - x ≤ c) {n : ℝ} {S : Set (ℝ × ℝ)}
    (hfree : ¬ PointSetContainsPattern S ((X : Set ℝ) ×ˢ (Y : Set ℝ))) :
    ¬ ContainsPatternD {v : Fin 3 → ℝ | (v 2, v 0) ∈ S ∧ v 1 ∈ Ioo 0 n} (stack r c) := by
  classical
  rintro ⟨f, hf, hmem⟩
  let rank (x : ℝ) : Fin 3 := if hx : x ∈ X then (X.orderIsoOfFin hX).symm ⟨x, hx⟩ else 0
  let z (x : ℝ) := ((rank x : ℕ) + 1 : ℝ) * c
  let v (x y : ℝ) : Fin 3 → ℝ := ![y, 0, z x]
  have hv (x : ℝ) {y : ℝ} (hy : y ∈ Y) : v x y ∈ stack r c := by
    refine ⟨hY y hy, by simpa [v] using hr, Or.inr rfl, (rank x : ℕ) + 1, by omega, ?_, ?_⟩
    · have := (rank x).isLt
      omega
    · simp [v, z]
  apply hfree
  refine ⟨fun x => f 2 (z x), f 0, ?_, ?_, ?_⟩
  · intro p hp q hq hlt
    have hpX : p.1 ∈ X := hp.1
    have hqX : q.1 ∈ X := hq.1
    have hlt' : rank q.1 < rank p.1 := by
      simpa [rank, hpX, hqX] using hlt
    have hstep : ((rank q.1 : ℕ) : ℝ) + 1 ≤ (rank p.1 : ℕ) := by exact_mod_cast hlt'
    have hsep : c ≤ z p.1 - z q.1 := by
      dsimp [z]
      nlinarith [mul_le_mul_of_nonneg_right hstep hc.le]
    exact (hgap _ hqX _ hpX).trans (hsep.trans
      (hf 2 _ (hv p.1 hp.2) _ (hv q.1 hq.2) (show z q.1 < z p.1 by linarith)))
  · intro p hp q hq hlt
    exact hf 0 _ (hv p.1 hp.2) _ (hv q.1 hq.2) hlt
  · intro p hp
    exact (hmem _ (hv p.1 hp.2)).1

private theorem upper {X Y : Finset ℝ} (hX : X.card = 3) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) := by
  classical
  let r := 1 + ∑ a ∈ X ∪ Y, |a|
  have hr : 0 < r := by dsimp [r]; positivity
  have hR {a : ℝ} (ha : a ∈ X ∪ Y) : |a| ≤ r := by
    have := Finset.single_le_sum (f := abs) (fun b _ => abs_nonneg b) ha
    dsimp [r]
    linarith
  let c := 2 * r
  have hc : 0 < c := by dsimp [c]; positivity
  refine Asymptotics.IsBigO.of_bound (3 * c + 3 * (4 * r) ^ (1 / 3 : ℝ)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [Real.norm_of_nonneg (opx_nonneg _ _), Real.norm_of_nonneg (by positivity)]
  apply Real.sSup_le _ (by positivity)
  rintro _ ⟨S, ⟨hS, hSn, hfree⟩, rfl⟩
  let T := {v : Fin 3 → ℝ | (v 2, v 0) ∈ S ∧ v 1 ∈ Ioo 0 (n : ℝ)}
  have hT : IsOpen T := (hS.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
  have hTn : T ⊆ Icc 0 (fun _ => (n : ℝ)) := by
    intro v hv
    obtain ⟨h2, h0⟩ := hSn hv.1
    have h1 := hv.2
    exact ⟨fun i => by fin_cases i <;> first | exact h0.1 | exact h1.1.le | exact h2.1,
      fun i => by fin_cases i <;> first | exact h0.2 | exact h1.2.le | exact h2.2⟩
  have hfreeT : ¬ ContainsPatternD T (stack r c) := by
    apply cylinder_free hX hr.le (fun y hy => hR (Finset.mem_union_right X hy)) hc _ hfree
    intro x hx x' hx'
    have h1 := (abs_le.mp (hR (Finset.mem_union_left Y hx))).1
    have h2 := (abs_le.mp (hR (Finset.mem_union_left Y hx'))).2
    dsimp [c]
    linarith
  have hvol : volume.real T = (volume S).toReal * n := by
    rw [Measure.real,
      ← measurePreserving_rotatedCoords.measure_preimage hT.measurableSet.nullMeasurableSet]
    change (volume (S ×ˢ Ioo 0 (n : ℝ))).toReal = _
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hn0.le]
  have h := volume_le_of_free (t := 3) (by decide) hr hc hn0 hT hTn hfreeT
  rw [hvol] at h
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) - 1 / 3 = 8 / 3 by norm_num] at h
  have hpow : (n : ℝ) ^ (8 / 3 : ℝ) = (n : ℝ) ^ (5 / 3 : ℝ) * n := by
    rw [← Real.rpow_add_one hn0.ne']; norm_num
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  apply le_of_mul_le_mul_right _ hn0
  rw [hpow] at h h2
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 3 * c)]

-- One cell width works for all distinct coordinates of the finite pattern.
private theorem exists_width (A : Finset ℝ) :
    ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 64 ∧ ∀ a ∈ A, ∀ b ∈ A, a < b → u ≤ b - a := by
  classical
  let gaps := ((A ×ˢ A).image fun p => p.2 - p.1).filter (0 < ·)
  let D := insert (1 / 64 : ℝ) gaps
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  refine ⟨D.min' hD, ?_, D.min'_le _ (Finset.mem_insert_self ..), ?_⟩
  · rcases Finset.mem_insert.mp (D.min'_mem hD) with h | h
    · rw [h]; norm_num
    · exact (Finset.mem_filter.mp h).2
  · intro a ha b hb hab
    apply D.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, sub_pos.mpr hab⟩)

-- An expanding copy of the grid in the union of open cells would use distinct cell
-- indices for three columns and three rows.
private theorem cells_lower {X Y : Finset ℝ} (hX : X.card = 3) (hY : 3 ≤ Y.card)
    {u : ℝ} (hu : 0 < u) (hgap : ∀ a ∈ X ∪ Y, ∀ b ∈ X ∪ Y, a < b → u ≤ b - a)
    {M : ℕ} {E : Finset (ℕ × ℕ)} (hE : ∀ e ∈ E, e.1 < M ∧ e.2 < M)
    (hfree : ∀ I J : Finset ℕ, I.card = 3 → J.card = 3 → ¬ I ×ˢ J ⊆ E) :
    E.card * u ^ 2 ≤ opx (M * u) ((X : Set ℝ) ×ˢ (Y : Set ℝ)) := by
  classical
  let cell (k : ℕ) := Ioo ((k : ℝ) * u) ((k + 1 : ℝ) * u)
  let box (e : ℕ × ℕ) := cell e.1 ×ˢ cell e.2
  let S := ⋃ e ∈ E, box e
  have hbox (e : ℕ × ℕ) : IsOpen (box e) := isOpen_Ioo.prod isOpen_Ioo
  have hS : IsOpen S := isOpen_biUnion fun e _ => hbox e
  have hbound {k : ℕ} (hk : k < M) : cell k ⊆ Icc 0 ((M : ℝ) * u) := by
    intro x hx
    have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    exact ⟨(mul_nonneg (Nat.cast_nonneg k) hu.le).trans hx.1.le,
      hx.2.le.trans (mul_le_mul_of_nonneg_right hk' hu.le)⟩
  have hSn : S ⊆ Icc 0 ((M : ℝ) * u) ×ˢ Icc 0 ((M : ℝ) * u) := by
    rintro p hp
    obtain ⟨e, he, hp⟩ := mem_iUnion₂.mp hp
    exact ⟨hbound (hE e he).1 hp.1, hbound (hE e he).2 hp.2⟩
  let idx (x : ℝ) := ⌊x / u⌋₊
  have hidx {k : ℕ} {x : ℝ} (hx : x ∈ cell k) : idx x = k := by
    have h0 := (mul_nonneg (Nat.cast_nonneg k) hu.le).trans hx.1.le
    exact (Nat.floor_eq_iff (div_nonneg h0 hu.le)).mpr
      ⟨(le_div_iff₀ hu).mpr hx.1.le, (div_lt_iff₀ hu).mpr hx.2⟩
  have hdisj : (E : Set (ℕ × ℕ)).PairwiseDisjoint box := by
    intro e _ e' _ hne
    refine disjoint_left.mpr fun p hp hp' => hne ?_
    exact Prod.ext ((hidx hp.1).symm.trans (hidx hp'.1)) ((hidx hp.2).symm.trans (hidx hp'.2))
  have hvol : volume.real S = E.card * u ^ 2 := by
    have hcell (k : ℕ) : volume (cell k) = ENNReal.ofReal u := by
      change volume (Ioo _ _) = _
      rw [Real.volume_Ioo]
      congr 1
      ring
    have hvolbox (e : ℕ × ℕ) : volume (box e) = ENNReal.ofReal u ^ 2 := by
      change volume (cell e.1 ×ˢ cell e.2) = _
      rw [Measure.volume_eq_prod, Measure.prod_prod, hcell, hcell, sq]
    rw [Measure.real, measure_biUnion_finset hdisj fun e _ => (hbox e).measurableSet]
    simp [hvolbox, ENNReal.toReal_mul, ENNReal.toReal_pow, hu.le]
  have hfreeS : ¬ PointSetContainsPattern S ((X : Set ℝ) ×ˢ (Y : Set ℝ)) := by
    rintro ⟨f, g, hf, hg, himg⟩
    have hcell {x y : ℝ} (hx : x ∈ X) (hy : y ∈ Y) : (idx (f x), idx (g y)) ∈ E := by
      obtain ⟨e, he, hp⟩ := mem_iUnion₂.mp (himg (x, y) ⟨hx, hy⟩)
      rwa [hidx hp.1, hidx hp.2]
    obtain ⟨Y', hsub, hY'⟩ := Finset.exists_subset_card_eq hY
    obtain ⟨x₀, hx₀⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y₀, hy₀⟩ : Y.Nonempty := Finset.card_pos.mp (by omega)
    have hcol : StrictMonoOn (idx ∘ f) (X : Set ℝ) := by
      intro x hx x' hx' hlt
      have he := hf (x', y₀) ⟨hx', hy₀⟩ (x, y₀) ⟨hx, hy₀⟩ hlt
      have hd := hgap x (Finset.mem_union_left _ hx) x' (Finset.mem_union_left _ hx') hlt
      exact floor_lt_floor_of_add_le hu (hSn (himg (x, y₀) ⟨hx, hy₀⟩)).1.1 (by linarith)
    have hrow : StrictMonoOn (idx ∘ g) (Y' : Set ℝ) := by
      intro y hy y' hy' hlt
      have he := hg (x₀, y') ⟨hx₀, hsub hy'⟩ (x₀, y) ⟨hx₀, hsub hy⟩ hlt
      have hd := hgap y (Finset.mem_union_right _ (hsub hy)) y'
        (Finset.mem_union_right _ (hsub hy')) hlt
      exact floor_lt_floor_of_add_le hu (hSn (himg (x₀, y) ⟨hx₀, hsub hy⟩)).2.1 (by linarith)
    apply hfree (X.image (idx ∘ f)) (Y'.image (idx ∘ g))
      ((Finset.card_image_of_injOn hcol.injOn).trans hX)
      ((Finset.card_image_of_injOn hrow.injOn).trans hY')
    rintro ⟨i, j⟩ hij
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hij).1
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hij).2
    exact hcell hx (hsub hy)
  rw [← hvol]
  refine le_csSup ?_ ⟨S, ⟨hS, hSn, hfreeS⟩, rfl⟩
  refine ⟨volume.real (Icc 0 ((M : ℝ) * u) ×ˢ Icc 0 ((M : ℝ) * u)), ?_⟩
  rintro _ ⟨T, ⟨_, hT, _⟩, rfl⟩
  exact measureReal_mono hT (isCompact_Icc.prod isCompact_Icc).measure_ne_top

-- Bertrand's postulate supplies a Brown graph with between n and 64n vertices on each side.
private theorem lower {X Y : Finset ℝ} (hX : X.card = 3) (hY : 3 ≤ Y.card) :
    (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) := by
  classical
  obtain ⟨u, hu, hu64, hgap⟩ := exists_width (X ∪ Y)
  refine Asymptotics.IsBigO.of_bound (2 / u ^ 2) ?_
  filter_upwards [Filter.eventually_ge_atTop 8] with n hn
  let s := (n : ℝ) ^ (1 / 3 : ℝ)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs3 : s ^ 3 = n := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hs2 : 2 ≤ s :=
    le_of_pow_le_pow_left₀ (by norm_num : 3 ≠ 0) hs (by rw [hs3]; norm_num; exact hn)
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.exists_prime_lt_and_le_two_mul ⌈s⌉₊
    (Nat.ceil_pos.2 (by linarith)).ne'
  have := Fact.mk hp
  have hps : s ≤ p := (Nat.le_ceil s).trans (by exact_mod_cast hmp.le)
  have hp3 : 3 ≤ p := by
    have h : (2 : ℝ) < p := (hs2.trans (Nat.le_ceil s)).trans_lt (by exact_mod_cast hmp)
    exact_mod_cast h
  have hp4 : (p : ℝ) ≤ 4 * s := by
    have h : (p : ℝ) ≤ 2 * ⌈s⌉₊ := by exact_mod_cast hp2m
    linarith [Nat.ceil_lt_add_one hs]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨ρ, hρ⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; omega)
  obtain ⟨E, hE, hEcard, hEfree⟩ := exists_cells (V := Fin 3 → ZMod p)
    (fun a b => brownQ (b - a) = ρ) (brown_free h2 hρ)
  have hcardV : Fintype.card (Fin 3 → ZMod p) = p ^ 3 := by simp [ZMod.card]
  rw [hcardV] at hE
  have hfit : ((p ^ 3 : ℕ) : ℝ) * u ≤ n := by
    push_cast
    calc (p : ℝ) ^ 3 * u ≤ (4 * s) ^ 3 * (1 / 64) := by gcongr
      _ = (n : ℝ) := by rw [← hs3]; ring
  have harea := (cells_lower hX hY hu hgap hE hEfree).trans (opx_mono_left _ hfit)
  have hcount : (p : ℝ) ^ 3 * (((p : ℝ) - 1) * p) ≤ E.card := by
    rw [hEcard]
    have h := card_brown (F := ZMod p) ρ
    rw [ZMod.card] at h
    calc (p : ℝ) ^ 3 * ((p - 1) * p) = ((p ^ 3 * ((p - 1) * p) : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub hp.one_le]
          ring
      _ ≤ _ := by exact_mod_cast h
  have hpow : (n : ℝ) ^ (5 / 3 : ℝ) = s ^ 5 := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  have hhalf : (p : ℝ) / 2 ≤ p - 1 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith
  have hcard : s ^ 5 / 2 ≤ E.card := calc
    s ^ 5 / 2 ≤ (p : ℝ) ^ 5 / 2 := by gcongr
    _ = (p : ℝ) ^ 3 * ((p / 2) * p) := by ring
    _ ≤ _ := (by gcongr : (p : ℝ) ^ 3 * ((p / 2) * p) ≤ p ^ 3 * ((p - 1) * p))
    _ ≤ _ := hcount
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (opx_nonneg _ _), hpow,
    div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hu)]
  linarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg u)]

end opx_grid_three_columns_isTheta

/-- **Continuous Turán number of a grid with three columns.** Let $X$ and $Y$ be finite sets of
real numbers with $|X| = 3$ and $|Y| \ge 3$, and let $P = X \times Y$ be the grid with $3$ columns
and $|Y|$ rows. Then $\operatorname{opx}(n, P) = \Theta(n^{5/3})$ as the natural number $n$ tends
to infinity.

Source: Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 3.7
(`integers-2024-A1-cor-3-7`), second sentence. -/
public theorem opx_grid_three_columns_isTheta {X Y : Finset ℝ} (hX : X.card = 3)
    (hY : 3 ≤ Y.card) :
    (fun n : ℕ => opx n ((X : Set ℝ) ×ˢ (Y : Set ℝ))) =Θ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) :=
  ⟨opx_grid_three_columns_isTheta.upper hX, opx_grid_three_columns_isTheta.lower hX hY⟩

end MetaMathlibExt
