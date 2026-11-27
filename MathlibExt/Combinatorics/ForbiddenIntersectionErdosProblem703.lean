/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Data.Fin.Tuple.Basic
import MathlibExt.Probability.McDiarmid

/-!
# Families avoiding one intersection size (Erdős Problem 703)

Erdős Problem 703: let `r ≥ 1` and define `T(n, r)` to be maximal such that there exists a family
`𝓕` of subsets of `{1, …, n}` of size `T(n, r)` such that `|A ∩ B| ≠ r` for all `A, B ∈ 𝓕`. Estimate
`T(n, r)` for `r ≥ 2`. In particular, is it true that for every `ε > 0` there exists `δ > 0` such
that for all `εn < r < (1/2 - ε) n` we have `T(n, r) < (2 - δ)^n`?

The Frankl–Rödl theorem gives an exponential bound for families avoiding one intersection size.

Source: T. F. Bloom, Erdős Problems, Problem #703, https://www.erdosproblems.com/703 (status PROVED
(LEAN)). UnsolvedMath record UM-30006986 (`EP-703`), dataset ulamai/UnsolvedMath v1.8.0.

`T(n, r) < (2 - δ)^n` is stated as: every family with the property has fewer than `(2 - δ)^n`
members. The condition is read literally for all `A, B ∈ 𝓕` (including `A = B`); with distinct pairs
the bound follows as well, since adding the `r`-sets changes `|𝓕|` by at most `C(n, r)`. The
open-ended 'estimate `T(n, r)`' is not formalized. Compared with the formal-conjectures statement
`ErdosProblems/703.lean` (equivalent; no code imported).

The proof specializes the coordinate reduction in Dodos and Karamanlis,
*Forbidden sparse intersections*, <https://arxiv.org/abs/2303.16015>, to uniform measure.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703Wanted

/-- **Erdős Problem 703: exponential gap for a forbidden intersection size.** The proposition that
for every $\varepsilon > 0$ there is $\delta > 0$ such that for all natural numbers $n$ and $r$ with
$\varepsilon n < r < (1/2 - \varepsilon) n$, every family $\mathcal{F}$ of subsets of
$\{1, \dots, n\}$ with $|A \cap B| \ne r$ for all $A, B \in \mathcal{F}$ (including $A = B$) has
$|\mathcal{F}| < (2 - \delta)^n$. Equivalently, $T(n, r) < (2 - \delta)^n$, where $T(n, r)$ is the
largest size of such a family. -/
def forbiddenIntersectionExponentialGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n r : ℕ, ε * n < r → (r : ℝ) < (1 / 2 - ε) * n →
    ∀ F : Finset (Finset (Fin n)), (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) →
      (F.card : ℝ) < (2 - δ) ^ n

open Finset
open scoped BigOperators

/-! ## Binary families and coordinate slices -/

private abbrev Cube (n : ℕ) := Fin n → Bool

private noncomputable def density {n : ℕ} (A : Finset (Cube n)) : ℝ :=
  (A.card : ℝ) / 2 ^ n

private theorem density_nonneg {n : ℕ} (A : Finset (Cube n)) : 0 ≤ density A := by
  unfold density
  positivity

private theorem density_le_one {n : ℕ} (A : Finset (Cube n)) : density A ≤ 1 := by
  rw [density, div_le_one (by positivity)]
  exact_mod_cast (show A.card ≤ 2 ^ n by
    simpa [Fintype.card_fun] using A.card_le_univ)

private theorem density_mono {n : ℕ} {A B : Finset (Cube n)} (h : A ⊆ B) :
    density A ≤ density B :=
  div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

private theorem density_map {n : ℕ} (A : Finset (Cube n)) (e : Cube n ↪ Cube n) :
    density (A.map e) = density A := by
  simp [density]

private theorem density_union_add_inter {n : ℕ} (A B : Finset (Cube n)) :
    density (A ∪ B) + density (A ∩ B) = density A + density B := by
  simp only [density, ← add_div, ← Nat.cast_add]
  rw [card_union_add_card_inter]

private def supportEquiv (n : ℕ) : Cube n ≃ Finset (Fin n) where
  toFun x := univ.filter (fun i => x i = true)
  invFun s i := decide (i ∈ s)
  left_inv x := by
    funext i
    cases h : x i <;> simp [h]
  right_inv s := by
    ext i
    simp

private theorem mem_support {n : ℕ} (x : Cube n) (i : Fin n) :
    i ∈ supportEquiv n x ↔ x i = true := by
  simp [supportEquiv]

private def overlap {n : ℕ} (x y : Cube n) : ℕ :=
  ∑ i, if x i = true ∧ y i = true then 1 else 0

private theorem overlap_eq_card {n : ℕ} (x y : Cube n) :
    overlap x y = (supportEquiv n x ∩ supportEquiv n y).card := by
  unfold overlap
  rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
  congr 1
  ext i
  simp [mem_support]

private theorem overlap_le {n : ℕ} (x y : Cube n) : overlap x y ≤ n := by
  rw [overlap_eq_card]
  simpa using (supportEquiv n x ∩ supportEquiv n y).card_le_univ

private theorem overlap_cons {n : ℕ} (b c : Bool) (x y : Cube n) :
    overlap (Fin.cons b x) (Fin.cons c y) =
      overlap x y + (if b = true ∧ c = true then 1 else 0) := by
  rw [overlap, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, overlap, add_comm]

private noncomputable def slice {n : ℕ} (A : Finset (Cube (n + 1))) (b : Bool) :
    Finset (Cube n) := by
  classical exact univ.filter (fun x => Fin.cons b x ∈ A)

private theorem mem_slice {n : ℕ} {A : Finset (Cube (n + 1))} {b : Bool} {x : Cube n} :
    x ∈ slice A b ↔ Fin.cons b x ∈ A := by
  classical simp [slice]

private theorem density_slices {n : ℕ} (A : Finset (Cube (n + 1))) :
    density (slice A false) + density (slice A true) = 2 * density A := by
  classical
  let cons (b : Bool) : Cube n ↪ Cube (n + 1) :=
    ⟨fun x => Fin.cons b x, fun x y h => by
      simpa using congrArg (fun f : Cube (n + 1) => Fin.tail f) h⟩
  have hsplit : (slice A false).map (cons false) ∪ (slice A true).map (cons true) = A := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hx | hx <;>
        obtain ⟨y, hy, rfl⟩ := mem_map.mp hx <;> exact mem_slice.mp hy
    · intro hx
      have hmem (b : Bool) (hb : x 0 = b) : x ∈ (slice A b).map (cons b) := by
        have he : Fin.cons b (Fin.tail x) = x := by rw [← hb, Fin.cons_self_tail]
        exact mem_map.mpr ⟨Fin.tail x, mem_slice.mpr (by rwa [he]), he⟩
      cases h0 : x 0
      · exact mem_union_left _ (hmem false h0)
      · exact mem_union_right _ (hmem true h0)
  have hdis : Disjoint ((slice A false).map (cons false)) ((slice A true).map (cons true)) := by
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨y, _, rfl⟩ := mem_map.mp hx
    obtain ⟨z, _, hz⟩ := mem_map.mp hy
    have h0 := congrArg (fun f : Cube (n + 1) => f 0) hz
    change true = false at h0
    cases h0
  have hcard := congrArg Finset.card hsplit
  rw [card_union_of_disjoint hdis, card_map, card_map] at hcard
  simp only [density, ← add_div, ← Nat.cast_add, hcard, pow_succ]
  ring

private def avoids {n : ℕ} (a b : ℕ) (A B : Finset (Cube n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, ¬ (a ≤ overlap x y ∧ overlap x y ≤ b)

private theorem avoids_comm {n a b : ℕ} {A B : Finset (Cube n)} :
    avoids a b A B ↔ avoids a b B A := by
  have hsymm (x y : Cube n) : overlap x y = overlap y x := by
    rw [overlap_eq_card, overlap_eq_card, inter_comm]
  constructor <;> intro h x hx y hy hz <;>
    exact h y hy x hx (by simpa only [hsymm y x] using hz)

private theorem avoids_slice_true {n a b : ℕ} {A B : Finset (Cube (n + 1))}
    (h : avoids a b A B) (ha : 0 < a) (hab : a ≤ b) :
    avoids (a - 1) (b - 1) (slice A true) (slice B true) := by
  intro x hx y hy hz
  apply h _ (mem_slice.mp hx) _ (mem_slice.mp hy)
  simp only [overlap_cons, and_self, ↓reduceIte]
  omega

private theorem avoids_slice_union {n a b : ℕ} {A B : Finset (Cube (n + 1))}
    (h : avoids a b A B) : avoids a b (slice A false) (slice B false ∪ slice B true) := by
  intro x hx y hy hz
  rcases mem_union.mp hy with hy | hy
  · exact h _ (mem_slice.mp hx) _ (mem_slice.mp hy) (by simpa [overlap_cons] using hz)
  · exact h _ (mem_slice.mp hx) _ (mem_slice.mp hy) (by simpa [overlap_cons] using hz)

private theorem avoids_slice_inter {n a b : ℕ} {A B : Finset (Cube (n + 1))}
    (h : avoids a b A B) (ha : 0 < a) (hab : a ≤ b) :
    avoids (a - 1) b (slice A true) (slice B false ∩ slice B true) := by
  intro x hx y hy hz
  by_cases hlow : a ≤ overlap x y
  · apply h _ (mem_slice.mp hx) _ (mem_slice.mp (mem_inter.mp hy).1)
    simpa [overlap_cons] using And.intro hlow hz.2
  · apply h _ (mem_slice.mp hx) _ (mem_slice.mp (mem_inter.mp hy).2)
    simp only [overlap_cons, and_self, ↓reduceIte]
    omega


/-! ## Reduction to a forbidden interval at an endpoint -/

-- With both slice densities normalized to have mean one, small gains force
-- a large intersection of the second family's slices.
private theorem normalizedWidening {d a₀ a₁ b₀ b₁ u v : ℝ}
    (hd : 0 < d) (hd' : d ≤ 1 / 10)
    (ha : a₀ + a₁ = 2) (hb : b₀ + b₁ = 2)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀)
    (hu₀ : b₀ ≤ u) (hu₁ : b₁ ≤ u) (hv₁ : a₁ ≤ v)
    (ht : a₁ * b₁ ≤ 1 + d) (hf : a₀ * u ≤ 1 + d) (hs : v * b₀ ≤ 1 + d) :
    1 - d - 6 * d ^ 2 ≤ a₁ * (2 - u) := by
  have h₀₀ := (mul_le_mul_of_nonneg_left hu₀ ha₀).trans hf
  have h₀₁ := (mul_le_mul_of_nonneg_left hu₁ ha₀).trans hf
  have h₁₀ := (mul_le_mul_of_nonneg_right hv₁ hb₀).trans hs
  have ha₀' : a₀ ≤ 1 + d := by
    linarith [show a₀ * b₀ + a₀ * b₁ = 2 * a₀ by rw [← mul_add, hb]; ring]
  have ha₁' : a₁ ≤ 1 + d := by
    linarith [show a₁ * b₀ + a₁ * b₁ = 2 * a₁ by rw [← mul_add, hb]; ring]
  have hu : 1 ≤ u := by linarith
  have hm : (1 - d) * u ≤ 1 + d :=
    (mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ u)).trans hf
  have hu' : u ≤ 1 + 3 * d := by
    apply le_of_mul_le_mul_left _ (by linarith : 0 < 1 - d)
    exact hm.trans (by nlinarith [mul_nonneg hd.le (show 0 ≤ 1 - 3 * d by linarith)])
  have hmul : (a₁ - 1) * (u - 1) ≤ 3 * d ^ 2 := by
    calc
      _ ≤ d * (u - 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ d * (3 * d) := mul_le_mul_of_nonneg_left (by linarith) hd.le
      _ = _ := by ring
  nlinarith only [hmul, hf, show a₀ = 2 - a₁ by linarith,
    show a₀ * u = (2 - a₁) * u by rw [show a₀ = 2 - a₁ by linarith]]

private theorem widenDensity {n : ℕ} {A B : Finset (Cube (n + 1))} {d : ℝ}
    (hd : 0 < d) (hd' : d ≤ 1 / 10) (hA : 0 < density A) (hB : 0 < density B)
    (ht : density (slice A true) * density (slice B true) ≤ (1 + d) * (density A * density B))
    (hf : density (slice A false) * density (slice B false ∪ slice B true) ≤
      (1 + d) * (density A * density B))
    (hs : density (slice A false ∪ slice A true) * density (slice B false) ≤
      (1 + d) * (density A * density B)) :
    (1 - d - 6 * d ^ 2) * (density A * density B) ≤
      density (slice A true) * density (slice B false ∩ slice B true) := by
  have normalize (x y : ℝ) : x / density A * (y / density B) ≤ 1 + d ↔
      x * y ≤ (1 + d) * (density A * density B) := by
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos hA hB)]
  have havg (C : Finset (Cube (n + 1))) (hC : 0 < density C) :
      density (slice C false) / density C + density (slice C true) / density C = 2 := by
    rw [← add_div, density_slices, mul_div_cancel_right₀ _ hC.ne']
  have hinter :
      2 - density (slice B false ∪ slice B true) / density B =
        density (slice B false ∩ slice B true) / density B := by
    rw [sub_eq_iff_eq_add, add_comm, ← add_div, density_union_add_inter, density_slices,
      mul_div_cancel_right₀ _ hB.ne']
  have h := normalizedWidening hd hd' (havg A hA) (havg B hB)
    (div_nonneg (density_nonneg _) hA.le) (div_nonneg (density_nonneg _) hB.le)
    (div_le_div_of_nonneg_right (density_mono subset_union_left) hB.le)
    (div_le_div_of_nonneg_right (density_mono subset_union_right) hB.le)
    (div_le_div_of_nonneg_right (density_mono subset_union_right) hA.le)
    ((normalize _ _).mpr ht) ((normalize _ _).mpr hf) ((normalize _ _).mpr hs)
  rw [hinter, div_mul_div_comm, le_div_iff₀ (mul_pos hA hB)] at h
  exact h

private theorem log_gain {d : ℝ} (hd : 0 < d) :
    d - 10 * d ^ 2 ≤ Real.log (1 + d) := by
  have hpos : 0 < 1 + d := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 + d)⁻¹ ≤ 1 - d + d ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith only [mul_nonneg (sq_nonneg d) hd.le]
  linarith [sq_nonneg d]

private theorem log_widen {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 10) :
    0 < 1 - d - 6 * d ^ 2 ∧ -d - 10 * d ^ 2 ≤ Real.log (1 - d - 6 * d ^ 2) := by
  have hsq : d ^ 2 ≤ 1 / 100 := by
    nlinarith [mul_nonneg hd.le (show 0 ≤ 1 / 10 - d by linarith)]
  have hpos : 0 < 1 - d - 6 * d ^ 2 := by linarith
  refine ⟨hpos, ?_⟩
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (1 - d - 6 * d ^ 2)⁻¹ ≤ 1 + d + 10 * d ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith only [mul_nonneg (sq_nonneg d) (show 0 ≤ 3 - 16 * d - 60 * d ^ 2 by linarith)]
  linarith

private theorem reductionStep {n a b : ℕ} {A B : Finset (Cube (n + 1))} {d : ℝ}
    (hd : 0 < d) (hd' : d ≤ 1 / 10) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ n)
    (hP : 0 < density A * density B) (havoid : avoids a b A B) :
    ∃ (i j : ℕ) (C D : Finset (Cube n)), i ≤ j ∧ j ≤ n ∧ a ≤ i + 1 ∧ j ≤ b ∧
      avoids i j C D ∧ 0 < density C * density D ∧
      Real.log (density A * density B) + d * (1 - 2 * ((j : ℝ) - i - b + a)) - 10 * d ^ 2 ≤
        Real.log (density C * density D) := by
  let Target : Prop :=
    ∃ (i j : ℕ) (C D : Finset (Cube n)), i ≤ j ∧ j ≤ n ∧ a ≤ i + 1 ∧ j ≤ b ∧
      avoids i j C D ∧ 0 < density C * density D ∧
      Real.log (density A * density B) + d * (1 - 2 * ((j : ℝ) - i - b + a)) - 10 * d ^ 2 ≤
        Real.log (density C * density D)
  change Target
  have finish (i j : ℕ) (C D : Finset (Cube n)) (k : ℝ)
      (hij : i ≤ j) (hj : j ≤ n) (hi : a ≤ i + 1) (hjb : j ≤ b) (hcd : avoids i j C D)
      (hk : 0 < k) (hgain : k * (density A * density B) ≤ density C * density D)
      (hlog : d * (1 - 2 * ((j : ℝ) - i - b + a)) - 10 * d ^ 2 ≤ Real.log k) : Target := by
    have hpos := (mul_pos hk hP).trans_le hgain
    refine ⟨i, j, C, D, hij, hj, hi, hjb, hcd, hpos, ?_⟩
    have h := Real.log_le_log (mul_pos hk hP) hgain
    rw [Real.log_mul hk.ne' hP.ne'] at h
    linarith
  have hgpos : 0 < 1 + d := by linarith
  by_cases ht : (1 + d) * (density A * density B) ≤
      density (slice A true) * density (slice B true)
  · apply finish (a - 1) (b - 1) _ _ (1 + d) (by omega) (by omega) (by omega) (by omega)
      (avoids_slice_true havoid ha hab) hgpos ht
    have hb' : 1 ≤ b := by omega
    push_cast [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub hb']
    convert log_gain hd using 1; ring
  by_cases hf : (1 + d) * (density A * density B) ≤
      density (slice A false) * density (slice B false ∪ slice B true)
  · exact finish a b _ _ (1 + d) hab hb (by omega) le_rfl (avoids_slice_union havoid)
      hgpos hf (by convert log_gain hd using 1; ring)
  by_cases hs : (1 + d) * (density A * density B) ≤
      density (slice A false ∪ slice A true) * density (slice B false)
  · exact finish a b _ _ (1 + d) hab hb (by omega) le_rfl
      (avoids_comm.mp (avoids_slice_union (avoids_comm.mp havoid)))
      hgpos hs (by convert log_gain hd using 1; ring)
  have hA : 0 < density A := by
    by_contra! hn
    exact (not_le_of_gt hP) (mul_nonpos_of_nonpos_of_nonneg hn (density_nonneg B))
  have hB : 0 < density B := by
    by_contra! hn
    exact (not_le_of_gt hP) (mul_nonpos_of_nonneg_of_nonpos (density_nonneg A) hn)
  obtain ⟨hk, hlog⟩ := log_widen hd hd'
  apply finish (a - 1) b _ _ (1 - d - 6 * d ^ 2) (by omega) hb (by omega) le_rfl
    (avoids_slice_inter havoid ha hab) hk
    (widenDensity hd hd' hA hB (not_le.mp ht).le (not_le.mp hf).le (not_le.mp hs).le)
  push_cast [Nat.cast_sub (show 1 ≤ a by omega)]
  convert hlog using 1; ring

-- The difference of interval widths counts the steps that paid for widening.
private theorem reductionTerminal {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1 / 10)
    (n a b : ℕ) (A B : Finset (Cube n)) (hab : a ≤ b) (hb : b ≤ n)
    (hP : 0 < density A * density B) (havoid : avoids a b A B) :
    ∃ (m i j : ℕ) (C D : Finset (Cube m)), i ≤ j ∧ j ≤ m ∧ m ≤ n ∧
      a + m ≤ i + n ∧ j ≤ b ∧ (i = 0 ∨ j = m) ∧
      avoids i j C D ∧ 0 < density C * density D ∧
      Real.log (density A * density B) +
          d * ((n : ℝ) - m - 2 * ((j : ℝ) - i - b + a)) - 10 * d ^ 2 * (n - (m : ℝ)) ≤
        Real.log (density C * density D) := by
  induction n generalizing a b with
  | zero =>
    have ha : a = 0 := by omega
    exact ⟨0, a, b, A, B, hab, hb, le_rfl, le_rfl, le_rfl, Or.inl ha, havoid, hP, by ring_nf; rfl⟩
  | succ n ih =>
    by_cases he : a = 0 ∨ b = n + 1
    · exact ⟨n + 1, a, b, A, B, hab, hb, le_rfl, le_rfl, le_rfl, he, havoid, hP, by ring_nf; rfl⟩
    obtain ⟨i, j, C, D, hij, hj, hi, hjb, hCD, hCDpos, hlog⟩ :=
      reductionStep hd hd' (by omega) hab (by omega) hP havoid
    obtain ⟨m, k, l, E, F, hkl, hlm, hmn, hik, hlj, hstop, hEF, hEFpos, hlog'⟩ :=
      ih i j C D hij hj hCDpos hCD
    refine ⟨m, k, l, E, F, hkl, hlm, by omega, by omega, hlj.trans hjb, hstop,
      hEF, hEFpos, ?_⟩
    push_cast
    linarith only [hlog, hlog']


/-! ## Concentration at each endpoint -/

private noncomputable def average {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  ∑ x, (1 / 2 : ℝ) ^ n * f x

private def BoundedDifferences {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ (i : Fin n) (x y : Cube n), (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ 1

private theorem density_upper_tail {n : ℕ} {C : Finset (Cube n)} {f : Cube n → ℝ}
    {t : ℝ} (ht : 0 < t) (hf : BoundedDifferences f)
    (hC : ∀ x ∈ C, t ≤ f x - average f) :
    density C ≤ Real.exp (-2 * t ^ 2 / n) := by
  classical
  have hp : (∑ _ : Bool, (1 / 2 : ℝ)) = 1 := by norm_num [Fintype.sum_bool]
  have h := MathlibExt.Probability.McDiarmid.mcdiarmid_one_sided_finite_iid
    (fun _ : Bool => (1 / 2 : ℝ)) (fun _ => by norm_num) hp f
    (fun _ => 1) (fun _ => zero_le_one) t ht hf
  have hv : (∑ _ : Fin n, (1 : ℝ) ^ 2) = n := by simp
  simp only [hv] at h
  have htail : density (univ.filter (fun x => t ≤ f x - average f)) ≤
      Real.exp (-2 * t ^ 2 / n) := by
    simpa [density, average, one_div_pow, div_eq_mul_inv] using h
  exact (density_mono (fun x hx => mem_filter.mpr ⟨mem_univ _, hC x hx⟩)).trans htail

private theorem density_lower_tail {n : ℕ} {C : Finset (Cube n)} {f : Cube n → ℝ}
    {t : ℝ} (ht : 0 < t) (hf : BoundedDifferences f)
    (hC : ∀ x ∈ C, t ≤ average f - f x) :
    density C ≤ Real.exp (-2 * t ^ 2 / n) := by
  have havg : average (-f) = -average f := by
    simp [average, mul_neg, sum_neg_distrib]
  apply density_upper_tail (f := -f) ht
  · intro i x y hxy
    change |(-f x) - (-f y)| ≤ 1
    rw [neg_sub_neg, abs_sub_comm]
    exact hf i x y hxy
  · intro x hx
    change t ≤ (-f x) - average (-f)
    rw [havg, neg_sub_neg]
    exact hC x hx

private theorem abs_count_sub_le {n : ℕ} {p q : Fin n → Prop}
    [DecidablePred p] [DecidablePred q] (i : Fin n) (heq : ∀ j, j ≠ i → (p j ↔ q j)) :
    |((∑ j, if p j then 1 else 0 : ℕ) : ℝ) - ((∑ j, if q j then 1 else 0 : ℕ) : ℝ)| ≤ 1 := by
  classical
  have hrest :
      (∑ j ∈ univ.erase i, if p j then (1 : ℝ) else 0) =
        ∑ j ∈ univ.erase i, if q j then (1 : ℝ) else 0 := by
    exact sum_congr rfl fun j hj => if_congr (heq j (mem_erase.mp hj).1) rfl rfl
  have hp := sum_erase_add univ (fun j => if p j then (1 : ℝ) else 0) (mem_univ i)
  have hq := sum_erase_add univ (fun j => if q j then (1 : ℝ) else 0) (mem_univ i)
  push_cast
  rw [← hp, ← hq, hrest]
  split_ifs <;> simp

private def complementEquiv (n : ℕ) : Cube n ≃ Cube n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

private theorem overlap_complement {n : ℕ} (x : Cube n) :
    overlap (complementEquiv n x) x = 0 := by
  unfold overlap
  apply sum_eq_zero
  intro i _
  cases hx : x i <;> simp [complementEquiv, hx]

-- If every cross-intersection is large, the minimum intersection with the first family
-- separates the second family from all complements of the first.
private theorem density_avoids_initial {n b : ℕ} {A B : Finset (Cube n)}
    (hA : A.Nonempty) (hb : 0 < b) (havoid : avoids 0 b A B) :
    density A * density B ≤ Real.exp (-(b : ℝ) ^ 2 / (2 * n)) := by
  classical
  let f (x : Cube n) : ℝ := A.inf' hA (fun a => (overlap x a : ℝ))
  have hbd : BoundedDifferences f := by
    intro i x y hxy
    have hstep (x y : Cube n) (heq : ∀ j, j ≠ i → x j = y j) : f x - 1 ≤ f y := by
      apply le_inf'
      intro a ha
      have hle : f x ≤ (overlap x a : ℝ) := inf'_le (fun z => (overlap x z : ℝ)) ha
      have hab : |(overlap x a : ℝ) - (overlap y a : ℝ)| ≤ 1 := by
        exact abs_count_sub_le i (fun j hj => by rw [heq j hj])
      linarith [(abs_le.mp hab).2]
    exact abs_le.mpr ⟨by linarith [hstep y x (fun j hj => (hxy j hj).symm)],
      by linarith [hstep x y hxy]⟩
  have hzero : ∀ x ∈ A.map (complementEquiv n).toEmbedding, f x ≤ 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    have hle := inf'_le (fun z => (overlap (complementEquiv n a) z : ℝ)) ha
    change f (complementEquiv n a) ≤ 0
    simpa only [overlap_complement, Nat.cast_zero, f] using hle
  have hlarge : ∀ x ∈ B, (b : ℝ) ≤ f x := by
    intro x hx
    apply le_inf'
    intro a ha
    have hn := avoids_comm.mp havoid x hx a ha
    exact_mod_cast (show b ≤ overlap x a by omega)
  have ht : 0 < (b : ℝ) / 2 := by positivity
  have he : -2 * ((b : ℝ) / 2) ^ 2 / n = -(b : ℝ) ^ 2 / (2 * n) := by ring
  rw [← he]
  by_cases hmean : (b : ℝ) / 2 ≤ average f
  · have htail := density_lower_tail ht hbd
      (C := A.map (complementEquiv n).toEmbedding) (fun x hx => by linarith [hzero x hx])
    rw [density_map] at htail
    exact (mul_le_of_le_one_right (density_nonneg A) (density_le_one B)).trans htail
  · have htail := density_upper_tail ht hbd (C := B) (fun x hx => by linarith [hlarge x hx])
    exact (mul_le_of_le_one_left (density_nonneg B) (density_le_one A)).trans htail

private noncomputable def weight {n : ℕ} (x : Cube n) : ℝ := overlap x x

private theorem weight_eq_card {n : ℕ} (x : Cube n) :
    weight x = (supportEquiv n x).card := by
  rw [weight, overlap_eq_card, inter_self]

private theorem weight_boundedDifferences {n : ℕ} : BoundedDifferences (weight (n := n)) := by
  intro i x y hxy
  exact abs_count_sub_le i (fun j hj => by rw [hxy j hj])

private theorem average_weight (n : ℕ) : average (weight (n := n)) = (n : ℝ) / 2 := by
  classical
  have hcomp (x : Cube n) : weight x + weight (complementEquiv n x) = n := by
    simp only [weight, overlap, and_self, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← sum_add_distrib]
    calc
      _ = ∑ _i : Fin n, (1 : ℝ) := by
        apply sum_congr rfl
        intro i _
        cases hx : x i <;> simp [complementEquiv, hx]
      _ = n := by simp
  have h := (complementEquiv n).sum_comp (fun x => (1 / 2 : ℝ) ^ n * weight x)
  change (∑ x, (1 / 2 : ℝ) ^ n * weight (complementEquiv n x)) = average weight at h
  have hnorm : (∑ _x : Cube n, (1 / 2 : ℝ) ^ n * n) = n := by
    simp
  have hadd : average (weight (n := n)) +
      (∑ x, (1 / 2 : ℝ) ^ n * weight (complementEquiv n x)) = n := by
    rw [average, ← sum_add_distrib, ← hnorm]
    exact sum_congr rfl fun x _ => by rw [← mul_add, hcomp]
  linarith

private noncomputable def lowerFamily {n : ℕ} (A : Finset (Cube n)) : Finset (Finset (Fin n)) := by
  classical exact univ.filter (fun s => ∃ x ∈ A, s ⊆ supportEquiv n x)

private theorem mem_lowerFamily {n : ℕ} {A : Finset (Cube n)} {s : Finset (Fin n)} :
    s ∈ lowerFamily A ↔ ∃ x ∈ A, s ⊆ supportEquiv n x := by
  classical simp [lowerFamily]

private theorem isLowerSet_lowerFamily {n : ℕ} (A : Finset (Cube n)) :
    IsLowerSet (lowerFamily A : Set (Finset (Fin n))) := by
  intro s t hts hs
  obtain ⟨x, hx, hsub⟩ := mem_lowerFamily.mp hs
  exact mem_lowerFamily.mpr ⟨x, hx, hts.trans hsub⟩

private theorem card_le_lowerFamily {n : ℕ} (A : Finset (Cube n)) : A.card ≤ (lowerFamily A).card :=
  (card_map (f := (supportEquiv n).toEmbedding) (s := A)).ge.trans <|
    card_le_card fun s hs => by
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
      exact mem_lowerFamily.mpr ⟨x, hx, Subset.rfl⟩

-- The downward closures still have small cross-intersections. Harris–Kleitman
-- bounds their density product by the lower tail of the size of a single set.
private theorem density_avoids_final {n a : ℕ} {A B : Finset (Cube n)}
    {t : ℝ} (ht : 0 < t) (hsmall : (a : ℝ) ≤ (n : ℝ) / 2 - t)
    (havoid : avoids a n A B) :
    density A * density B ≤ Real.exp (-2 * t ^ 2 / n) := by
  classical
  let C := (lowerFamily A ∩ lowerFamily B).map (supportEquiv n).symm.toEmbedding
  have hcard : A.card * B.card ≤ 2 ^ n * C.card := by
    exact (Nat.mul_le_mul (card_le_lowerFamily A) (card_le_lowerFamily B)).trans
      (by simpa [C] using
        (isLowerSet_lowerFamily A).le_card_inter_finset (isLowerSet_lowerFamily B))
  have hprod : density A * density B ≤ density C := by
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hcast : (A.card : ℝ) * B.card ≤ 2 ^ n * C.card := by exact_mod_cast hcard
    simp only [density, div_mul_div_comm]
    rw [div_le_div_iff₀ (mul_pos hp hp) hp]
    calc
      _ ≤ ((2 : ℝ) ^ n * C.card) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hcast hp.le
      _ = _ := by ring
  apply hprod.trans (density_lower_tail ht weight_boundedDifferences ?_)
  intro x hx
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hx
  obtain ⟨y, hy, hys⟩ := mem_lowerFamily.mp (mem_inter.mp hs).1
  obtain ⟨z, hz, hzs⟩ := mem_lowerFamily.mp (mem_inter.mp hs).2
  have hle : s.card ≤ overlap y z := by
    rw [overlap_eq_card]
    exact card_le_card (subset_inter hys hzs)
  have hover := havoid y hy z hz
  have hs' : (s.card : ℝ) ≤ a := by
    exact_mod_cast (show s.card ≤ a by have := overlap_le y z; omega)
  simp only [average_weight, weight_eq_card, Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  linarith


/-! ## Exponential bound -/

private theorem density_bound {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 4)
    {n r : ℕ} (hn : 0 < n) (hrlo : ε * n < r) (hrhi : (r : ℝ) < (1 / 2 - ε) * n)
    {A B : Finset (Cube n)} (havoid : avoids r r A B) :
    density A * density B ≤ Real.exp (-((ε ^ 2 / 1000) ^ 2) * n) := by
  let d := ε ^ 2 / 1000
  change density A * density B ≤ Real.exp (-d ^ 2 * n)
  have hd : 0 < d := by dsimp [d]; positivity
  have hεsq : ε ^ 2 ≤ ε := by
    nlinarith [mul_nonneg hε.le (show 0 ≤ 1 - ε by linarith)]
  have hd' : d ≤ 1 / 100 := by dsimp [d]; linarith
  have hη : 11 * d ≤ ε / 2 := by dsimp [d]; linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : r ≤ n := by
    have : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le hn'.le
    exact_mod_cast (show (r : ℝ) ≤ n by linarith)
  by_contra! hlarge
  have hP : 0 < density A * density B := (Real.exp_pos _).trans hlarge
  have hstart : -d ^ 2 * n < Real.log (density A * density B) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlarge
  obtain ⟨m, i, j, C, D, hij, hjm, hmn, hlow, hjr, hend, hCD, hCDpos, hlog⟩ :=
    reductionTerminal hd (by linarith) n r r A B le_rfl hrn hP havoid
  simp only [sub_add_cancel] at hlog
  have hCDle : density C * density D ≤ 1 :=
    (mul_le_of_le_one_right (density_nonneg C) (density_le_one D)).trans (density_le_one C)
  have hlogle := Real.log_nonpos hCDpos.le hCDle
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlow' : (r : ℝ) + m ≤ i + n := by exact_mod_cast hlow
  have hbudget : (n : ℝ) - m - 2 * ((j : ℝ) - i) ≤ ε * n / 2 := by
    have hcost : 10 * d ^ 2 * ((n : ℝ) - m) ≤ 10 * d ^ 2 * n :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hprogress : (n : ℝ) - m - 2 * ((j : ℝ) - i) ≤ 11 * d * n := by
      apply le_of_mul_le_mul_left _ hd
      linarith only [hlog, hstart, hlogle, hcost]
    exact hprogress.trans (by linarith [mul_le_mul_of_nonneg_right hη hn'.le])
  have hlower : -(3 * d * n) < Real.log (density C * density D) := by
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast hjm.trans hmn
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hwidth : -(2 * (n : ℝ)) ≤ (n : ℝ) - m - 2 * ((j : ℝ) - i) := by linarith
    have hw := mul_le_mul_of_nonneg_left hwidth hd.le
    have hcost : 10 * d ^ 2 * ((n : ℝ) - m) ≤ 10 * d ^ 2 * n :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hsmall : 11 * d ^ 2 * n ≤ d * n := by
      nlinarith only [mul_nonneg (show 0 ≤ 1 - 11 * d by linarith)
        (show 0 ≤ d * (n : ℝ) by positivity)]
    linarith only [hstart, hlog, hw, hcost, hsmall]
  let t := ε * (n : ℝ) / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hscale (hm' : (0 : ℝ) < m) : -(t ^ 2) / (2 * m) ≤ -(ε ^ 2 * n / 32) := by
    apply (div_le_iff₀ (show (0 : ℝ) < 2 * m by positivity)).2
    have h := mul_le_mul_of_nonneg_left hmn' (show 0 ≤ ε ^ 2 * n / 16 by positivity)
    dsimp [t]
    linarith only [h]
  have hupper : density C * density D ≤ Real.exp (-(ε ^ 2 * n / 32)) := by
    rcases hend with hi | hj
    · subst i
      have hlow' : (r : ℝ) + m ≤ n := by simpa using hlow'
      have hsize : t ≤ j := by dsimp [t]; push_cast at hbudget; linarith [hrlo]
      have hjpos : (0 : ℝ) < j := ht.trans_le hsize
      have hmpos : (0 : ℝ) < m := hjpos.trans_le (by exact_mod_cast hjm)
      have hCpos : 0 < density C := by
        exact pos_of_mul_pos_left hCDpos (density_nonneg D)
      have hC : C.Nonempty := by
        by_contra! h
        rw [h, density, card_empty, Nat.cast_zero, zero_div] at hCpos
        exact (lt_irrefl _ hCpos)
      have h := density_avoids_initial hC (by exact_mod_cast hjpos) hCD
      apply h.trans
      apply Real.exp_le_exp.mpr
      exact (div_le_div_of_nonneg_right (neg_le_neg (pow_le_pow_left₀ ht.le hsize 2))
        (by positivity : (0 : ℝ) ≤ 2 * m)).trans (hscale hmpos)
    · subst j
      have hmr : (m : ℝ) ≤ r := by exact_mod_cast hjr
      have hsmall : (i : ℝ) ≤ (m : ℝ) / 2 - t := by
        dsimp [t]
        linarith only [hbudget, hmr, hrhi, mul_nonneg hε.le hn'.le]
      have hmpos : (0 : ℝ) < m := by
        linarith [Nat.cast_nonneg (α := ℝ) i]
      apply (density_avoids_final ht hsmall hCD).trans
      apply Real.exp_le_exp.mpr
      apply le_trans _ (hscale hmpos)
      have hscale2 : -2 * t ^ 2 / (m : ℝ) ≤ -(t ^ 2) / (2 * m) := by
        rw [div_mul_eq_div_div_swap]
        have hpos : 0 ≤ t ^ 2 / (m : ℝ) := by positivity
        rw [mul_div_assoc, neg_mul, neg_div]
        linarith
      exact hscale2
  have hlogUpper := Real.log_le_log hCDpos hupper
  rw [Real.log_exp] at hlogUpper
  have hcontr : 3 * d * n ≤ ε ^ 2 * n / 32 := by
    dsimp [d]
    linarith only [show 0 ≤ ε ^ 2 * (n : ℝ) by positivity]
  linarith only [hlower, hlogUpper, hcontr]

/--
**Frankl–Rödl forbidden intersection theorem.** For every $\varepsilon > 0$ there is $\delta > 0$
such that for all natural numbers $n$ and $r$ with $\varepsilon n < r < (1/2 - \varepsilon) n$,
every family $\mathcal{F}$ of subsets of $\{1, \dots, n\}$ with $|A \cap B| \ne r$ for all
$A, B \in \mathcal{F}$ (including $A = B$) has $|\mathcal{F}| < (2 - \delta)^n$. This answers the
second question of Erdős Problem 703 in the affirmative.

Source: T.
F. Bloom, Erdős Problems, Problem #703, https://www.erdosproblems.com/703 (status PROVED (LEAN));
resolution: P. Frankl and V. Rödl, Forbidden intersections, Trans. Amer. Math. Soc. 300 (1987),
259-286, erdosproblems.com/703: 'The answer to the second question is yes, proved by Frankl and
Rödl', https://www.erdosproblems.com/703.
-/
theorem forbiddenIntersectionExponentialGap_holds : forbiddenIntersectionExponentialGap := by
  intro ε hε
  let e := min ε (1 / 4)
  have he : 0 < e := lt_min hε (by norm_num)
  let d := e ^ 2 / 1000
  have hd : 0 < d := by dsimp [d]; positivity
  let c := d ^ 2 / 4
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2 - 2 * Real.exp (-c), ?_, ?_⟩
  · linarith [Real.exp_lt_one_iff.mpr (neg_neg_of_pos hc)]
  intro n r hlo hhi F hF
  have hn : 0 < n := by
    by_contra! h
    have hn0 : n = 0 := by omega
    exact (not_lt_of_ge (Nat.cast_nonneg (α := ℝ) r)) (by simpa [hn0] using hhi)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen := mul_le_mul_of_nonneg_right (min_le_left ε (1 / 4)) hn'.le
  let A := F.map (supportEquiv n).symm.toEmbedding
  have hA : avoids r r A A := by
    intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hy
    apply hF s hs t ht
    simpa only [overlap_eq_card, Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using
      (le_antisymm hxy.2 hxy.1)
  have hbound := density_bound he (min_le_right ε (1 / 4)) hn
    (hen.trans_lt hlo) (show (r : ℝ) < (1 / 2 - e) * n by linarith [hhi]) hA
  change density A * density A ≤ Real.exp (-d ^ 2 * n) at hbound
  have hdensity : density A < Real.exp (-c * n) := by
    by_contra! h
    have hp := (mul_le_mul h h (Real.exp_pos _).le (density_nonneg A)).trans hbound
    rw [← Real.exp_add, Real.exp_le_exp] at hp
    have hh : 0 < d ^ 2 * (n : ℝ) := by positivity
    dsimp [c] at hp
    linarith only [hp, hh]
  rw [density, card_map, div_lt_iff₀ (by positivity)] at hdensity
  rw [show 2 - (2 - 2 * Real.exp (-c)) = 2 * Real.exp (-c) by ring,
    mul_pow, ← Real.exp_nat_mul]
  simpa only [mul_comm] using hdensity

end MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703Wanted
