/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.IrrationalStepProgressions
import Mathlib.Data.Int.Interval

/-!
# The union of an interval and an integer progression is not MSTD

Counting sums and differences of `I_n ∪ J(x, m, d)` in the integer lattice.
-/

namespace MetaMathlibExt

open scoped Pointwise

private def latI (n : ℕ) : Finset ℤ := Finset.Icc 0 ((n : ℤ) - 1)

private def latJ (m d x : ℕ) : Finset ℤ :=
  (Finset.range (m + 1)).image fun i : ℕ => (x : ℤ) + (i : ℤ) * (d : ℤ)

private def latC (n : ℕ) : Finset ℤ := Finset.Icc 0 (2 * (n : ℤ) - 2)

private def latE (n m d x : ℕ) : Finset ℤ :=
  (Finset.range (m + 1)).biUnion fun i : ℕ =>
    Finset.Icc ((x : ℤ) + (i : ℤ) * (d : ℤ)) ((x : ℤ) + (i : ℤ) * (d : ℤ) + (n : ℤ) - 1)

private def latK (m d x : ℕ) : Finset ℤ :=
  (Finset.range (2 * m + 1)).image fun k : ℕ => 2 * (x : ℤ) + (k : ℤ) * (d : ℤ)

private def latF (n m d x : ℕ) : Finset ℤ :=
  (Finset.range (m + 1)).biUnion fun i : ℕ =>
    Finset.Icc ((x : ℤ) + (i : ℤ) * (d : ℤ) - (n : ℤ) + 1) ((x : ℤ) + (i : ℤ) * (d : ℤ))

private def latG (n m d x : ℕ) : Finset ℤ :=
  (latF n m d x).filter fun t => (n : ℤ) ≤ t

private def latCp (n : ℕ) : Finset ℤ := Finset.Icc (-((n : ℤ) - 1)) ((n : ℤ) - 1)

private def latP (m d x : ℕ) : Finset ℤ :=
  (Finset.range (m + 1)).image fun i : ℕ => (x : ℤ) + (i : ℤ) * (d : ℤ) - 1

private def latQ (m d x : ℕ) : Finset ℤ :=
  (Finset.range (m + 1)).image fun i : ℕ => (x : ℤ) + (i : ℤ) * (d : ℤ)

-- The interval `I_n` is the integer image of `Icc 0 (n - 1)`.
private theorem image_latI (n : ℕ) :
    (latI n).image ((↑) : ℤ → ℝ) = realIntervalSet n := by
  ext z
  simp only [latI, realIntervalSet, Finset.mem_image, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    have htn : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg h0
    refine ⟨t.toNat, by omega, ?_⟩
    rw [← Int.cast_natCast, htn]
  · rintro ⟨i, himem, rfl⟩
    exact ⟨(i : ℤ), ⟨by omega, by omega⟩, Int.cast_natCast i⟩

-- The progression `J` is the integer image of its lattice points.
private theorem image_latJ (m d x : ℕ) :
    (latJ m d x).image ((↑) : ℤ → ℝ) = realAPSet (x : ℝ) m (d : ℝ) := by
  ext z
  simp only [latJ, realAPSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ⟨j, hjmem, rfl⟩, rfl⟩
    exact ⟨j, hjmem, by push_cast; ring⟩
  · rintro ⟨j, hjmem, rfl⟩
    exact ⟨(x : ℤ) + (j : ℤ) * (d : ℤ), ⟨j, hjmem, rfl⟩, by push_cast; ring⟩

private theorem image_sub_intCast (s t : Finset ℤ) :
    (s - t).image ((↑) : ℤ → ℝ) = s.image ((↑) : ℤ → ℝ) - t.image ((↑) : ℤ → ℝ) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_sub]
  constructor
  · rintro ⟨u, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨(a : ℝ), ⟨a, ha, rfl⟩, (b : ℝ), ⟨b, hb, rfl⟩, by push_cast; ring⟩
  · rintro ⟨u, ⟨a, ha, rfl⟩, v, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, by push_cast; ring⟩

-- Every sum lies in the initial interval, a cross block, or a pure `J + J` sum.
private theorem sum_subset (n m d x : ℕ) :
    (latI n ∪ latJ m d x) + (latI n ∪ latJ m d x)
      ⊆ latC n ∪ latE n m d x ∪ latK m d x := by
  intro s hs
  simp only [Finset.mem_add, Finset.mem_union] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  simp only [latI, latJ, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at ha hb
  rcases ha with ha | ⟨i, hi, rfl⟩ <;> rcases hb with hb | ⟨j, hj, rfl⟩
  · simp only [Finset.mem_union, latC, Finset.mem_Icc]
    exact Or.inl (Or.inl ⟨by omega, by omega⟩)
  · simp only [Finset.mem_union, latE, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_Icc]
    exact Or.inl (Or.inr ⟨j, hj, by omega, by omega⟩)
  · simp only [Finset.mem_union, latE, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_Icc]
    exact Or.inl (Or.inr ⟨i, hi, by omega, by omega⟩)
  · simp only [Finset.mem_union, latK, Finset.mem_image, Finset.mem_range]
    refine Or.inr ⟨i + j, by omega, ?_⟩
    push_cast
    ring

private theorem card_latC (n : ℕ) (hn : 3 ≤ n) : (latC n).card = 2 * n - 1 := by
  simp only [latC, Int.card_Icc]
  omega

private theorem card_latK_le (m d x : ℕ) : (latK m d x).card ≤ 2 * m + 1 := by
  have h : (latK m d x).card ≤ (Finset.range (2 * m + 1)).card := by
    simp only [latK]
    exact Finset.card_image_le
  rwa [Finset.card_range] at h

-- Shifting the large cross differences by `n - 1` gives the large cross sums.
private theorem image_latG (n m d x : ℕ) :
    (latG n m d x).image (fun t : ℤ => t + ((n : ℤ) - 1))
      = (latE n m d x).filter fun s => 2 * (n : ℤ) - 1 ≤ s := by
  ext s
  simp only [latG, latF, latE, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨t, htmem, hts⟩
    obtain ⟨⟨i, hi, h1, h2⟩, h3⟩ := htmem
    subst s
    exact ⟨⟨i, hi, by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨i, hi, h1, h2⟩, h3⟩
    refine ⟨s - ((n : ℤ) - 1), ⟨⟨i, hi, by omega, by omega⟩, by omega⟩, ?_⟩
    omega

private theorem sdiff_latE_subset (n m d x : ℕ) :
    latE n m d x \ latC n ⊆ (latE n m d x).filter fun s => 2 * (n : ℤ) - 1 ≤ s := by
  intro s hs
  simp only [Finset.mem_sdiff, Finset.mem_filter] at hs ⊢
  obtain ⟨hsE, hsC⟩ := hs
  refine ⟨hsE, ?_⟩
  simp only [latE, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc] at hsE
  simp only [latC, Finset.mem_Icc] at hsC
  obtain ⟨i, hi, h1, h2⟩ := hsE
  have hnn : (0 : ℤ) ≤ (x : ℤ) + (i : ℤ) * (d : ℤ) := by positivity
  omega

-- The central interval lies in `I - I`.
private theorem central_subset (n m d x : ℕ) :
    latCp n ⊆ (latI n ∪ latJ m d x) - (latI n ∪ latJ m d x) := by
  intro t ht
  simp only [latCp, Finset.mem_Icc] at ht
  refine Finset.mem_sub.mpr ⟨max t 0, Finset.mem_union_left _ ?_, max (-t) 0,
    Finset.mem_union_left _ ?_, by omega⟩
  · simp only [latI, Finset.mem_Icc]
    omega
  · simp only [latI, Finset.mem_Icc]
    omega

-- Each cross block lies in `J - I`.
private theorem latF_subset (n m d x : ℕ) :
    latF n m d x ⊆ (latI n ∪ latJ m d x) - (latI n ∪ latJ m d x) := by
  intro t ht
  simp only [latF, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc] at ht
  obtain ⟨i, hi, h1, h2⟩ := ht
  refine Finset.mem_sub.mpr ⟨(x : ℤ) + (i : ℤ) * (d : ℤ), Finset.mem_union_right _ ?_,
    (x : ℤ) + (i : ℤ) * (d : ℤ) - t, Finset.mem_union_left _ ?_, by omega⟩
  · simp only [latJ, Finset.mem_image, Finset.mem_range]
    exact ⟨i, hi, rfl⟩
  · simp only [latI, Finset.mem_Icc]
    omega

private theorem latG_subset (n m d x : ℕ) :
    latG n m d x ⊆ (latI n ∪ latJ m d x) - (latI n ∪ latJ m d x) := by
  intro t ht
  simp only [latG, Finset.mem_filter] at ht
  exact latF_subset n m d x ht.1

private theorem neg_latG_subset (n m d x : ℕ) :
    (latG n m d x).image Neg.neg
      ⊆ (latI n ∪ latJ m d x) - (latI n ∪ latJ m d x) := by
  intro s hs
  simp only [Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_sub.mp (latG_subset n m d x ht)
  exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by omega⟩

private theorem disjoint_central_latG (n m d x : ℕ) :
    Disjoint (latCp n) (latG n m d x) := by
  rw [Finset.disjoint_left]
  intro t htC htG
  simp only [latCp, Finset.mem_Icc] at htC
  simp only [latG, Finset.mem_filter] at htG
  omega

private theorem disjoint_central_neg (n m d x : ℕ) :
    Disjoint (latCp n) ((latG n m d x).image Neg.neg) := by
  rw [Finset.disjoint_left]
  intro t htC htG
  simp only [latCp, Finset.mem_Icc] at htC
  simp only [Finset.mem_image, latG, Finset.mem_filter] at htG
  obtain ⟨u, ⟨huF, huN⟩, rfl⟩ := htG
  omega

private theorem disjoint_latG_neg (n m d x : ℕ) (hn : 3 ≤ n) :
    Disjoint (latG n m d x) ((latG n m d x).image Neg.neg) := by
  rw [Finset.disjoint_left]
  intro t htG1 htG2
  simp only [latG, Finset.mem_filter] at htG1
  simp only [Finset.mem_image, latG, Finset.mem_filter] at htG2
  obtain ⟨u, ⟨huF, huN⟩, rfl⟩ := htG2
  omega

private theorem card_latCp (n : ℕ) (hn : 3 ≤ n) : (latCp n).card = 2 * n - 1 := by
  simp only [latCp, Int.card_Icc]
  omega

private theorem latP_subset (n m d x : ℕ) (hn : 3 ≤ n) (hx₁ : n + 1 ≤ x) :
    latP m d x ⊆ latG n m d x := by
  intro p hp
  simp only [latP, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hnn : (0 : ℤ) ≤ (i : ℤ) * (d : ℤ) := by positivity
  simp only [latG, latF, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_Icc]
  refine ⟨⟨i, hi, by omega, by omega⟩, by omega⟩

private theorem latQ_subset (n m d x : ℕ) (hn : 3 ≤ n) (hx₁ : n + 1 ≤ x) :
    latQ m d x ⊆ latG n m d x := by
  intro p hp
  simp only [latQ, Finset.mem_image, Finset.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hnn : (0 : ℤ) ≤ (i : ℤ) * (d : ℤ) := by positivity
  simp only [latG, latF, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_Icc]
  refine ⟨⟨i, hi, by omega, by omega⟩, by omega⟩

private theorem card_latP (m d x : ℕ) (hd : 2 ≤ d) : (latP m d x).card = m + 1 := by
  have hinj : Function.Injective
      (fun i : ℕ => (x : ℤ) + (i : ℤ) * (d : ℤ) - 1) := by
    intro i j h
    dsimp only at h
    have h2 : (i : ℤ) * (d : ℤ) = (j : ℤ) * (d : ℤ) := by omega
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hij : (i : ℤ) = (j : ℤ) := mul_right_cancel₀ hd0 h2
    exact_mod_cast hij
  unfold latP
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

private theorem card_latQ (m d x : ℕ) (hd : 2 ≤ d) : (latQ m d x).card = m + 1 := by
  have hinj : Function.Injective
      (fun i : ℕ => (x : ℤ) + (i : ℤ) * (d : ℤ)) := by
    intro i j h
    dsimp only at h
    have h2 : (i : ℤ) * (d : ℤ) = (j : ℤ) * (d : ℤ) := by omega
    have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hij : (i : ℤ) = (j : ℤ) := mul_right_cancel₀ hd0 h2
    exact_mod_cast hij
  unfold latQ
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

private theorem disjoint_latP_latQ (m d x : ℕ) (hd : 2 ≤ d) :
    Disjoint (latP m d x) (latQ m d x) := by
  rw [Finset.disjoint_left]
  intro t htP htQ
  simp only [latP, Finset.mem_image, Finset.mem_range] at htP
  simp only [latQ, Finset.mem_image, Finset.mem_range] at htQ
  obtain ⟨i, hi, rfl⟩ := htP
  obtain ⟨j, hj, hji⟩ := htQ
  have h3 : (i : ℤ) * (d : ℤ) - (j : ℤ) * (d : ℤ) = 1 := by omega
  have h2 : ((i : ℤ) - (j : ℤ)) * (d : ℤ) = 1 := by rw [sub_mul]; exact h3
  have hdiv : (d : ℤ) ∣ 1 := ⟨(i : ℤ) - (j : ℤ), by rw [mul_comm]; exact h2.symm⟩
  have hd1 : (d : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdiv
  have hdeq : d = 1 := by exact_mod_cast hd1
  omega

-- In the integer lattice, the sumset is no larger than the difference set.
private theorem card_add_le_card_sub (n m d x : ℕ) (hn : 3 ≤ n) (hd : 2 ≤ d)
    (hx₁ : n + 1 ≤ x) :
    ((latI n ∪ latJ m d x) + (latI n ∪ latJ m d x)).card
      ≤ ((latI n ∪ latJ m d x) - (latI n ∪ latJ m d x)).card := by
  have hsub := sum_subset n m d x
  have hcardUE : (latC n ∪ latE n m d x).card
      = (latC n).card + (latE n m d x \ latC n).card := by
    rw [Finset.union_comm, ← Finset.card_sdiff_add_card, add_comm]
  have hC := card_latC n hn
  have hK := card_latK_le m d x
  have himg := image_latG n m d x
  have hinj : Function.Injective (fun t : ℤ => t + ((n : ℤ) - 1)) := by
    intro a b h
    dsimp only at h
    omega
  have hcardG : ((latE n m d x).filter fun s => 2 * (n : ℤ) - 1 ≤ s).card
      = (latG n m d x).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  have hsdiff := sdiff_latE_subset n m d x
  have hle1 : ((latI n ∪ latJ m d x) + (latI n ∪ latJ m d x)).card
      ≤ 2 * n - 1 + (latG n m d x).card + (2 * m + 1) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (latC n ∪ latE n m d x) (latK m d x)
    have h3 := Finset.card_le_card hsdiff
    omega
  have hCp := card_latCp n hn
  have hsubC := central_subset n m d x
  have hsubG := latG_subset n m d x
  have hsubGn := neg_latG_subset n m d x
  have hdisj1 := disjoint_central_latG n m d x
  have hdisj2 := disjoint_central_neg n m d x
  have hdisj3 := disjoint_latG_neg n m d x hn
  have hdisjU : Disjoint (latCp n ∪ latG n m d x) ((latG n m d x).image Neg.neg) :=
    (Finset.disjoint_union_left).mpr ⟨hdisj2, hdisj3⟩
  have hcardD : (latCp n ∪ latG n m d x ∪ (latG n m d x).image Neg.neg).card
      = (2 * n - 1) + (latG n m d x).card + (latG n m d x).card := by
    rw [Finset.card_union_of_disjoint hdisjU, Finset.card_union_of_disjoint hdisj1,
      hCp, Finset.card_image_of_injective _ neg_injective]
  have hsubD : latCp n ∪ latG n m d x ∪ (latG n m d x).image Neg.neg
      ⊆ (latI n ∪ latJ m d x) - (latI n ∪ latJ m d x) := by
    intro t ht
    simp only [Finset.mem_union] at ht
    rcases ht with (ht | ht) | ht
    · exact hsubC ht
    · exact hsubG ht
    · exact hsubGn ht
  have hle2 : 2 * n - 1 + (latG n m d x).card + (latG n m d x).card
      ≤ ((latI n ∪ latJ m d x) - (latI n ∪ latJ m d x)).card := by
    have h := Finset.card_le_card hsubD
    omega
  have hPQsub : latP m d x ∪ latQ m d x ⊆ latG n m d x :=
    Finset.union_subset (latP_subset n m d x hn hx₁) (latQ_subset n m d x hn hx₁)
  have hPQcard : (latP m d x ∪ latQ m d x).card = (m + 1) + (m + 1) := by
    rw [Finset.card_union_of_disjoint (disjoint_latP_latQ m d x hd),
      card_latP m d x hd, card_latQ m d x hd]
  have hG : 2 * m + 1 ≤ (latG n m d x).card := by
    have h := Finset.card_le_card hPQsub
    omega
  omega

-- Retain the named hypotheses of the source statement.
set_option linter.unusedVariables false in
/-- **Interval plus integer progression starting in $[n + 1, 2n - 2]$ is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x$ with
$n + 1 \le x \le 2n - 2$, the set $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 1
(`integers-2026-A58-lem-1`). -/
public theorem not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx₁ : n + 1 ≤ x) (hx₂ : x ≤ 2 * n - 2) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
  have hI := image_latI n
  have hJ := image_latJ m d x
  have hA : (latI n ∪ latJ m d x).image ((↑) : ℤ → ℝ)
      = realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ) := by
    rw [Finset.image_union, hI, hJ]
  have hadd : ((latI n ∪ latJ m d x) + (latI n ∪ latJ m d x)).image ((↑) : ℤ → ℝ)
      = (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))
        + (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
    rw [← hA]
    exact Finset.image_add (Int.castRingHom ℝ)
  have hsub : ((latI n ∪ latJ m d x) - (latI n ∪ latJ m d x)).image ((↑) : ℤ → ℝ)
      = (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))
        - (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ)) := by
    rw [image_sub_intCast, hA]
  have hle := card_add_le_card_sub n m d x hn hd hx₁
  have hinjR : Function.Injective ((↑) : ℤ → ℝ) := Int.cast_injective
  simp only [IsMSTDSet]
  rw [← hadd, ← hsub, Finset.card_image_of_injective _ hinjR,
    Finset.card_image_of_injective _ hinjR]
  omega

end MetaMathlibExt
