/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

/-!
# A permanent matrix method for bounded asymptotically convergent sequences

There is one permanent matrix that sums a bounded real sequence to `S` exactly when some
strictly increasing subsequence of density one converges to `S`. Its rows are the uniform
averages over subsets containing at least half the indices of a nonempty initial interval.
The positive construction is the one in issue #8392; it is not attributed to Mazur.
-/

@[expose] public section

namespace MathlibExt.Analysis.Series.ScottishBook5BoundedWanted

/-- **Index sequences of density one.** A sequence $s \colon \mathbb{N} \to \mathbb{N}$ has
density one when it is strictly increasing and $s(n+1)/(n+1) \to 1$ as $n \to \infty$.

For a strictly increasing sequence of natural numbers this ratio condition is equivalent to the
usual counting definition of density $1$ for its set of values. -/
def HasDensityOne (s : ℕ → ℕ) : Prop :=
  StrictMono s ∧
  Filter.Tendsto (fun n => ((s (n + 1) : ℝ)) / ((n : ℝ) + 1)) Filter.atTop (nhds 1)

/-- **Asymptotically convergent sequences.** A real sequence $(x_n)_{n \in \mathbb{N}}$ is
asymptotically convergent to a real number $S$ when there is an index sequence $s$ of density
one such that $x_{s(n)} \to S$ as $n \to \infty$.

Source: this is the typescript's definition, verbatim in content. -/
def AsymptoticallyConvergent (x : ℕ → ℝ) (S : ℝ) : Prop :=
  ∃ s : ℕ → ℕ, HasDensityOne s ∧ Filter.Tendsto (x ∘ s) Filter.atTop (nhds S)

/-- **Summation by a matrix method.** A real matrix $(a_{ik})_{i,k \in \mathbb{N}}$ sums a real
sequence $(x_k)_{k \in \mathbb{N}}$ to a real number $S$ when for every row $i$ the series
$\sum_k a_{ik} x_k$ converges unconditionally (equivalently, absolutely) and the row sums
$\sum_k a_{ik} x_k$ tend to $S$ as $i \to \infty$. -/
def MatrixSums (a : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (S : ℝ) : Prop :=
  (∀ i : ℕ, Summable (fun k => a i k * x k)) ∧
  Filter.Tendsto (fun i => ∑' k, a i k * x k) Filter.atTop (nhds S)

/-- **Permanent matrix methods.** A real matrix $(a_{ik})_{i,k \in \mathbb{N}}$ is a permanent
(regular, or Toeplitz) method when it sums every convergent real sequence to its limit: for every
real sequence $x$ and real number $S$ with $x_n \to S$, the matrix sums $x$ to $S$.

The Silverman–Toeplitz conditions characterise exactly these methods.

Source: "Toeplitz method" is pinned to this standard reading; the typescript does not define it. -/
def IsPermanent (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ x : ℕ → ℝ, ∀ S : ℝ, Filter.Tendsto x Filter.atTop (nhds S) → MatrixSums a x S

/-- **Bounded sequences.** A real sequence $(x_n)_{n \in \mathbb{N}}$ is bounded when there is a
real number $B$ with $|x_n| \le B$ for all $n$. -/
def IsBounded (x : ℕ → ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, |x n| ≤ B

/-- **The bounded case of Scottish Book Problem 5.** There is a real matrix
$(a_{ik})_{i,k \in \mathbb{N}}$ that is a permanent matrix method such that for every bounded real
sequence $x$ and every real number $S$, the matrix sums $x$ to $S$ if and only if $x$ is
asymptotically convergent to $S$. -/
def ScottishBookProblem5Claim : Prop :=
  ∃ a : ℕ → ℕ → ℝ, IsPermanent a ∧
    ∀ x : ℕ → ℝ, IsBounded x →
      ∀ S : ℝ, MatrixSums a x S ↔ AsymptoticallyConvergent x S

open Filter Finset
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

private def fraction (p : ℕ → Prop) (n : ℕ) : ℝ :=
  (Nat.count p n : ℝ) / n

private lemma fraction_nonneg (p : ℕ → Prop) (n : ℕ) : 0 ≤ fraction p n := by
  unfold fraction
  positivity

private lemma fraction_mono {p q : ℕ → Prop} {n : ℕ}
    (h : ∀ k < n, p k → q k) : fraction p n ≤ fraction q n := by
  unfold fraction
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.count_mono_left h) (by positivity)

private lemma fraction_le_add {p q r : ℕ → Prop} {n : ℕ}
    (h : ∀ k < n, p k → q k ∨ r k) : fraction p n ≤ fraction q n + fraction r n := by
  have hcount : Nat.count p n ≤ Nat.count q n + Nat.count r n := by
    simp only [Nat.count_eq_card_filter_range]
    refine (card_le_card (t := (range n).filter q ∪ (range n).filter r) ?_).trans
      (card_union_le _ _)
    intro k hk
    simp only [mem_filter, mem_range, mem_union] at hk ⊢
    exact (h k hk.1 hk.2).imp (And.intro hk.1) (And.intro hk.1)
  simp only [fraction, ← add_div, ← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

private lemma fraction_le_one (p : ℕ → Prop) (n : ℕ) : fraction p n ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [fraction]
  · exact (div_le_one (by exact_mod_cast hn)).2 (by exact_mod_cast Nat.count_le p)

private lemma fraction_compl {p : ℕ → Prop} :
    (fun n ↦ fraction (fun k ↦ ¬p k) n) =ᶠ[atTop] (fun n ↦ 1 - fraction p n) := by
  let : DecidablePred (fun k ↦ ¬p k) := fun k ↦ Classical.propDecidable (¬p k)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h : Nat.count p n + Nat.count (fun k ↦ ¬p k) n = n := by
    simpa only [Nat.count_eq_card_filter_range, card_range] using
      (card_filter_add_card_filter_not (s := range n) p)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [eq_sub_iff_add_eq, fraction, fraction, ← add_div, ← Nat.cast_add, add_comm, h, div_self hn']

private lemma tendsto_fraction_compl_iff {p : ℕ → Prop} :
    Tendsto (fraction (fun k ↦ ¬p k)) atTop (𝓝 0) ↔ Tendsto (fraction p) atTop (𝓝 1) := by
  constructor
  · intro h
    have h' := tendsto_const_nhds (x := (1 : ℝ)) |>.sub (h.congr' fraction_compl)
    simpa using h'
  · intro h
    have h' := tendsto_const_nhds (x := (1 : ℝ)) |>.sub h
    exact (by simpa using h' : Tendsto (fun n ↦ 1 - fraction p n) atTop (𝓝 0)).congr'
      fraction_compl.symm

private lemma count_range {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    Nat.count (fun k ↦ k ∈ Set.range s) (s n) = n := by
  classical
  have h : (range (s n)).filter (fun k ↦ k ∈ Set.range s) = (range n).image s := by
    ext k
    simp only [mem_filter, mem_range, Set.mem_range, mem_image]
    constructor
    · rintro ⟨hk, j, rfl⟩
      exact ⟨j, hs.lt_iff_lt.mp hk, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hs hj, j, rfl⟩
  rw [Nat.count_eq_card_filter_range, h, card_image_of_injective _ hs.injective, card_range]

private lemma fraction_range_iff {s : ℕ → ℕ} (hs : StrictMono s) :
    Tendsto (fraction (fun k ↦ k ∈ Set.range s)) atTop (𝓝 1) ↔ HasDensityOne s := by
  classical
  let c := Nat.count (fun k ↦ k ∈ Set.range s)
  have hc (n : ℕ) : c (s n) = n := count_range hs n
  have hshift : HasDensityOne s ↔ Tendsto (fun n ↦ (s n : ℝ) / n) atTop (𝓝 1) := by
    unfold HasDensityOne
    rw [and_iff_right hs]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat (f := fun n ↦ (s n : ℝ) / n) (l := 𝓝 1) 1)
  rw [hshift]
  constructor
  · intro h
    have h' : Tendsto (fun n : ℕ ↦ (n : ℝ) / s n) atTop (𝓝 1) := by
      convert h.comp hs.tendsto_atTop using 1
      funext n
      change (n : ℝ) / s n = (c (s n) : ℝ) / s n
      rw [hc]
    simpa only [Function.comp_def, inv_div, inv_one] using h'.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  · intro h
    have h' : Tendsto (fun n : ℕ ↦ (n : ℝ) / s n) atTop (𝓝 1) := by
      simpa only [Function.comp_def, inv_div, inv_one] using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hcTop : Tendsto c atTop atTop := tendsto_atTop.2 fun j ↦
      (eventually_ge_atTop (s j)).mono fun _ hn ↦ (hc j).symm.le.trans (Nat.count_monotone _ hn)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h'.comp hcTop) tendsto_const_nhds ?_
      (Eventually.of_forall (fraction_le_one _))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hle : n ≤ s (c n) := by
      by_contra! hlt
      have hcount := Nat.count_strict_mono (p := fun k ↦ k ∈ Set.range s) ⟨c n, rfl⟩ hlt
      change c (s (c n)) < c n at hcount
      rw [hc] at hcount
      exact (Nat.lt_irrefl _) hcount
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hle)

private def vanishingExceptions (x : ℕ → ℝ) (S : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fraction (fun k ↦ ε ≤ |x k - S|)) atTop (𝓝 0)

private lemma tendsto_fraction_of_bounded_count {p : ℕ → Prop} {B : ℕ}
    (hB : ∀ n, Nat.count p n ≤ B) : Tendsto (fraction p) atTop (𝓝 0) :=
  tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := (B : ℝ))
    (Eventually.of_forall fun _ ↦ by positivity)
    (Eventually.of_forall fun n ↦ by exact_mod_cast hB n) tendsto_natCast_atTop_atTop

private lemma count_le_of_no_mem_after {p : ℕ → Prop} {N : ℕ} (h : ∀ k ≥ N, ¬p k)
    (n : ℕ) : Nat.count p n ≤ N := by
  classical
  rw [Nat.count_eq_card_filter_range, ← card_range N]
  apply card_le_card
  simp only [mem_filter, mem_range, subset_iff]
  exact fun k hk ↦ lt_of_not_ge fun hN ↦ h k hN hk.2

private lemma vanishingExceptions_of_asymptoticallyConvergent {x : ℕ → ℝ} {S : ℝ}
    (h : AsymptoticallyConvergent x S) : vanishingExceptions x S := by
  classical
  obtain ⟨s, hs, hx⟩ := h
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx ε hε
  let q : ℕ → Prop := fun k ↦ ε ≤ |x k - S| ∧ k ∈ Set.range s
  have hq : Tendsto (fraction q) atTop (𝓝 0) := by
    apply tendsto_fraction_of_bounded_count (count_le_of_no_mem_after (N := s N) _)
    rintro k hk ⟨hbad, j, rfl⟩
    have hj := hN j (hs.1.le_iff_le.mp hk)
    rw [Real.dist_eq, Function.comp_apply] at hj
    exact (not_lt_of_ge hbad) hj
  have hcompl := tendsto_fraction_compl_iff.2 ((fraction_range_iff hs.1).2 hs)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hq.add hcompl) (Eventually.of_forall (fraction_nonneg _)) ?_
  exact Eventually.of_forall fun n ↦ fraction_le_add fun k _ hk ↦ by
    by_cases hks : k ∈ Set.range s
    · exact Or.inl ⟨hk, hks⟩
    · exact Or.inr hks

private lemma asymptoticallyConvergent_of_vanishingExceptions {x : ℕ → ℝ} {S : ℝ}
    (h : vanishingExceptions x S) : AsymptoticallyConvergent x S := by
  classical
  let t : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have ht : ∀ j, 0 < t j := fun j ↦ by dsimp [t]; positivity
  have htMono : Antitone t := by
    intro i j hij
    exact div_le_div_of_nonneg_left zero_le_one (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hij)
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have hlim := ((tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1).comp
      (tendsto_add_atTop_nat 1)
    change Tendsto (fun j : ℕ ↦ 1 / (↑(j + 1) : ℝ)) atTop (𝓝 0) at hlim
    simpa only [t, Nat.cast_add, Nat.cast_one] using hlim
  choose C hC using fun j ↦ eventually_atTop.1 ((h (t j) (ht j)).eventually_lt_const (ht j))
  -- Successive cutoffs enforce the count bound and tend to infinity.
  let N := fun j ↦ (range (j + 1)).sup C + j
  have hN (j : ℕ) : C j ≤ N j :=
    (le_sup (f := C) (mem_range.2 (Nat.lt_succ_self j))).trans (Nat.le_add_right _ _)
  have hNlarge (j : ℕ) : j ≤ N j := Nat.le_add_left _ _
  have hNmono : StrictMono N := by
    intro i j hij
    exact Nat.add_lt_add_of_le_of_lt (sup_mono (range_mono (Nat.succ_le_succ hij.le))) hij
  let p : ℕ → Prop := fun k ↦ ∀ j, N j ≤ k → |x k - S| < t j
  have hpcompl : Tendsto (fraction (fun k ↦ ¬p k)) atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (ht0.eventually_lt_const hε)
    refine ⟨N J, fun n hn ↦ ?_⟩
    let ex : ∃ j, n < N (j + 1) := ⟨n, (Nat.lt_succ_self _).trans_le (hNlarge _)⟩
    let j := Nat.find ex
    have hj : n < N (j + 1) := Nat.find_spec ex
    have hjJ : J ≤ j := by
      by_contra! hlt
      exact (not_lt_of_ge (hNmono.monotone (Nat.succ_le_iff.2 hlt) |>.trans hn)) hj
    have hjN : N j ≤ n := by
      cases hja : j with
      | zero => exact (hNmono.monotone (Nat.zero_le J)).trans hn
      | succ a =>
        have ha : a < j := hja ▸ Nat.lt_succ_self a
        exact Nat.le_of_not_gt (Nat.find_min ex ha)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (fraction_nonneg _ _)]
    refine (fraction_mono ?_).trans_lt ((hC j n ((hN j).trans hjN)).trans (hJ j hjJ))
    intro k hk hkp
    dsimp [p] at hkp
    push Not at hkp
    obtain ⟨i, hi, hbad⟩ := hkp
    have hij : i ≤ j := Nat.lt_succ_iff.1 (hNmono.lt_iff_lt.mp (hi.trans_lt (hk.trans hj)))
    exact (htMono hij).trans hbad
  have hp := tendsto_fraction_compl_iff.1 hpcompl
  have hpInf : (Set.ofPred p).Infinite := by
    intro hfin
    have hzero := tendsto_fraction_of_bounded_count (Nat.count_le_card hfin)
    exact one_ne_zero (tendsto_nhds_unique hp hzero)
  refine ⟨Nat.nth p, (fraction_range_iff (Nat.nth_strictMono hpInf)).1 ?_, ?_⟩
  · simpa only [Nat.range_nth_of_infinite hpInf, Set.mem_ofPred] using hp
  · refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (ht0.eventually_lt_const hε)
    refine ⟨N J, fun n hn ↦ ?_⟩
    have hmem := Nat.nth_mem_of_infinite hpInf n
    have hn' : n ≤ Nat.nth p n := (Nat.nth_strictMono hpInf).id_le n
    exact (by simpa only [Function.comp_apply, Real.dist_eq] using hmem J (hn.trans hn') :
      dist ((x ∘ Nat.nth p) n) S < t J).trans (hJ J le_rfl)

private lemma asymptoticallyConvergent_iff_vanishingExceptions (x : ℕ → ℝ) (S : ℝ) :
    AsymptoticallyConvergent x S ↔ vanishingExceptions x S :=
  ⟨vanishingExceptions_of_asymptoticallyConvergent, asymptoticallyConvergent_of_vanishingExceptions⟩

-- The block of size parameter `n` uses all large subsets of the first `n` indices.
private def largeSets (n : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦ n ≤ 2 * A.card

private lemma mem_largeSets {n : ℕ} {A : Finset ℕ} :
    A ∈ largeSets n ↔ A ⊆ range n ∧ n ≤ 2 * A.card := by
  rw [largeSets, mem_filter, mem_powerset]

private lemma range_mem_largeSets (n : ℕ) : range n ∈ largeSets n := by
  refine mem_largeSets.2 ⟨Subset.rfl, ?_⟩
  simp only [card_range]
  omega

private lemma card_pos_of_mem_largeSets {n : ℕ} (hn : 0 < n) {A : Finset ℕ}
    (hA : A ∈ largeSets n) : 0 < A.card := by
  have h := (mem_largeSets.1 hA).2
  omega

-- `start n` is the index of the first row in the block for the prefix of length `n + 1`.
private def start : ℕ → ℕ
  | 0 => 0
  | n + 1 => start n + (largeSets (n + 1)).card

private lemma start_strictMono : StrictMono start := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have h := card_pos.2 ⟨_, range_mem_largeSets (n + 1)⟩
  simp only [start]
  omega

private lemma exists_lt_start (i : ℕ) : ∃ n, i < start (n + 1) :=
  ⟨i, (Nat.lt_succ_self i).trans_le (start_strictMono.id_le (i + 1))⟩

private def block (i : ℕ) : ℕ := Nat.find (exists_lt_start i)

private lemma block_spec (i : ℕ) : i < start (block i + 1) :=
  Nat.find_spec (exists_lt_start i)

private lemma le_block {n i : ℕ} (h : start n ≤ i) : n ≤ block i := by
  by_contra! hn
  exact (not_lt_of_ge ((start_strictMono.monotone (Nat.succ_le_iff.2 hn)).trans h)) (block_spec i)

private lemma start_block_le (i : ℕ) : start (block i) ≤ i := by
  cases he : block i with
  | zero => simp [start]
  | succ n =>
    have h : n < block i := he ▸ Nat.lt_succ_self n
    exact Nat.le_of_not_gt (Nat.find_min (exists_lt_start i) h)

private lemma rowOffset_lt_card (i : ℕ) :
    i - start (block i) < (largeSets (block i + 1)).card := by
  have h := block_spec i
  simp only [start] at h
  have hl := start_block_le i
  omega

private def rowSet (i : ℕ) : Finset ℕ :=
  ((largeSets (block i + 1)).equivFin.symm ⟨i - start (block i), rowOffset_lt_card i⟩).val

private lemma rowSet_mem (i : ℕ) : rowSet i ∈ largeSets (block i + 1) :=
  ((largeSets (block i + 1)).equivFin.symm _).property

private lemma exists_row {n : ℕ} {A : Finset ℕ} (hA : A ∈ largeSets (n + 1)) :
    ∃ i, start n ≤ i ∧ rowSet i = A := by
  let j := (largeSets (n + 1)).equivFin ⟨A, hA⟩
  let i := start n + j.val
  have hlow : start n ≤ i := Nat.le_add_right _ _
  have hhigh : i < start (n + 1) := by
    simpa only [start, i, Nat.add_lt_add_iff_left] using j.isLt
  have hb : block i = n := le_antisymm (Nat.find_min' (exists_lt_start i) hhigh) (le_block hlow)
  refine ⟨i, hlow, ?_⟩
  have hfin : ∀ (b : ℕ) (e : b = n)
      (h : i - start b < (largeSets (b + 1)).card),
      ((largeSets (b + 1)).equivFin.symm ⟨i - start b, h⟩).val = A := by
    intro b e h
    subst b
    have hj : (⟨i - start n, h⟩ : Fin (largeSets (n + 1)).card) = j := by
      apply Fin.ext
      simp [i]
    rw [hj, Equiv.symm_apply_apply]
  exact hfin (block i) hb (rowOffset_lt_card i)

private def matrix (i k : ℕ) : ℝ :=
  if k ∈ rowSet i then (rowSet i).card⁻¹ else 0

private def mean (x : ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  (∑ k ∈ A, x k) / A.card

private lemma matrix_mul_zero_off (x : ℕ → ℝ) (i k : ℕ) (hk : k ∉ rowSet i) :
    matrix i k * x k = 0 := by simp [matrix, hk]

private lemma matrix_tsum_eq_mean (x : ℕ → ℝ) (i : ℕ) :
    (∑' k, matrix i k * x k) = mean x (rowSet i) := by
  rw [tsum_eq_sum (fun k hk ↦ matrix_mul_zero_off x i k hk), mean, div_eq_inv_mul,
    mul_sum]
  exact sum_congr rfl fun k hk ↦ by simp [matrix, hk]

private def uniformMeans (x : ℕ → ℝ) (S : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ A ∈ largeSets n, |mean x A - S| < ε

private lemma matrixSums_iff_uniformMeans (x : ℕ → ℝ) (S : ℝ) :
    MatrixSums matrix x S ↔ uniformMeans x S := by
  rw [MatrixSums, and_iff_right (fun i ↦ summable_of_ne_finset_zero (matrix_mul_zero_off x i)),
    show (fun i ↦ ∑' k, matrix i k * x k) = fun i ↦ mean x (rowSet i) from
      funext (matrix_tsum_eq_mean x), Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨I, hI⟩ := h ε hε
    refine eventually_atTop.2 ⟨I + 1, fun n hn A hA ↦ ?_⟩
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨i, hi, rfl⟩ := exists_row hA
      have hin : I ≤ i := (show I ≤ n by omega).trans ((start_strictMono.id_le n).trans hi)
      simpa only [Real.dist_eq] using hI i hin
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε hε)
    refine ⟨start N, fun i hi ↦ ?_⟩
    rw [Real.dist_eq]
    exact hN (block i + 1) ((le_block hi).trans (Nat.le_succ _)) _ (rowSet_mem i)

private lemma mean_sub_const (x : ℕ → ℝ) (S : ℝ) {A : Finset ℕ} (hA : 0 < A.card) :
    mean (fun k ↦ x k - S) A = mean x A - S := by
  have h : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  simp only [mean, sum_sub_distrib, sum_const, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ h]

private lemma uniformMeans_center (x : ℕ → ℝ) (S : ℝ) :
    uniformMeans x S ↔ uniformMeans (fun k ↦ x k - S) 0 := by
  unfold uniformMeans
  constructor <;> intro h ε hε <;>
    filter_upwards [eventually_ge_atTop 1, h ε hε] with n hn h A hA <;>
    simpa only [mean_sub_const x S (card_pos_of_mem_largeSets (by omega) hA), sub_zero] using h A hA

-- At most the exceptional terms contribute beyond the tolerance, and a large subset has
-- at least half the denominator of the whole prefix.
private lemma abs_mean_le {x : ℕ → ℝ} {M η : ℝ} (hM : 0 ≤ M) (hx : ∀ k, |x k| ≤ M)
    (hη : 0 ≤ η) {n : ℕ} (hn : 0 < n) {A : Finset ℕ} (hA : A ∈ largeSets n) :
    |mean x A| ≤ η + (2 * M) * fraction (fun k ↦ η ≤ |x k|) n := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast card_pos_of_mem_largeSets hn hA
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlarge : (n : ℝ) ≤ 2 * A.card := by exact_mod_cast (mem_largeSets.1 hA).2
  let p : ℕ → Prop := fun k ↦ η ≤ |x k|
  have hcount : (A.filter p).card ≤ Nat.count p n := by
    rw [Nat.count_eq_card_filter_range]
    exact card_le_card (filter_subset_filter _ (mem_largeSets.1 hA).1)
  have hcount' : ((A.filter p).card : ℝ) ≤ Nat.count p n := by exact_mod_cast hcount
  have hsum : (∑ k ∈ A, |x k|) ≤ A.card * η + (Nat.count p n : ℝ) * M := by
    calc
      _ ≤ ∑ k ∈ A, (η + if p k then M else 0) := by
        apply sum_le_sum
        intro k _
        by_cases hk : p k
        · rw [ite_eq_left hk]
          linarith [hx k]
        · rw [ite_eq_right hk, add_zero]
          exact le_of_lt (lt_of_not_ge hk)
      _ = A.card * η + ((A.filter p).card : ℝ) * M := by
        rw [sum_add_distrib, sum_ite]
        simp [nsmul_eq_mul]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right hcount' hM) _
  calc
    |mean x A| = |∑ k ∈ A, x k| / A.card := by rw [mean, abs_div, abs_of_pos hcard]
    _ ≤ (A.card * η + (Nat.count p n : ℝ) * M) / A.card :=
      div_le_div_of_nonneg_right ((abs_sum_le_sum_abs x A).trans hsum) hcard.le
    _ = η + (Nat.count p n : ℝ) * M / A.card := by
      rw [add_div, mul_div_cancel_left₀ _ hcard.ne']
    _ ≤ η + (2 * M) * fraction p n := by
      apply add_le_add_right
      calc
        _ ≤ (Nat.count p n : ℝ) * M / ((n : ℝ) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
        _ = (2 * M) * fraction p n := by simp only [fraction]; ring

private lemma uniformMeans_of_vanishingExceptions {x : ℕ → ℝ} {S : ℝ}
    (hx : IsBounded x) (h : vanishingExceptions x S) : uniformMeans x S := by
  obtain ⟨B, hB⟩ := hx
  let M := B + |S|
  have hM : 0 ≤ M := add_nonneg ((abs_nonneg (x 0)).trans (hB 0)) (abs_nonneg _)
  have hy (k : ℕ) : |x k - S| ≤ M := (abs_sub _ _).trans (add_le_add_left (hB k) _)
  rw [uniformMeans_center]
  intro ε hε
  have hlimit : Tendsto (fun n ↦ ε / 2 + (2 * M) *
      fraction (fun k ↦ ε / 2 ≤ |x k - S|) n) atTop (𝓝 (ε / 2)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := ε / 2)).add ((h _ (half_pos hε)).const_mul (2 * M))
  filter_upwards [eventually_ge_atTop 1, hlimit.eventually_lt_const (half_lt_self hε)] with n hn hl
  intro A hA
  rw [sub_zero]
  exact (abs_mean_le hM hy (half_pos hε).le (by omega) hA).trans_lt hl

-- If the positive exceptional set is large it is itself a row, an immediate contradiction.
-- Otherwise its complement is a row; subtract the complement's contribution from the whole sum.
private lemma positive_exception_bound {x : ℕ → ℝ} {n : ℕ} (hn : 0 < n) {ε δ : ℝ}
    (hδ₀ : 0 < δ) (hδε : δ < ε) (h : ∀ A ∈ largeSets n, |mean x A| < δ) :
    ε * fraction (fun k ↦ ε ≤ x k) n ≤ 2 * δ := by
  let P := (range n).filter fun k ↦ ε ≤ x k
  have hPsub : P ⊆ range n := filter_subset _ _
  have hPsum : (P.card : ℝ) * ε ≤ ∑ k ∈ P, x k := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun k hk ↦ (mem_filter.1 hk).2
  have hPsmall : 2 * P.card < n := by
    by_contra! hlarge
    have hP : P ∈ largeSets n := mem_largeSets.2 ⟨hPsub, hlarge⟩
    have hp : (0 : ℝ) < P.card := by exact_mod_cast card_pos_of_mem_largeSets hn hP
    have hmean := (le_abs_self _).trans_lt (h P hP)
    rw [mean, div_lt_iff₀ hp] at hmean
    exact (not_lt_of_ge hPsum) (hmean.trans (mul_comm δ _ ▸ mul_lt_mul_of_pos_left hδε hp))
  let Q := range n \ P
  have hQcard : Q.card + P.card = n := by
    simpa only [card_range] using card_sdiff_add_card_eq_card hPsub
  have hQ : Q ∈ largeSets n := mem_largeSets.2 ⟨sdiff_subset, by omega⟩
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast card_pos_of_mem_largeSets hn hQ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hfull := (le_abs_self _).trans_lt (h _ (range_mem_largeSets n))
  rw [mean, card_range, div_lt_iff₀ hnr] at hfull
  have hcomp := (neg_lt_of_abs_lt (h _ hQ))
  rw [mean, lt_div_iff₀ hq] at hcomp
  have hsplit : (∑ k ∈ Q, x k) + ∑ k ∈ P, x k = ∑ k ∈ range n, x k := sum_sdiff hPsub
  have hqr : (Q.card : ℝ) ≤ n := by exact_mod_cast (show Q.card ≤ n by omega)
  have hcount : Nat.count (fun k ↦ ε ≤ x k) n = P.card := Nat.count_eq_card_filter_range _ _
  rw [fraction, hcount, ← mul_div_assoc, div_le_iff₀ hnr]
  nlinarith [mul_le_mul_of_nonneg_left hqr hδ₀.le]

private lemma vanishingExceptions_of_uniformMeans {x : ℕ → ℝ} {S : ℝ}
    (h : uniformMeans x S) : vanishingExceptions x S := by
  rw [uniformMeans_center] at h
  let y : ℕ → ℝ := fun k ↦ x k - S
  intro ε hε
  change Tendsto (fraction fun k ↦ ε ≤ |y k|) atTop (𝓝 0)
  refine Metric.tendsto_atTop.2 fun d hd ↦ ?_
  let δ := min (ε / 2) (ε * d / 8)
  have hδ₀ : 0 < δ := lt_min (half_pos hε) (by positivity)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδd : δ ≤ ε * d / 8 := min_le_right _ _
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h δ hδ₀)
  refine ⟨max N 1, fun n hn ↦ ?_⟩
  have hnr : 0 < n := (le_max_right N 1).trans hn
  have hA : ∀ A ∈ largeSets n, |mean y A| < δ := by
    simpa only [sub_zero] using hN n ((le_max_left N 1).trans hn)
  have hneg : ∀ A ∈ largeSets n, |mean (fun k ↦ -y k) A| < δ := by
    intro A ha
    simpa only [mean, sum_neg_distrib, neg_div, abs_neg] using hA A ha
  have hpos := positive_exception_bound hnr hδ₀ hδε hA
  have hneg' := positive_exception_bound hnr hδ₀ hδε hneg
  have hfraction : fraction (fun k ↦ ε ≤ |y k|) n ≤
      fraction (fun k ↦ ε ≤ y k) n + fraction (fun k ↦ ε ≤ -y k) n := by
    apply fraction_le_add
    intro k _ hk
    by_cases hy : 0 ≤ y k
    · exact Or.inl (by simpa only [abs_of_nonneg hy] using hk)
    · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hy)] using hk)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (fraction_nonneg _ _)]
  have hbound := mul_le_mul_of_nonneg_left hfraction hε.le
  by_contra! hbad
  have hbad' := mul_le_mul_of_nonneg_left hbad hε.le
  nlinarith [mul_pos hε hd]

private lemma isBounded_of_tendsto {x : ℕ → ℝ} {S : ℝ} (h : Tendsto x atTop (𝓝 S)) :
    IsBounded x := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (Metric.isBounded_range_of_tendsto x h)
  refine ⟨C + |x 0|, fun n ↦ ?_⟩
  have hdist := hC (Set.mem_range_self n) (Set.mem_range_self 0)
  rw [Real.dist_eq] at hdist
  have habs := abs_add_le (x n - x 0) (x 0)
  rw [sub_add_cancel] at habs
  exact habs.trans (add_le_add_left hdist _)

/-- A single permanent matrix sums a bounded real sequence to `S` if and only if it has a
strictly increasing subsequence of density one converging to `S`. The matrix is built from
uniform averages over the subsets containing at least half of a nonempty initial interval. -/
theorem scottishBookProblem5Claim : ScottishBookProblem5Claim := by
  have h (x : ℕ → ℝ) (hx : IsBounded x) (S : ℝ) :
      MatrixSums matrix x S ↔ AsymptoticallyConvergent x S :=
    (matrixSums_iff_uniformMeans x S).trans <|
      (Iff.intro vanishingExceptions_of_uniformMeans (uniformMeans_of_vanishingExceptions hx)).trans
        (asymptoticallyConvergent_iff_vanishingExceptions x S).symm
  refine ⟨matrix, ?_, h⟩
  intro x S hx
  apply (h x (isBounded_of_tendsto hx) S).2
  refine ⟨id, ⟨strictMono_id, ?_⟩, hx⟩
  have hconst (n : ℕ) : ((id (n + 1) : ℕ) : ℝ) / ((n : ℝ) + 1) = 1 := by
    rw [id_eq, Nat.cast_add, Nat.cast_one, div_self (by positivity)]
  simpa only [hconst] using (tendsto_const_nhds (x := (1 : ℝ)) :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))

end

end MathlibExt.Analysis.Series.ScottishBook5BoundedWanted
