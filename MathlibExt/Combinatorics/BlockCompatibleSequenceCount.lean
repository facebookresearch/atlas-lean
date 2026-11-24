/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Sort
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Interval.Finset.Fin

/-!
# Many block-compatible sequences

`conjecture_holds` gives an exponential lower bound for the number of block-size sequences
of pairwise balanced designs. Truncating lines of each slope to a different size lets us
recover the number of chosen lines of that slope from the sequence.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted

/-- **Pairwise balanced design.** For a natural number $n$, a finite list of blocks
$B_1, \ldots, B_m \subseteq \{0, \ldots, n - 1\}$ is a pairwise balanced design on these $n$ points
when the blocks are pairwise distinct, every block has at least two points, and every two distinct
points lie in exactly one common block. -/
def IsPBD (n : ℕ) (blocks : List (Finset (Fin n))) : Prop :=
  blocks.Nodup ∧
  (∀ B ∈ blocks, 2 ≤ B.card) ∧
    ∀ x y : Fin n, x ≠ y →
      ∃! B : Finset (Fin n), B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- **Block-compatible sequences.** For a natural number $n$, a finite sequence
$(x_1, \ldots, x_m)$ of natural numbers is block-compatible for $n$ when
$x_1 \ge x_2 \ge \cdots \ge x_m$, every $x_k$ satisfies $2 \le x_k \le n$, and there is a pairwise
balanced design on the point set $\{0, \ldots, n - 1\}$ whose blocks, listed in order as
$B_1, \ldots, B_m$, have sizes $|B_k| = x_k$ for every $k$. -/
def BlockCompatible (n : ℕ) (l : List ℕ) : Prop :=
  List.Pairwise (· ≥ ·) l ∧ (∀ x ∈ l, 2 ≤ x ∧ x ≤ n) ∧
    ∃ blocks : List (Finset (Fin n)),
      blocks.map Finset.card = l ∧ IsPBD n blocks

/-- **Many block-compatible sequences.** The statement that there are a real number $c > 0$ and a
natural number $N$ such that for every $n \ge N$ there is a finite set of at least
$\exp(c \sqrt{n} \log n)$ distinct finite sequences of natural numbers, each of which is
block-compatible for $n$. Here $\log$ is the natural logarithm.

Source: OWR-14299518-002, question (2). -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset (List ℕ), (∀ l ∈ S, BlockCompatible n l) ∧
      Real.exp (c * Real.sqrt n * Real.log n) ≤ (S.card : ℝ)

/-- Order the blocks by size and read off the multiplicities from the underlying finite set. -/
private theorem sizes_of_design {n : ℕ} (D : Finset (Finset (Fin n)))
    (hsize : ∀ B ∈ D, 2 ≤ B.card)
    (hpair : ∀ x y : Fin n, x ≠ y → ∃! B, B ∈ D ∧ x ∈ B ∧ y ∈ B) :
    ∃ l, BlockCompatible n l ∧ ∀ k, l.count k = (D.filter (k = ·.card)).card := by
  classical
  let cmp (B C : Finset (Fin n)) := decide (C.card ≤ B.card)
  let blocks := D.toList.mergeSort cmp
  have hperm : blocks.Perm D.toList := List.mergeSort_perm _ _
  have hmem {B} : B ∈ blocks ↔ B ∈ D := hperm.mem_iff.trans Finset.mem_toList
  refine ⟨blocks.map Finset.card, ⟨List.pairwise_map.mpr ?_, ?_, blocks, rfl,
    hperm.nodup_iff.mpr D.nodup_toList, fun B hB ↦ hsize B (hmem.mp hB), ?_⟩, ?_⟩
  · simpa [cmp, blocks] using List.pairwise_mergeSort (le := cmp)
      (by simp [cmp]; omega) (by simp [cmp]; omega) D.toList
  · intro k hk
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hk
    exact ⟨hsize B (hmem.mp hB), by simpa using B.card_le_univ⟩
  · simpa only [hmem] using hpair
  · intro k
    rw [(hperm.map Finset.card).count_eq, ← Multiset.coe_count, ← Multiset.map_coe,
      Finset.coe_toList, Multiset.count_map]
    rfl

/-- Fill in the uncovered pairs of a packing. This preserves every multiplicity above two. -/
private theorem complete_packing {n : ℕ} (L : Finset (Finset (Fin n)))
    (hsize : ∀ B ∈ L, 2 ≤ B.card)
    (hpack : ∀ x y : Fin n, x ≠ y → ∀ B ∈ L, ∀ C ∈ L,
      {x, y} ⊆ B → {x, y} ⊆ C → B = C) :
    ∃ l, BlockCompatible n l ∧ ∀ k, 2 < k → l.count k = (L.filter (k = ·.card)).card := by
  classical
  let pairs := Finset.univ.filter fun B : Finset (Fin n) =>
    B.card = 2 ∧ ∀ C ∈ L, ¬ B ⊆ C
  have mem_pairs {B} : B ∈ pairs ↔ B.card = 2 ∧ ∀ C ∈ L, ¬ B ⊆ C := by simp [pairs]
  obtain ⟨l, hl, hcount⟩ := sizes_of_design (L ∪ pairs) (by
    intro B hB
    rcases Finset.mem_union.mp hB with h | h
    · exact hsize B h
    · exact (mem_pairs.mp h).1.ge) (by
    intro x y hxy
    have pair_sub {B : Finset (Fin n)} (hx : x ∈ B) (hy : y ∈ B) : {x, y} ⊆ B :=
      Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    have eq_pair {B} (hB : B ∈ pairs) (hx : x ∈ B) (hy : y ∈ B) : {x, y} = B :=
      Finset.eq_of_subset_of_card_le (pair_sub hx hy)
        (by rw [(mem_pairs.mp hB).1, Finset.card_pair hxy])
    by_cases covered : ∃ C ∈ L, {x, y} ⊆ C
    · obtain ⟨C, hC, hsub⟩ := covered
      refine ⟨C, ⟨Finset.mem_union_left _ hC, hsub (by simp), hsub (by simp)⟩, ?_⟩
      rintro B ⟨hB, hx, hy⟩
      rcases Finset.mem_union.mp hB with hb | hb
      · exact hpack x y hxy B hb C hC (pair_sub hx hy) hsub
      · exact False.elim ((mem_pairs.mp hb).2 C hC (eq_pair hb hx hy ▸ hsub))
    · have hp : {x, y} ∈ pairs :=
        mem_pairs.mpr ⟨Finset.card_pair hxy, fun C hC hs ↦ covered ⟨C, hC, hs⟩⟩
      refine ⟨{x, y}, ⟨Finset.mem_union_right _ hp, by simp, by simp⟩, ?_⟩
      rintro B ⟨hB, hx, hy⟩
      rcases Finset.mem_union.mp hB with hb | hb
      · exact False.elim (covered ⟨B, hb, pair_sub hx hy⟩)
      · exact (eq_pair hb hx hy).symm)
  refine ⟨l, hl, fun k hk ↦ (hcount k).trans (congrArg Finset.card ?_)⟩
  apply Finset.ext
  intro B
  simp only [Finset.mem_filter, Finset.mem_union, mem_pairs]
  grind

section Lines

variable {p n : ℕ} [Fact p.Prime]

/-- Include an initial segment of residues in the prime field. -/
private def coord {m : ℕ} (h : m ≤ p) : Fin m ↪ ZMod p :=
  (Fin.castLEEmb h).trans (ZMod.finEquiv p).toEquiv.toEmbedding

/-- Parametrize the nonvertical affine line of slope a and intercept b. -/
private def line (a b : ZMod p) : ZMod p ↪ ZMod p × ZMod p :=
  ⟨fun x ↦ (x, a * x + b), fun _ _ h ↦ congrArg Prod.fst h⟩

private abbrev LineIndex (p : ℕ) := Fin (p - 2) × Fin p

private def slope (i : Fin (p - 2)) : ZMod p := coord (Nat.sub_le p 2) i

/-- Retain exactly i + 3 points on every line of slope i. -/
private def segment (e : ZMod p × ZMod p ↪ Fin n) (u : LineIndex p) : Finset (Fin n) :=
  let xs := coord (m := u.1.val + 3) (p := p) (by have := u.1.isLt; omega)
  Finset.univ.map ((xs.trans (line (slope u.1) (coord le_rfl u.2))).trans e)

private theorem segment_card (e : ZMod p × ZMod p ↪ Fin n) (u : LineIndex p) :
    (segment e u).card = u.1.val + 3 := by simp [segment]

private theorem mem_segment_line {e : ZMod p × ZMod p ↪ Fin n} {u : LineIndex p} {z : Fin n}
    (hz : z ∈ segment e u) :
    ∃ x : ZMod p, e (x, slope u.1 * x + coord le_rfl u.2) = z := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hz
  exact ⟨_, rfl⟩

/-- Two distinct common points recover both the slope and the intercept. -/
private theorem index_eq_of_common_pair {e : ZMod p × ZMod p ↪ Fin n} {u v : LineIndex p}
    {x y : Fin n} (hxy : x ≠ y) (hxu : x ∈ segment e u) (hyu : y ∈ segment e u)
    (hxv : x ∈ segment e v) (hyv : y ∈ segment e v) : u = v := by
  obtain ⟨s, rfl⟩ := mem_segment_line hxu
  obtain ⟨t, rfl⟩ := mem_segment_line hyu
  obtain ⟨s', hs⟩ := mem_segment_line hxv
  obtain ⟨t', ht⟩ := mem_segment_line hyv
  obtain ⟨rfl, hs⟩ := Prod.mk.inj (e.injective hs)
  obtain ⟨rfl, ht⟩ := Prod.mk.inj (e.injective ht)
  have hst : s' ≠ t' := by rintro rfl; exact hxy rfl
  have hzero : (slope v.1 - slope u.1) * (s' - t') = 0 := by
    linear_combination hs - ht
  have ha := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hst))
  refine Prod.ext ((coord (Nat.sub_le p 2)).injective ha.symm) ((coord le_rfl).injective ?_)
  rwa [ha, add_right_inj, eq_comm] at hs

private def segmentEmbedding (e : ZMod p × ZMod p ↪ Fin n) :
    LineIndex p ↪ Finset (Fin n) where
  toFun := segment e
  inj' := by
    intro u v h
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
      (show 1 < (segment e u).card by rw [segment_card]; omega)
    exact index_eq_of_common_pair hxy hx hy (h ▸ hx) (h ▸ hy)

/-- Choose an initial segment of intercepts independently for every slope. -/
private theorem realize_counts (e : ZMod p × ZMod p ↪ Fin n) (f : Fin (p - 2) → Fin p) :
    ∃ l, BlockCompatible n l ∧ ∀ i, l.count (i.val + 3) = (f i).val := by
  classical
  let T := Finset.univ.filter fun u : LineIndex p => u.2 < f u.1
  let L := T.map (segmentEmbedding e)
  obtain ⟨l, hl, hcount⟩ := complete_packing L (by
    intro B hB
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hB
    change 2 ≤ (segment e u).card
    rw [segment_card]
    omega) (by
    intro x y hxy B hB C hC hsubB hsubC
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hC
    exact congrArg (segment e) (index_eq_of_common_pair hxy
      (hsubB (by simp)) (hsubB (by simp)) (hsubC (by simp)) (hsubC (by simp))))
  refine ⟨l, hl, fun i ↦ (hcount (i.val + 3) (by omega)).trans ?_⟩
  simp only [L, Finset.filter_map, Finset.card_map]
  have hfiber : T.filter (fun u => i.val + 3 = ((segmentEmbedding e) u).card) =
      {i} ×ˢ Finset.Iio (f i) := by
    ext ⟨j, b⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_Iio]
    change (b < f j ∧ i.val + 3 = (segment e (j, b)).card) ↔ j = i ∧ b < f i
    rw [segment_card]
    simp only [Nat.add_right_cancel_iff, Fin.val_inj]
    grind
  simp [hfiber]

end Lines

/-- The multiplicities distinguish all p^(p-2) choices of intercept counts. -/
private theorem many_at_prime {p n : ℕ} [Fact p.Prime] (hfit : p * p ≤ n) :
    ∃ S : Finset (List ℕ), (∀ l ∈ S, BlockCompatible n l) ∧ S.card = p ^ (p - 2) := by
  classical
  obtain ⟨e⟩ : Nonempty (ZMod p × ZMod p ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa [ZMod.card] using hfit)
  choose seq hcompat hcount using realize_counts e
  have hinj : Function.Injective seq := by
    intro f g h
    funext i
    apply Fin.ext
    rw [← hcount f i, h, hcount g i]
  refine ⟨Finset.univ.map ⟨seq, hinj⟩, ?_, ?_⟩
  · intro l hl
    obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp hl
    exact hcompat f
  · simp

/-- Bertrand's postulate gives a prime whose square fits and whose double exceeds √n. -/
private theorem fitting_prime {n : ℕ} (hn : 64 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 4 ≤ p ∧ p * p ≤ n ∧ n ≤ (2 * p) ^ 2 := by
  have hs : 8 ≤ n.sqrt := Nat.le_sqrt.mpr hn
  obtain ⟨p, hp, hlow, hhigh⟩ := Nat.exists_prime_lt_and_le_two_mul (n.sqrt / 2) (by omega)
  refine ⟨p, hp, by omega, ?_, ?_⟩
  · exact (Nat.mul_self_le_mul_self (show p ≤ n.sqrt by omega)).trans (Nat.sqrt_le n)
  · exact (Nat.lt_succ_sqrt' n).le.trans (Nat.pow_le_pow_left (by omega) _)

/-- Convert the finite count to a uniform real exponential bound. -/
private theorem exp_le_count {p n : ℕ} (hp : 4 ≤ p) (hn : 0 < n) (hscale : n ≤ (2 * p) ^ 2) :
    Real.exp (1 / 16 * Real.sqrt n * Real.log n) ≤ ((p ^ (p - 2) : ℕ) : ℝ) := by
  have hp' : 4 ≤ (p : ℝ) := by exact_mod_cast hp
  have hscale' : (n : ℝ) ≤ (2 * (p : ℝ)) ^ 2 := by exact_mod_cast hscale
  have hroot : Real.sqrt n ≤ 4 * ((p - 2 : ℕ) : ℝ) := by
    refine (Real.sqrt_le_iff.mpr ⟨by positivity, hscale'⟩).trans ?_
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    push_cast
    linarith
  have hpow : (n : ℝ) ≤ (p : ℝ) ^ 4 := by
    calc
      (n : ℝ) ≤ (2 * (p : ℝ)) ^ 2 := hscale'
      _ ≤ ((p : ℝ) ^ 2) ^ 2 := by gcongr; nlinarith
      _ = (p : ℝ) ^ 4 := by ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n) hpow
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hlog₀ : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  calc
    Real.exp (1 / 16 * Real.sqrt n * Real.log n) ≤
        Real.exp (1 / 16 * (4 * ((p - 2 : ℕ) : ℝ)) * (4 * Real.log p)) := by gcongr
    _ = Real.exp (((p - 2 : ℕ) : ℝ) * Real.log p) := by congr 1; ring
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by positivity)]; push_cast; rfl

/--
**Many block-compatible sequences (Erdős Problem 732).** There are a real number $c > 0$ and a
natural number $N$ such that for every $n \ge N$ there is a finite set of at least
$\exp(c \sqrt{n} \log n)$ distinct finite sequences of natural numbers, each of which is
block-compatible for $n$. Here $\log$ is the natural logarithm.

Alon proved the stronger bound that at least $2^{(1/2 + o(1)) \sqrt{n} \log n}$ sequences are
block-compatible for $n$ (Oberwolfach Report 42/2025, Theorem 4; also Theorem 2.3 of his note
'Blocking partial designs and block-compatible sequences').

Source: N. Alon, On designs and
partial designs, extended abstract in Oberwolfach Report 42/2025 (Combinatorics, Probability and
Computing), pp. 2249-2250, Theorem 4, https://doi.org/10.4171/owr/2025/42; N. Alon, Blocking
partial designs and block-compatible sequences, note, Theorem 2.3,
https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf; T. F. Bloom, Erdős Problem #732,
erdosproblems.com (status PROVED), https://www.erdosproblems.com/732. Moved from
`OpenConjectures/Combinatorics/BlockCompatibleSequenceCount`.
-/
public theorem conjecture_holds : conjecture := by
  refine ⟨1 / 16, by norm_num, 64, ?_⟩
  intro n hn
  obtain ⟨p, hp, hlarge, hfit, hscale⟩ := fitting_prime hn
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hcard⟩ := many_at_prime hfit
  exact ⟨S, hS, hcard ▸ exp_le_count hlarge (by omega) hscale⟩

end MathlibExt.Combinatorics.BlockCompatibleSequenceCountWanted
