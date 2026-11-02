/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Rayleigh

/-!
Source provenance for concept `jis_sem_329070e9cea40082f4048ff4`
("almost Beatty partition").

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL22/Hildebrand/hilde2.tex`
File SHA-256: `293500514025c31a4932039c6c352c549b00ddaa4700be115c59174661a03818`
Source blocks: lines 350-425 with
SHA-256 `2e8d7075e9b98c40d79c1f9222b5d7067df1d4d2ee1d33c2fa7174096c71806c`,
and lines 441-464 with
SHA-256 `687ff2ae1a163c823a339681502fbd6703a10be1922252fba6893f74741a5957`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Beatty term.** For a positive integer $n$ and a real number $\alpha$, the Beatty term
$b_n(\alpha)$ is the natural number $\max(\lfloor n/\alpha \rfloor, 0)$: the $n$-th term
$\lfloor n \cdot (1/\alpha) \rfloor$ of the Beatty sequence of slope $1/\alpha$, truncated at
$0$. Division by zero is read as $0$, so $b_n(0) = 0$.

Source: frozen source statements `jis_3a6643107cb0f496a9559012`,
`jis_74d8835ba8df562bb5834fef`, `jis_8d72c1833a8a5da5a1a319c0`,
`jis_9c431d0d610f8a075ea0cb13`, `jis_aac0e146b36de598ccb32fd6`,
`jis_c2877cfd93d3493ab5d68e84`, and `jis_ec4d65fd2ab77c1aec768d61`. -/
public noncomputable def beattyTerm (n : { n : ℕ // 0 < n }) (α : ℝ) : ℕ :=
  (beattySeq (1 / α) (n.val : ℤ)).toNat

/-- **Beatty term as a natural-number floor.** For every positive integer $n$ and every real
number $\alpha$, the Beatty term $b_n(\alpha)$ equals the natural-number floor of $n/\alpha$:
the largest natural number $m$ with $m \le n/\alpha$ when $n/\alpha \ge 0$, and $0$ when
$n/\alpha < 0$. Division by zero is read as $0$, so $n/0 = 0$. -/
public theorem beattyTerm_eq_floor (n : { n : ℕ // 0 < n }) (α : ℝ) :
    beattyTerm n α = Nat.floor ((n.val : ℝ) / α) := by
  simp [beattyTerm, beattySeq, div_eq_mul_inv, Int.floor_toNat]

/-- **Almost Beatty sequence.** Let $\alpha$ be a real number. A sequence $(s_n)_{n \ge 1}$ of
natural numbers indexed by the positive integers is an almost Beatty sequence for $\alpha$ when
$0 < \alpha < 1$, the sequence is strictly increasing, $s_n > 0$ for every $n \ge 1$, and
there is a natural number $B$ with $|s_n - b_n(\alpha)| \le B$ for every $n \ge 1$, where
$b_n(\alpha)$ is the Beatty term, equal to $\lfloor n/\alpha \rfloor$ once $\alpha > 0$.

Source: concept `jis_sem_329070e9cea40082f4048ff4`; frozen source statements
`jis_3a6643107cb0f496a9559012`, `jis_74d8835ba8df562bb5834fef`,
`jis_8d72c1833a8a5da5a1a319c0`, `jis_9c431d0d610f8a075ea0cb13`,
`jis_aac0e146b36de598ccb32fd6`, `jis_c2877cfd93d3493ab5d68e84`, and
`jis_ec4d65fd2ab77c1aec768d61`. -/
public def IsAlmostBeattySequence (s : { n : ℕ // 0 < n } → ℕ) (α : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ StrictMono s ∧
    (∀ n, 0 < s n) ∧
      ∃ B : ℕ, ∀ n, ((s n : ℤ) - (beattyTerm n α : ℤ)).natAbs ≤ B

/-- **Three-way partition of the positive integers.** Three sequences $s_1, s_2, s_3$ of natural
numbers indexed by the positive integers partition the positive integers when their ranges are
pairwise disjoint, that is, $s_i(m) \ne s_j(n)$ for all $i \ne j$ and all positive integers $m$
and $n$, and the union of their ranges is exactly the set of positive integers: a natural
number $k$ is a value of some $s_i$ if and only if $k > 0$.

Source: concept `jis_sem_329070e9cea40082f4048ff4`; frozen source statements
`jis_3a6643107cb0f496a9559012`, `jis_74d8835ba8df562bb5834fef`,
`jis_8d72c1833a8a5da5a1a319c0`, `jis_9c431d0d610f8a075ea0cb13`,
`jis_aac0e146b36de598ccb32fd6`, `jis_c2877cfd93d3493ab5d68e84`, and
`jis_ec4d65fd2ab77c1aec768d61`. -/
public def IsPositiveNatThreeWayPartition (s1 s2 s3 : { n : ℕ // 0 < n } → ℕ) : Prop :=
  (∀ m n, s1 m ≠ s2 n) ∧
    (∀ m n, s1 m ≠ s3 n) ∧
      (∀ m n, s2 m ≠ s3 n) ∧
        ∀ k : ℕ, (∃ n, s1 n = k ∨ s2 n = k ∨ s3 n = k) ↔ 0 < k

/-- **Almost Beatty partition.** Given real numbers $\alpha_1, \alpha_2, \alpha_3$, three
sequences $s_1, s_2, s_3$ of natural numbers indexed by the positive integers form an almost
Beatty partition when, for each $i$, the sequence $s_i$ is an almost Beatty sequence for
$\alpha_i$, and the three sequences form a three-way partition of the positive integers: their
ranges are pairwise disjoint and their union is the set of positive integers.

Source: concept `jis_sem_329070e9cea40082f4048ff4`; frozen source statements
`jis_3a6643107cb0f496a9559012`, `jis_74d8835ba8df562bb5834fef`,
`jis_8d72c1833a8a5da5a1a319c0`, `jis_9c431d0d610f8a075ea0cb13`,
`jis_aac0e146b36de598ccb32fd6`, `jis_c2877cfd93d3493ab5d68e84`, and
`jis_ec4d65fd2ab77c1aec768d61`. -/
public def IsAlmostBeattyPartition (s1 s2 s3 : { n : ℕ // 0 < n } → ℕ) (α1 α2 α3 : ℝ) : Prop :=
  IsAlmostBeattySequence s1 α1 ∧
    IsAlmostBeattySequence s2 α2 ∧
      IsAlmostBeattySequence s3 α3 ∧ IsPositiveNatThreeWayPartition s1 s2 s3

/-- **Beatty sequences are almost Beatty.** For every real number $\alpha$ with
$0 < \alpha < 1$, the sequence of Beatty terms $n \mapsto b_n(\alpha) = \lfloor n/\alpha \rfloor$,
indexed by the positive integers $n$, is an almost Beatty sequence for $\alpha$.

The proof takes the bound $B = 0$ and derives strict monotonicity and positivity from
$0 < \alpha < 1$.

Source: concept `jis_sem_329070e9cea40082f4048ff4`; frozen source statements
`jis_3a6643107cb0f496a9559012`, `jis_74d8835ba8df562bb5834fef`,
`jis_8d72c1833a8a5da5a1a319c0`, `jis_9c431d0d610f8a075ea0cb13`,
`jis_aac0e146b36de598ccb32fd6`, `jis_c2877cfd93d3493ab5d68e84`, and
`jis_ec4d65fd2ab77c1aec768d61`. -/
public theorem beattyTerm_isAlmostBeattySequence (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    IsAlmostBeattySequence (fun n => beattyTerm n α) α := by
  have h1div : (1 : ℝ) < 1 / α := by
    have h10 : (1 : ℝ) * α < 1 := by
      simpa using hα1
    exact (lt_div_iff₀ hα0).mpr h10
  have hmono : StrictMono (fun n : { n : ℕ // 0 < n } => beattyTerm n α) := by
    intro m n hmn
    have hmn' : m.val < n.val := hmn
    have hmn1 : m.val + 1 ≤ n.val := by omega
    have hcast1 : (m.val : ℝ) + 1 ≤ (n.val : ℝ) := by
      have h : ((m.val + 1 : ℕ) : ℝ) ≤ ((n.val : ℕ) : ℝ) := Nat.cast_le.mpr hmn1
      rw [Nat.cast_add, Nat.cast_one] at h
      exact h
    have hA : ((m.val : ℝ) + 1) / α ≤ (n.val : ℝ) / α :=
      (div_le_div_iff_of_pos_right hα0).mpr hcast1
    rw [add_div] at hA
    have hB : (((m.val : ℝ) / α + 1 : ℝ)) < (((m.val : ℝ) / α + 1 / α : ℝ)) :=
      add_lt_add_right h1div (((m.val : ℝ) / α : ℝ))
    have key : (m.val : ℝ) / α + 1 < (n.val : ℝ) / α :=
      lt_of_lt_of_le hB hA
    have hx0 : (0 : ℝ) ≤ (m.val : ℝ) / α :=
      le_of_lt (div_pos (Nat.cast_pos.mpr m.2) hα0)
    have hxa : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) ≤ (m.val : ℝ) / α :=
      Nat.floor_le hx0
    have h1 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) + 1 ≤ (m.val : ℝ) / α + 1 :=
      add_le_add_left hxa 1
    have h3 : (n.val : ℝ) / α < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have h4 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) + 1 <
        ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      lt_trans (lt_of_le_of_lt h1 key) h3
    have h5 : ((Nat.floor ((m.val : ℝ) / α) : ℕ) : ℝ) <
        ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) :=
      (add_lt_add_iff_right (1 : ℝ)).mp h4
    change beattyTerm m α < beattyTerm n α
    rw [beattyTerm_eq_floor, beattyTerm_eq_floor]
    exact Nat.cast_lt.mp h5
  have hpos : ∀ n : { n : ℕ // 0 < n }, 0 < beattyTerm n α := by
    intro n
    have hn1 : 1 ≤ n.val := n.2
    have hcastn : (1 : ℝ) ≤ (n.val : ℝ) := by
      have h : ((1 : ℕ) : ℝ) ≤ ((n.val : ℕ) : ℝ) := Nat.cast_le.mpr hn1
      rw [Nat.cast_one] at h
      exact h
    have hle : (1 : ℝ) ≤ (n.val : ℝ) / α := by
      rw [le_div_iff₀ hα0, one_mul]
      exact le_trans (le_of_lt hα1) hcastn
    have h2 : (1 : ℝ) < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 :=
      lt_of_le_of_lt hle (Nat.lt_floor_add_one _)
    have h3 : (0 : ℝ) + 1 < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) + 1 := by
      rw [zero_add]
      exact h2
    have h4 : (0 : ℝ) < ((Nat.floor ((n.val : ℝ) / α) : ℕ) : ℝ) :=
      (add_lt_add_iff_right (1 : ℝ)).mp h3
    rw [beattyTerm_eq_floor]
    exact Nat.cast_pos.mp h4
  refine ⟨hα0, hα1, hmono, hpos, 0, fun n => by simp⟩

end

end MetaMathlibExt
