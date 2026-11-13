/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Real.Basic

namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-!
# Erdős–Szekeres monotone subsequence theorem

Every injective real sequence of length `(r - 1) * (s - 1) + 1` contains an
increasing subsequence of length `r` or a decreasing subsequence of length `s`.

Source: P. Erdős and G. Szekeres, “A combinatorial problem in geometry,”
_Compositio Mathematica_ 2 (1935), 463–470; the two-parameter
monotone-subsequence bound is proved on p. 468.
NUMDAM record: https://www.numdam.org/item/CM_1935__2__463_0/.
-/

/-- **A positive natural number exceeds its predecessor.** For every natural number $k > 0$,
$k - 1 < k$. -/
theorem sub_one_lt_of_pos {k : ℕ} (hk : 0 < k) : k - 1 < k := by omega

/-- **Increasing subsequence.** For $f : \{0, \dots, N-1\} \to \mathbb{R}$ and $k \in \mathbb{N}$,
a map $\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ is an increasing subsequence of $f$ of
length $k$ when $\varphi(i) < \varphi(j)$ and $f(\varphi(i)) < f(\varphi(j))$ for all $i < j$. -/
def IsIncrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ i) < f (φ j))

/-- **Decreasing subsequence.** For $f : \{0, \dots, N-1\} \to \mathbb{R}$ and $k \in \mathbb{N}$,
a map $\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ is a decreasing subsequence of $f$ of
length $k$ when $\varphi(i) < \varphi(j)$ and $f(\varphi(j)) < f(\varphi(i))$ for all $i < j$. -/
def IsDecrSubseq {N : ℕ} (f : Fin N → ℝ) (k : ℕ) (φ : Fin k → Fin N) : Prop :=
  (∀ i j : Fin k, i < j → φ i < φ j) ∧
  (∀ i j : Fin k, i < j → f (φ j) < f (φ i))

/-- **Increasing subsequence ending at a position.** For $f : \{0, \dots, N-1\} \to \mathbb{R}$,
a position $p$ and $k \in \mathbb{N}$, this is the statement that $k \ge 1$ and $f$ has an
increasing subsequence $\varphi$ of length $k$ (indices and values strictly increasing) ending at
$p$, that is, with $\varphi(k-1) = p$. -/
def IsIncrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsIncrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- **Decreasing subsequence ending at a position.** For $f : \{0, \dots, N-1\} \to \mathbb{R}$,
a position $p$ and $k \in \mathbb{N}$, this is the statement that $k \ge 1$ and $f$ has a
decreasing subsequence $\varphi$ of length $k$ (indices strictly increasing and values strictly
decreasing) ending at $p$, that is, with $\varphi(k-1) = p$. -/
def IsDecrEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ) : Prop :=
  ∃ (hk : 0 < k) (φ : Fin k → Fin N),
    IsDecrSubseq f k φ ∧ φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = p

/-- Classical decidability for filtering positions by `IsIncrEnd`. -/
noncomputable instance decIncrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsIncrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- Classical decidability for filtering positions by `IsDecrEnd`. -/
noncomputable instance decDecrEnd (N : ℕ) (f : Fin N → ℝ) (p : Fin N) :
    DecidablePred (IsDecrEnd f p) :=
  fun _ => Classical.propDecidable _

/-- **No strict pair in a one-element set.** There are no $i, j \in \{0\}$ with $i < j$. -/
theorem fin1_false {i j : Fin 1} (hij : i < j) : False := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have h1 := i.isLt
  have h2 := j.isLt
  omega

/-- **One-term subsequences are increasing.** For every real sequence $f$ indexed by
$\{0, \dots, N-1\}$ and every position $p$, the subsequence of length $1$ consisting of the term
at position $p$ is a strictly increasing subsequence of $f$. -/
theorem singleton_incr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- **One-term subsequences are decreasing.** For every real sequence $f$ indexed by
$\{0, \dots, N-1\}$ and every position $p$, the subsequence of length $1$ consisting of the term
at position $p$ is a strictly decreasing subsequence of $f$. -/
theorem singleton_decr {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrSubseq f 1 (fun _ => p) :=
  ⟨fun _ _ hij => False.elim (fin1_false hij),
    fun _ _ hij => False.elim (fin1_false hij)⟩

/-- **Length of the longest increasing subsequence ending at a position.** For
$f : \{0, \dots, N-1\} \to \mathbb{R}$ and a position $p$, this is the largest $k \le N$ such that
$f$ has an increasing subsequence of length $k$ ending at $p$, where indices and values both
increase strictly. -/
noncomputable def incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsIncrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_incr f p, rfl⟩⟩

/-- **Length of the longest decreasing subsequence ending at a point.** For a real sequence $f$
indexed by $\{0, \dots, N-1\}$ and an index $p$, this is the largest $k$ such that $f$ has a
strictly decreasing subsequence of length $k$ ending at $p$, that is, indices
$i_1 < \dots < i_k = p$ with $f(i_1) > \dots > f(i_k)$. The maximum exists: $k = 1$ qualifies, and
every such $k$ is at most $N$. -/
noncomputable def decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsDecrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_decr f p, rfl⟩⟩

/-- **Subsequences are no longer than the sequence.** If
$\varphi \colon \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ is strictly increasing, that is
$\varphi(i) < \varphi(j)$ whenever $i < j$, then $k \le N$. -/
theorem subseqLen_le {N k : ℕ} {φ : Fin k → Fin N}
    (hidx : ∀ i j : Fin k, i < j → φ i < φ j) : k ≤ N := by
  have hinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    rcases lt_trichotomy i j with h | h | h
    · exact (ne_of_lt (hidx i j h)) hij
    · exact hne h
    · exact (ne_of_gt (hidx j i h)) hij
  have hcard := Fintype.card_le_of_injective φ hinj
  simp only [Fintype.card_fin] at hcard
  exact hcard

/-- **The longest increasing subsequence ending at a position is attained.** For every
$f : \{0, \dots, N-1\} \to \mathbb{R}$ and every position $p$, $f$ has an increasing subsequence
ending at $p$ whose length equals the length of the longest increasing subsequence of $f$ ending
at $p$. -/
theorem incrLen_isEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsIncrEnd f p (incrLen f p) :=
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- **The longest decreasing subsequence ending at a point is attained.** For every real sequence
$f$ indexed by $\{0, \dots, N-1\}$ and every index $p$, $f$ has a strictly decreasing subsequence
ending at $p$ whose length equals the length of the longest strictly decreasing subsequence of $f$
ending at $p$. -/
theorem decrLen_isEnd {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    IsDecrEnd f p (decrLen f p) :=
  (Finset.mem_filter.mp (Finset.max'_mem _ _)).2

/-- **Bound by the longest increasing subsequence ending at a position.** Let $f$ be a real
sequence indexed by $\{0, \dots, N-1\}$ and let $p$ be a position. If $f$ has a strictly
increasing subsequence of length $k$ ending exactly at $p$, then $k$ is at most the length of the
longest strictly increasing subsequence of $f$ ending at $p$. -/
theorem le_incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ)
    (h : IsIncrEnd f p k) : k ≤ incrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsIncrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

/-- **Bound by the longest decreasing subsequence ending at a position.** Let $f$ be a real
sequence indexed by $\{0, \dots, N-1\}$ and let $p$ be a position. If $f$ has a strictly
decreasing subsequence of length $k$ ending exactly at $p$, then $k$ is at most the length of the
longest strictly decreasing subsequence of $f$ ending at $p$. -/
theorem le_decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) (k : ℕ)
    (h : IsDecrEnd f p k) : k ≤ decrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := h
  have hkN : k ≤ N := subseqLen_le hsub.1
  have hmem : k ∈ (Finset.range (N + 1)).filter (IsDecrEnd f p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk, φ, hsub, hlast⟩
  exact Finset.le_max' _ k hmem

/-- **Longest increasing subsequences ending at a position have length at least one.** For every
$f : \{0, \dots, N-1\} \to \mathbb{R}$ and every position $p$, the length of the longest
increasing subsequence of $f$ ending at $p$ is at least $1$. -/
theorem incrLen_ge_one {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    1 ≤ incrLen f p :=
  le_incrLen f p 1 ⟨by omega, fun _ => p, singleton_incr f p, rfl⟩

/-- **The longest decreasing subsequence ending at a point has length at least one.** For every
real sequence $f$ indexed by $\{0, \dots, N-1\}$ and every index $p$, the length of the longest
strictly decreasing subsequence of $f$ ending at $p$ is at least $1$. -/
theorem decrLen_ge_one {N : ℕ} (f : Fin N → ℝ) (p : Fin N) :
    1 ≤ decrLen f p :=
  le_decrLen f p 1 ⟨by omega, fun _ => p, singleton_decr f p, rfl⟩

/-- **Appending an entry to a map of indices.** Given
$\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ and $p \in \{0, \dots, N-1\}$, the appended map
on $\{0, \dots, k\}$ sends each $i < k$ to $\varphi(i)$ and sends $k$ to $p$. -/
def extendMap {N k : ℕ} (φ : Fin k → Fin N) (p : Fin N) : Fin (k + 1) → Fin N :=
  fun i => if h : i.val < k then φ ⟨i.val, h⟩ else p

/-- **Entries of a strictly increasing index map lie at or below its last entry.** Let $k \ge 1$
and let $\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ be strictly increasing with
$\varphi(k-1) = q$. Then $\varphi(i) \le q$ for every $i < k$. -/
theorem idx_le_last {N k : ℕ} {q : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    φ ⟨i.val, hik⟩ ≤ q := by
  have hval : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hidx _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

/-- **The last value is the largest along a strictly increasing selection.** Let $f$ be a real
sequence indexed by $\{0, \dots, N-1\}$, let $k \ge 1$, and let $\varphi$ map
$\{0, \dots, k-1\}$ to $\{0, \dots, N-1\}$ so that $f(\varphi(i)) < f(\varphi(j))$ whenever
$i < j < k$. If $\varphi(k-1) = q$, then $f(\varphi(i)) \le f(q)$ for every $i < k$. -/
theorem val_le_last_incr {N k : ℕ} {f : Fin N → ℝ} {q : Fin N}
    {φ : Fin k → Fin N} (hk : 0 < k)
    (hval : ∀ i j : Fin k, i < j → f (φ i) < f (φ j))
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    f (φ ⟨i.val, hik⟩) ≤ f q := by
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, hlast]

/-- **The last value is the smallest along a strictly decreasing selection.** Let $f$ be a real
sequence indexed by $\{0, \dots, N-1\}$, let $k \ge 1$, and let $\varphi$ map
$\{0, \dots, k-1\}$ to $\{0, \dots, N-1\}$ so that $f(\varphi(j)) < f(\varphi(i))$ whenever
$i < j < k$. If $\varphi(k-1) = q$, then $f(q) \le f(\varphi(i))$ for every $i < k$. -/
theorem last_le_val_decr {N k : ℕ} {f : Fin N → ℝ} {q : Fin N}
    {φ : Fin k → Fin N} (hk : 0 < k)
    (hval : ∀ i j : Fin k, i < j → f (φ j) < f (φ i))
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    {i : Fin (k + 1)} (hik : i.val < k) :
    f q ≤ f (φ ⟨i.val, hik⟩) := by
  have hval0 : i.val ≤ k - 1 := by omega
  have hle : (⟨i.val, hik⟩ : Fin k) ≤ ⟨k - 1, sub_one_lt_of_pos hk⟩ :=
    Fin.le_def.mpr hval0
  rcases lt_or_eq_of_le hle with h | h
  · have hlt := hval _ _ h
    rw [hlast] at hlt
    exact le_of_lt hlt
  · rw [h, ← hlast]

/-- **Appending a later index keeps indices increasing.** Let $k \ge 1$ and let
$\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ be strictly increasing with last value
$\varphi(k-1) = q$. If $p$ is an index with $q < p$, then the map on $\{0, \dots, k\}$ obtained by
appending $p$ to $\varphi$, which sends each $i < k$ to $\varphi(i)$ and sends $k$ to $p$, is
strictly increasing. -/
theorem extend_idx {N k : ℕ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q) (hqp : q < p)
    (i j : Fin (k + 1)) (hij : i < j) :
    extendMap φ p i < extendMap φ p j := by
  have hiv : i.val < j.val := Fin.lt_def.mp hij
  have hik : i.val < k := by omega
  change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
    (if h : j.val < k then φ ⟨j.val, h⟩ else p)
  by_cases hjk : j.val < k
  · rw [dite_eq_left hik, dite_eq_left hjk]
    exact hidx _ _ (Fin.lt_def.mpr hiv)
  · rw [dite_eq_left hik, dite_eq_right hjk]
    exact lt_of_le_of_lt (idx_le_last hk hidx hlast hik) hqp

/-- **The last entry of an appended map.** For every map
$\varphi : \{0, \dots, k-1\} \to \{0, \dots, N-1\}$ and every $p \in \{0, \dots, N-1\}$, the map
obtained by appending $p$ to $\varphi$ takes the value $p$ at its last index $k$. -/
theorem extend_last {N k : ℕ} (φ : Fin k → Fin N) {p : Fin N}
    (hk1 : 0 < k + 1) :
    extendMap φ p ⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ = p := by
  have hval : (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val =
      k + 1 - 1 := rfl
  have hneg : ¬ (⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ : Fin (k + 1)).val < k := by
    omega
  unfold extendMap
  exact dite_eq_right hneg

/-- **Extending an increasing subsequence.** Let $f : \{0, \dots, N-1\} \to \mathbb{R}$, let
$k \ge 1$, and let $\varphi$ be an increasing subsequence of $f$ of length $k$ (indices and values
strictly increasing) with last index $\varphi(k-1) = q$. If $p \in \{0, \dots, N-1\}$ satisfies
$q < p$ and $f(q) < f(p)$, then $f$ has an increasing subsequence of length $k + 1$ ending at
$p$. -/
theorem incrExtend {N k : ℕ} {f : Fin N → ℝ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hsub : IsIncrSubseq f k φ)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    (hqp : q < p) (hval : f q < f p) : IsIncrEnd f p (k + 1) := by
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.1 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (idx_le_last hk hsub.1 hlast hik) hqp
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : i.val < k then φ ⟨i.val, h⟩ else p) <
      f (if h : j.val < k then φ ⟨j.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_le_of_lt (val_le_last_incr hk hsub.2 hlast hik) hval

/-- **Extending a decreasing subsequence.** Let $f$ be a real sequence indexed by
$\{0, \dots, N-1\}$, let $k \ge 1$, and let $\varphi$ be a decreasing subsequence of $f$ of length
$k$, that is, indices $\varphi(0) < \dots < \varphi(k-1)$ with
$f(\varphi(0)) > \dots > f(\varphi(k-1))$, whose last index is $\varphi(k-1) = q$. If $p$ is an
index with $q < p$ and $f(p) < f(q)$, then $f$ has a decreasing subsequence of length $k + 1$ that
ends at $p$. -/
theorem decrExtend {N k : ℕ} {f : Fin N → ℝ} {q p : Fin N} {φ : Fin k → Fin N}
    (hk : 0 < k) (hsub : IsDecrSubseq f k φ)
    (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
    (hqp : q < p) (hval : f p < f q) : IsDecrEnd f p (k + 1) := by
  refine ⟨by omega, extendMap φ p, ⟨?_, ?_⟩, extend_last φ (by omega)⟩
  · intro i j hij
    exact extend_idx hk hsub.1 hlast hqp i j hij
  · intro i j hij
    have hiv : i.val < j.val := Fin.lt_def.mp hij
    have hik : i.val < k := by omega
    change f (if h : j.val < k then φ ⟨j.val, h⟩ else p) <
      f (if h : i.val < k then φ ⟨i.val, h⟩ else p)
    by_cases hjk : j.val < k
    · rw [dite_eq_left hik, dite_eq_left hjk]
      exact hsub.2 _ _ (Fin.lt_def.mpr hiv)
    · rw [dite_eq_left hik, dite_eq_right hjk]
      exact lt_of_lt_of_le hval (last_le_val_decr hk hsub.2 hlast hik)

/-- **Longest increasing subsequence lengths increase strictly along increasing pairs.** Let
$f : \{0, \dots, N-1\} \to \mathbb{R}$ and let $q < p$ be positions with $f(q) < f(p)$. Then the
length of the longest increasing subsequence of $f$ ending at $q$ is strictly less than the
length of the longest increasing subsequence of $f$ ending at $p$. -/
theorem incrMono {N : ℕ} (f : Fin N → ℝ) {q p : Fin N}
    (hqp : q < p) (hval : f q < f p) : incrLen f q < incrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := incrLen_isEnd f q
  have hle : incrLen f q + 1 ≤ incrLen f p :=
    le_incrLen f p _ (incrExtend hk hsub hlast hqp hval)
  omega

/-- **Longest decreasing subsequence lengths grow along a descent.** Let $f$ be a real sequence
indexed by $\{0, \dots, N-1\}$, and let $q < p$ be indices with $f(p) < f(q)$. Then the length of
the longest strictly decreasing subsequence of $f$ ending at $q$ is strictly less than the length
of the longest strictly decreasing subsequence of $f$ ending at $p$. -/
theorem decrMono {N : ℕ} (f : Fin N → ℝ) {q p : Fin N}
    (hqp : q < p) (hval : f p < f q) : decrLen f q < decrLen f p := by
  obtain ⟨hk, φ, hsub, hlast⟩ := decrLen_isEnd f q
  have hle : decrLen f q + 1 ≤ decrLen f p :=
    le_decrLen f p _ (decrExtend hk hsub hlast hqp hval)
  omega

/-- **Increasing subsequences of every smaller length.** Let $f$ be a real sequence indexed by
$\{0, \dots, N-1\}$. If $f$ has a strictly increasing subsequence of length $k$, then for every
$r \le k$ it has a strictly increasing subsequence of length $r$. -/
theorem truncIncr {N k r : ℕ} {f : Fin N → ℝ} {φ : Fin k → Fin N}
    (hsub : IsIncrSubseq f k φ) (hrk : r ≤ k) :
    ∃ φ' : Fin r → Fin N, IsIncrSubseq f r φ' :=
  ⟨fun i => φ (Fin.castLE hrk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

/-- **Decreasing subsequences of every smaller length.** Let $f$ be a real sequence indexed by
$\{0, \dots, N-1\}$. If $f$ has a strictly decreasing subsequence of length $k$, then for every
$s \le k$ it has a strictly decreasing subsequence of length $s$. -/
theorem truncDecr {N k s : ℕ} {f : Fin N → ℝ} {φ : Fin k → Fin N}
    (hsub : IsDecrSubseq f k φ) (hsk : s ≤ k) :
    ∃ ψ : Fin s → Fin N, IsDecrSubseq f s ψ :=
  ⟨fun i => φ (Fin.castLE hsk i), fun _ _ hij => hsub.1 _ _ hij,
    fun _ _ hij => hsub.2 _ _ hij⟩

/-- **Erdős–Szekeres theorem.** Let $r, s \ge 1$ be natural numbers, let $N = (r - 1)(s - 1) + 1$,
and let $f$ be an injective real sequence indexed by $\{0, \dots, N-1\}$. Then $f$ has a strictly
increasing subsequence of length $r$, that is, indices $i_1 < \dots < i_r$ with
$f(i_1) < \dots < f(i_r)$, or a strictly decreasing subsequence of length $s$, that is, indices
$j_1 < \dots < j_s$ with $f(j_1) > \dots > f(j_s)$. -/
public theorem erdos_szekeres {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (f : Fin ((r - 1) * (s - 1) + 1) → ℝ) (hinj : Function.Injective f) :
    (∃ φ : Fin r → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin r, i < j → φ i < φ j) ∧
      (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((r - 1) * (s - 1) + 1),
      (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
      (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) := by
  classical
  by_cases hr1 : r = 1
  · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
    subst hr1
    refine Or.inl ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
      exact False.elim (fin1_false hij)
  · by_cases hs1 : s = 1
    · have hNpos : 0 < (r - 1) * (s - 1) + 1 := Nat.succ_pos _
      subst hs1
      refine Or.inr ⟨fun _ => ⟨0, hNpos⟩, ?_, ?_⟩ <;> intro i j hij <;>
        exact False.elim (fin1_false hij)
    · have hr2 : 1 < r := by omega
      have hs2 : 1 < s := by omega
      by_cases ha : ∃ p, r ≤ incrLen f p
      · obtain ⟨p, hp⟩ := ha
        obtain ⟨_, φ, hsub, _⟩ := incrLen_isEnd f p
        obtain ⟨φ', hsub'⟩ := truncIncr hsub hp
        exact Or.inl ⟨φ', hsub'.1, hsub'.2⟩
      · by_cases hb : ∃ p, s ≤ decrLen f p
        · obtain ⟨p, hp⟩ := hb
          obtain ⟨_, φ, hsub, _⟩ := decrLen_isEnd f p
          obtain ⟨ψ, hsub'⟩ := truncDecr hsub hp
          exact Or.inr ⟨ψ, hsub'.1, hsub'.2⟩
        · have ha' : ∀ p, incrLen f p < r :=
            fun p => not_le.mp (fun h => ha ⟨p, h⟩)
          have hb' : ∀ p, decrLen f p < s :=
            fun p => not_le.mp (fun h => hb ⟨p, h⟩)
          have hmem1 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
              incrLen f p - 1 < r - 1 := by
            intro p
            have h1 := incrLen_ge_one f p
            have h2 := ha' p
            omega
          have hmem2 : ∀ p : Fin ((r - 1) * (s - 1) + 1),
              decrLen f p - 1 < s - 1 := by
            intro p
            have h1 := decrLen_ge_one f p
            have h2 := hb' p
            omega
          have hcard :
              (Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))).card <
              (Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1))).card := by
            rw [Finset.card_univ, Finset.card_univ, Fintype.card_prod,
              Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
            exact Nat.lt_succ_self _
          have hmap : Set.MapsTo
              (fun p : Fin ((r - 1) * (s - 1) + 1) =>
                ((⟨incrLen f p - 1, hmem1 p⟩ : Fin (r - 1)),
                  (⟨decrLen f p - 1, hmem2 p⟩ : Fin (s - 1))))
              ↑(Finset.univ : Finset (Fin ((r - 1) * (s - 1) + 1)))
              ↑(Finset.univ : Finset (Fin (r - 1) × Fin (s - 1))) := by
            intro x _
            exact Finset.mem_univ _
          obtain ⟨x, _, y, _, hne, heq⟩ :=
            Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap
          have ha_mk : (⟨incrLen f x - 1, hmem1 x⟩ : Fin (r - 1)) =
              ⟨incrLen f y - 1, hmem1 y⟩ :=
            congrArg Prod.fst heq
          have hb_mk : (⟨decrLen f x - 1, hmem2 x⟩ : Fin (s - 1)) =
              ⟨decrLen f y - 1, hmem2 y⟩ :=
            congrArg Prod.snd heq
          have ha_sub : incrLen f x - 1 = incrLen f y - 1 :=
            Fin.ext_iff.mp ha_mk
          have hb_sub : decrLen f x - 1 = decrLen f y - 1 :=
            Fin.ext_iff.mp hb_mk
          have ha_eq : incrLen f x = incrLen f y := by
            have h1 := incrLen_ge_one f x
            have h2 := incrLen_ge_one f y
            omega
          have hb_eq : decrLen f x = decrLen f y := by
            have h1 := decrLen_ge_one f x
            have h2 := decrLen_ge_one f y
            omega
          have hval_ne : x.val ≠ y.val := fun h => hne (Fin.ext_iff.mpr h)
          rcases lt_trichotomy x.val y.val with hlt | heq_val | hgt
          · have hxy : x < y := Fin.lt_def.mpr hlt
            have hfne : f x ≠ f y := fun h => hne (hinj h)
            rcases lt_trichotomy (f x) (f y) with hltf | heqf | hgtf
            · exfalso
              have hm := incrMono f hxy hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hxy hgtf
              omega
          · exact absurd heq_val hval_ne
          · have hyx : y < x := Fin.lt_def.mpr hgt
            have hfne : f y ≠ f x := fun h => hne (hinj h).symm
            rcases lt_trichotomy (f y) (f x) with hltf | heqf | hgtf
            · exfalso
              have hm := incrMono f hyx hltf
              omega
            · exact absurd heqf hfne
            · exfalso
              have hm := decrMono f hyx hgtf
              omega

end MathlibExt.Combinatorics.Order.ErdosSzekeres
