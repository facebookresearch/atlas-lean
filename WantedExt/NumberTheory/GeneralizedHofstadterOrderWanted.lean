/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pointwise order of generalized Hofstadter functions

Statements from Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions).

For `k ≥ 1`, `F_k(0) = 0` and `F_k(n) = n - F_k^k(n - 1)` (`hofstadterF`; exponents are
iterates, written `f^[j]`). `F_2` is Hofstadter's `G` and `F_3` is `H`. The substitution
`τ_k` maps `k ↦ k 1` and `i ↦ i + 1` for `1 ≤ i < k` (`hofTau`), `x_k` is its fixed point,
read off the prefixes `τ_k^n(k)` (`hofWord`), `L_k(n) = |τ_k(x_k[0:n))|` (`hofL`), and
`C_k^{(P)}(n) = #{0 ≤ j < n : P(x_k[j])}` (`hofCount`). The constants `α_k` and `β_k`, the
positive zeros of `X^k + X - 1` and `X^k - X^{k-1} - 1`, enter statements as hypotheses on a
real root, so no new definition is needed. The paper's `f <_∞ g` is `∀ᶠ n in atTop, f n < g n`.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- Fuel-bounded evaluation of the generalized Hofstadter recursion: `p` bounds the recursion
depth (the paper's Rocq encoding `recf`).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.4 (Rocq definition `recf`). -/
def hofstadterFAux (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | p + 1, n => n - (hofstadterFAux k p)^[k] (n - 1)

/-- The generalized Hofstadter function `F_k`: `F_k(0) = 0` and `F_k(n) = n - F_k^k(n - 1)`
for `n ≥ 1` (see `hofstadterF_zero` and `hofstadterF_eq`).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
def hofstadterF (k n : ℕ) : ℕ :=
  hofstadterFAux k n n

/-- `hofstadterFAux k p n ≤ n`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1 (`0 ≤ F_k(n) ≤ n`). -/
theorem hofstadterFAux_le (k p n : ℕ) : hofstadterFAux k p n ≤ n := by
  cases p with
  | zero => simp [hofstadterFAux]
  | succ p => simp only [hofstadterFAux]; omega

private theorem iterate_eq_of_eqOn {f g : ℕ → ℕ} (N : ℕ) (hf : ∀ m, f m ≤ m)
    (hfg : ∀ m ≤ N, f m = g m) : ∀ j x, x ≤ N → f^[j] x = g^[j] x := by
  intro j
  induction j with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg x hx]
    exact ih _ ((hf x).trans hx)

private theorem hofstadterFAux_succ_eq (k : ℕ) :
    ∀ p n, n ≤ p → hofstadterFAux k (p + 1) n = hofstadterFAux k p n := by
  intro p
  induction p with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp [hofstadterFAux]
  | succ p ih =>
    intro n hn
    change n - (hofstadterFAux k (p + 1))^[k] (n - 1) = n - (hofstadterFAux k p)^[k] (n - 1)
    rw [iterate_eq_of_eqOn p (hofstadterFAux_le k (p + 1)) ih k (n - 1) (by omega)]

private theorem hofstadterFAux_eq_of_le (k : ℕ) {p n : ℕ} (h : n ≤ p) :
    hofstadterFAux k p n = hofstadterF k n := by
  induction p, h using Nat.le_induction with
  | base => rfl
  | succ p hnp ih => rw [hofstadterFAux_succ_eq k p n hnp, ih]

/-- `F_k(0) = 0`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
theorem hofstadterF_zero (k : ℕ) : hofstadterF k 0 = 0 := rfl

/-- The defining recursion `F_k(n) = n - F_k^k(n - 1)` for `n ≥ 1` (the paper's Rocq lemma
`f_eqn`).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.1. -/
theorem hofstadterF_eq (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    hofstadterF k n = n - (hofstadterF k)^[k] (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change m + 1 - (hofstadterFAux k m)^[k] (m + 1 - 1) = _
  rw [iterate_eq_of_eqOn m (hofstadterFAux_le k m) (fun x hx => hofstadterFAux_eq_of_le k hx)
    k (m + 1 - 1) (by omega)]

/-- First values of `F_2 = G` (OEIS A005206) and `F_3 = H` (OEIS A005374).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Figure 1. -/
theorem hofstadterF_small_values :
    (List.range 11).map (hofstadterF 2) = [0, 1, 1, 2, 3, 3, 4, 4, 5, 6, 6] ∧
      (List.range 11).map (hofstadterF 3) = [0, 1, 1, 2, 3, 4, 4, 5, 5, 6, 7] := by
  decide

/-- The substitution `τ_k`: `k ↦ k 1` and `i ↦ i + 1` (used for `1 ≤ i < k`).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofTau (k i : ℕ) : List ℕ :=
  if i = k then [k, 1] else [i + 1]

/-- `τ_k` extended to finite words as a morphism.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofTauList (k : ℕ) (w : List ℕ) : List ℕ :=
  w.flatMap (hofTau k)

/-- Each letter is replaced by a nonempty word under `τ_k`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (definition of `τ_k`). -/
theorem one_le_length_hofTau (k i : ℕ) : 1 ≤ (hofTau k i).length := by
  unfold hofTau
  split <;> simp

/-- `τ_k` does not shorten words.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (definition of `τ_k`). -/
theorem length_le_length_hofTauList (k : ℕ) (w : List ℕ) :
    w.length ≤ (hofTauList k w).length := by
  induction w with
  | nil => simp [hofTauList]
  | cons a w ih =>
    simp only [hofTauList, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have := one_le_length_hofTau k a
    omega

/-- `τ_k` preserves prefixes.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (`τ_k` is a morphism). -/
theorem hofTauList_isPrefix {k : ℕ} {u v : List ℕ} (h : u <+: v) :
    hofTauList k u <+: hofTauList k v := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨hofTauList k t, by simp [hofTauList, List.flatMap_append]⟩

/-- Every prefix `τ_k^j(k)` begins with the letter `k`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (`τ_k(k) = k 1`). -/
theorem exists_hofTauList_iterate_eq_cons (k j : ℕ) :
    ∃ r, (hofTauList k)^[j] [k] = k :: r := by
  induction j with
  | zero => exact ⟨[], rfl⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨1 :: hofTauList k r, ?_⟩
    rw [Function.iterate_succ_apply', hr]
    simp [hofTauList, hofTau]

/-- The prefix `τ_k^j(k)` has length at least `j + 1`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem succ_le_length_hofTauList_iterate (k j : ℕ) :
    j + 1 ≤ ((hofTauList k)^[j] [k]).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨r, hr⟩ := exists_hofTauList_iterate_eq_cons k j
    rw [Function.iterate_succ_apply', hr]
    rw [hr] at ih
    have := length_le_length_hofTauList k r
    have h2 : (hofTauList k (k :: r)).length = 2 + (hofTauList k r).length := by
      simp [hofTauList, hofTau]
      omega
    rw [h2]
    simp only [List.length_cons] at ih
    omega

/-- `τ_k^j(k)` is a prefix of `τ_k^{j+1}(k)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofTauList_iterate_isPrefix_succ (k j : ℕ) :
    (hofTauList k)^[j] [k] <+: (hofTauList k)^[j + 1] [k] := by
  induction j with
  | zero => exact ⟨[1], by simp [hofTauList, hofTau]⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply' (hofTauList k) j,
      Function.iterate_succ_apply' (hofTauList k) (j + 1)]
    exact hofTauList_isPrefix ih

/-- Coherence of the prefixes: `τ_k^i(k)` is a prefix of `τ_k^j(k)` for `i ≤ j`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofTauList_iterate_isPrefix (k : ℕ) {i j : ℕ} (hij : i ≤ j) :
    (hofTauList k)^[i] [k] <+: (hofTauList k)^[j] [k] := by
  induction hij with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (hofTauList_iterate_isPrefix_succ k _)

/-- Apply `τ_k` to `w` until the word has more than `n` letters, with fuel `f`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
def hofGrowAux (k n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, w => w
  | f + 1, w => if n < w.length then w else hofGrowAux k n f (hofTauList k w)

/-- The shortest prefix `τ_k^j(k)` with more than `n` letters; at most `n` substitution steps
are needed, and each step at most doubles the length.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
def hofGrow (k n : ℕ) : List ℕ :=
  hofGrowAux k n n [k]

/-- Growing from a prefix `τ_k^j(k)` yields a prefix `τ_k^m(k)` that has more than `n` letters
or used all `f` steps.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
theorem hofGrowAux_iterate (k n f j : ℕ) :
    ∃ m, hofGrowAux k n f ((hofTauList k)^[j] [k]) = (hofTauList k)^[m] [k] ∧
      (n < ((hofTauList k)^[m] [k]).length ∨ j + f ≤ m) := by
  induction f generalizing j with
  | zero => exact ⟨j, rfl, Or.inr le_rfl⟩
  | succ f ih =>
    by_cases h : n < ((hofTauList k)^[j] [k]).length
    · exact ⟨j, by simp [hofGrowAux, h], Or.inl h⟩
    · obtain ⟨m, hm, hm'⟩ := ih (j + 1)
      refine ⟨m, ?_, hm'.imp_right fun h' => by omega⟩
      simp only [hofGrowAux, h, ↓reduceIte]
      rw [← Function.iterate_succ_apply' (hofTauList k) j, hm]

/-- `hofGrow k n` is a prefix `τ_k^m(k)` with more than `n` letters.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (prefixes `τ_k^j(k)` of `x_k`). -/
theorem exists_hofGrow_eq (k n : ℕ) :
    ∃ m, hofGrow k n = (hofTauList k)^[m] [k] ∧ n < (hofGrow k n).length := by
  obtain ⟨m, hm, hm'⟩ := hofGrowAux_iterate k n n 0
  refine ⟨m, hm, ?_⟩
  rw [hofGrow, show [k] = (hofTauList k)^[0] [k] from rfl, hm]
  rcases hm' with h | h
  · exact h
  · have := succ_le_length_hofTauList_iterate k m
    omega

/-- The letter `x_k[n]` of the fixed point `x_k` of `τ_k`, read off the shortest prefix
`τ_k^j(k)` with more than `n` letters (`hofWord_eq_getElem` gives every longer prefix).

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
def hofWord (k n : ℕ) : ℕ :=
  (hofGrow k n).getD n 0

/-- `x_k[n]` is the `n`-th letter of every prefix `τ_k^j(k)` long enough to contain it.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2 (the fixed point `x_k` is the limit of `τ_k^j(k)`). -/
theorem hofWord_eq_getElem (k n j : ℕ) (h : n < ((hofTauList k)^[j] [k]).length) :
    hofWord k n = ((hofTauList k)^[j] [k])[n] := by
  obtain ⟨m, hm, hlen⟩ := exists_hofGrow_eq k n
  rw [hofWord, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp only [hm] at hlen ⊢
  rcases le_total m j with hmj | hjm
  · exact (hofTauList_iterate_isPrefix k hmj).getElem hlen
  · exact ((hofTauList_iterate_isPrefix k hjm).getElem h).symm

/-- `x_k[n]` is the `n`-th letter of `τ_k^n(k)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 1.2. -/
theorem hofWord_eq_getElem_self (k n : ℕ) :
    hofWord k n = ((hofTauList k)^[n] [k])[n]'(succ_le_length_hofTauList_iterate k n) :=
  hofWord_eq_getElem k n n _

/-- The prefix `x_k[0:n)`, cut from one prefix `τ_k^j(k)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
def hofPrefix (k n : ℕ) : List ℕ :=
  (hofGrow k n).take n

/-- `x_k[0:n)` lists the letters `x_k[0], …, x_k[n-1]`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
theorem hofPrefix_eq_map (k n : ℕ) : hofPrefix k n = (List.range n).map (hofWord k) := by
  obtain ⟨m, hm, hlen⟩ := exists_hofGrow_eq k n
  apply List.ext_getElem
  · simp [hofPrefix]
    omega
  · intro i h₁ h₂
    simp only [hofPrefix, List.getElem_take, List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h₂
    rw [hm] at hlen
    rw [hofWord_eq_getElem k i m (by omega)]
    simp only [hm]

/-- `L_k(n) = |τ_k(x_k[0:n))|`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 2. -/
def hofL (k n : ℕ) : ℕ :=
  (hofTauList k (hofPrefix k n)).length

/-- `C_k^{(P)}(n) = #{0 ≤ j < n : P(x_k[j])}`, counted along the prefix `x_k[0:n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 4. -/
def hofCount (k : ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  (hofPrefix k n).countP fun a => decide (P a)

/-- `C_k^{(P)}(n)` is the number of indices `j < n` with `P(x_k[j])`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Section 4. -/
theorem hofCount_eq_card (k : ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    hofCount k P n = ((Finset.range n).filter fun j => P (hofWord k j)).card := by
  rw [hofCount, hofPrefix_eq_map, List.countP_map, List.countP_eq_length_filter]
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  rfl

/-- First letters of the Fibonacci word `x_2 = 2122121…` and of `x_3 = 3123313…`, and first
values of `L_2`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Figure 2. -/
theorem hofWord_small_values :
    (List.range 8).map (hofWord 2) = [2, 1, 2, 2, 1, 2, 1, 2] ∧
      (List.range 8).map (hofWord 3) = [3, 1, 2, 3, 3, 1, 3, 1] ∧
      (List.range 6).map (hofL 2) = [0, 2, 3, 5, 7, 8] := by
  decide

/-- **Main theorem.** For all `k ≥ 1` and `n`, `F_k(n) ≤ F_{k+1}(n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 1 (`jis-2026-26.3.3-thm-1`). -/
public theorem_wanted hofstadterF_le_succ {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofstadterF k n ≤ hofstadterF (k + 1) n

/-- Basic properties of `F_k^j` for `j, k ≥ 1`: `F_k^j(1) = F_k^j(2) = 1`; `F_k^j(n) ≥ 1` for
`n ≥ 1`; `F_k^j(n) < n` for `n ≥ 2`; `∂F_k(n) = 1 - ∂F_k^k(n-1)` for `n ≥ 1`; `∂F_k^j(n) ∈
{0, 1}`; `F_k^j` is monotone and onto but not one-to-one.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 2 (`jis-2026-26.3.3-prop-2`). -/
public theorem_wanted hofstadterF_iterate_basic {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (hofstadterF k)^[j] 1 = 1 ∧ (hofstadterF k)^[j] 2 = 1 ∧
      (∀ n, 1 ≤ n → 1 ≤ (hofstadterF k)^[j] n) ∧
      (∀ n, 2 ≤ n → (hofstadterF k)^[j] n < n) ∧
      (∀ n, 1 ≤ n →
        (hofstadterF k (n + 1) : ℤ) - hofstadterF k n =
          1 - (((hofstadterF k)^[k] n : ℤ) - (hofstadterF k)^[k] (n - 1))) ∧
      (∀ n, (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n ∨
        (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n + 1) ∧
      Monotone (hofstadterF k)^[j] ∧ Function.Surjective (hofstadterF k)^[j] ∧
      ¬ Function.Injective (hofstadterF k)^[j]

/-- The prefixes `τ_k^j(k)`: `τ_k^j(k) = k 1 2 ⋯ j` for `j ≤ k`, and
`τ_k^j(k) = τ_k^{j-1}(k) τ_k^{j-k}(k)` for `j ≥ k`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 3 (`jis-2026-26.3.3-prop-3`). -/
public theorem_wanted hofTauList_iterate_self {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (j ≤ k → (hofTauList k)^[j] [k] = k :: List.range' 1 j) ∧
      (k ≤ j → (hofTauList k)^[j] [k] =
        (hofTauList k)^[j - 1] [k] ++ (hofTauList k)^[j - k] [k])

/-- Basic properties of `L_k^j` for `k ≥ 1`: `L_k^j(n) = |τ_k^j(x_k[0:n))|`; `L_k^j(0) = 0` and
`L_k^j(n+1) = L_k^j(n) + |τ_k^j(x_k[n])|`; `L_k^j(1) = j + 1` for `j ≤ k` and
`L_k^j(1) = L_k^{j-1}(1) + L_k^{j-k}(1)` for `j ≥ k`; `L_k^j` is strictly increasing in `n`;
`L_k^j(n) ≥ n` with equality only when `j = 0` or `n = 0`; for `n ≥ 1`, `j ↦ L_k^j(n)` is
strictly increasing.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 4 (`jis-2026-26.3.3-prop-4`). -/
public theorem_wanted hofL_iterate_basic {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∀ n, (hofL k)^[j] n = ((hofTauList k)^[j] (hofPrefix k n)).length) ∧
      (hofL k)^[j] 0 = 0 ∧
      (∀ n, (hofL k)^[j] (n + 1) =
        (hofL k)^[j] n + ((hofTauList k)^[j] [hofWord k n]).length) ∧
      (j ≤ k → (hofL k)^[j] 1 = j + 1) ∧
      (k ≤ j → (hofL k)^[j] 1 = (hofL k)^[j - 1] 1 + (hofL k)^[j - k] 1) ∧
      StrictMono (hofL k)^[j] ∧
      (∀ n, n ≤ (hofL k)^[j] n ∧ ((hofL k)^[j] n = n ↔ j = 0 ∨ n = 0)) ∧
      (∀ n, 1 ≤ n → StrictMono fun i => (hofL k)^[i] n)

/-- For `j ≥ 0` and `k, m ≥ 1` there is a unique `n ≥ 1` with `L_k^j(n-1) < m ≤ L_k^j(n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 5 (`jis-2026-26.3.3-prop-5`). -/
public theorem_wanted existsUnique_hofL_iterate_bracket {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (j : ℕ) :
    ∃! n, 1 ≤ n ∧ (hofL k)^[j] (n - 1) < m ∧ m ≤ (hofL k)^[j] n

/-- For `j ≥ 0` and `k ≥ 1`: (a) for `n ≥ 1`, `F_k^{-j}({n}) = (L_k^j(n-1), L_k^j(n)]`;
(b) equivalently, for `m ≥ 1`, `L_k^j(F_k^j(m) - 1) < m ≤ L_k^j(F_k^j(m))`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 6 (`jis-2026-26.3.3-thm-6`). -/
public theorem_wanted hofstadterF_iterate_preimage_eq_Ioc {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∀ n, 1 ≤ n →
      (hofstadterF k)^[j] ⁻¹' {n} = Set.Ioc ((hofL k)^[j] (n - 1)) ((hofL k)^[j] n)) ∧
      (∀ m, 1 ≤ m →
        (hofL k)^[j] ((hofstadterF k)^[j] m - 1) < m ∧ m ≤ (hofL k)^[j] ((hofstadterF k)^[j] m))

/-- For `j ≥ 0` and `k ≥ 1`, `F_k^j` and `L_k^j` form a Galois connection
(`F_k^j(n) ≤ m ↔ n ≤ L_k^j(m)`), and it is a Galois insertion: `F_k^j ∘ L_k^j = id`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 7 (`jis-2026-26.3.3-cor-7`). -/
public theorem_wanted hofstadterF_hofL_galoisInsertion {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    GaloisConnection (hofstadterF k)^[j] (hofL k)^[j] ∧
      ∀ m, (hofstadterF k)^[j] ((hofL k)^[j] m) = m

/-- For `k ≥ 1`: `F_k^{k-1}(n) = C_k^{(=k)}(n)`; `F_k^j(n) = C_k^{(>j)}(n)` for `0 ≤ j < k`;
`F_k^{k+i-1}(n) = C_k^{(=i)}(n+i)` for `1 ≤ i < k`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 8 (`jis-2026-26.3.3-prop-8`). -/
public theorem_wanted hofstadterF_iterate_eq_hofCount {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (hofstadterF k)^[k - 1] n = hofCount k (· = k) n ∧
      (∀ j < k, (hofstadterF k)^[j] n = hofCount k (j < ·) n) ∧
      (∀ i, 1 ≤ i → i < k → (hofstadterF k)^[k + i - 1] n = hofCount k (· = i) (n + i))

/-- For `k ≥ 1`, `L_k(n) = n + C_k^{(=k)}(n) = n + F_k^{k-1}(n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 9 (`jis-2026-26.3.3-prop-9`). -/
public theorem_wanted hofL_eq_add_hofCount {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofL k n = n + hofCount k (· = k) n ∧ hofL k n = n + (hofstadterF k)^[k - 1] n

/-- For `k > 1`, `F_k(n) = n - C_k^{(=1)}(n) = C_k^{(≠1)}(n)`; hence `∂F_k(n) = 0` exactly when
`x_k[n] = 1`, and `∂F_k(n) = 1` otherwise.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 10 (`jis-2026-26.3.3-prop-10`). -/
public theorem_wanted hofstadterF_eq_hofCount_ne_one {k : ℕ} (hk : 1 < k) (n : ℕ) :
    hofstadterF k n = n - hofCount k (· = 1) n ∧ hofstadterF k n = hofCount k (· ≠ 1) n ∧
      (hofstadterF k (n + 1) = hofstadterF k n ↔ hofWord k n = 1) ∧
      (hofWord k n ≠ 1 → hofstadterF k (n + 1) = hofstadterF k n + 1)

/-- For `1 ≤ j < k`, `x_k[n] = j` iff `∂F_k^{j-1}(n) = 1` and `∂F_k^j(n) = 0`; for `k ≥ 1`,
`x_k[n] = k` iff `∂F_k^{k-1}(n) = 1`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 11 (`jis-2026-26.3.3-prop-11`). -/
public theorem_wanted hofWord_eq_iff_hofstadterF_iterate_diff {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∀ j, 1 ≤ j → j < k →
      (hofWord k n = j ↔
        (hofstadterF k)^[j - 1] (n + 1) = (hofstadterF k)^[j - 1] n + 1 ∧
          (hofstadterF k)^[j] (n + 1) = (hofstadterF k)^[j] n)) ∧
      (hofWord k n = k ↔ (hofstadterF k)^[k - 1] (n + 1) = (hofstadterF k)^[k - 1] n + 1)

/-- Let `α_k`, `β_k` be the positive zeros of `X^k + X - 1` and `X^k - X^{k-1} - 1`. Then
`(α_k)` is strictly increasing and `(β_k)` strictly decreasing; `1 + 1/k ≤ β_k ≤ 1 + 1/√k`
and `√k ≤ β_k^{k-1} ≤ k`; `β_k → 1` and `α_k → 1`; and
`α_k = 1 - ln k / k + o(ln k / k)`, `β_k = 1 + ln k / k + o(ln k / k)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 13 and Definition 12 (`jis-2026-26.3.3-prop-13`). -/
public theorem_wanted hofstadter_roots_monotone_asymptotics (α β : ℕ → ℝ)
    (hα : ∀ k, 1 ≤ k → 0 < α k ∧ α k ^ k + α k - 1 = 0)
    (hβ : ∀ k, 1 ≤ k → 0 < β k ∧ β k ^ k - β k ^ (k - 1) - 1 = 0) :
    (∀ k, 1 ≤ k → α k < α (k + 1)) ∧ (∀ k, 1 ≤ k → β (k + 1) < β k) ∧
      (∀ k : ℕ, 1 ≤ k →
        1 + 1 / (k : ℝ) ≤ β k ∧ β k ≤ 1 + 1 / Real.sqrt k ∧
          Real.sqrt k ≤ β k ^ (k - 1) ∧ β k ^ (k - 1) ≤ k) ∧
      Tendsto β atTop (𝓝 1) ∧ Tendsto α atTop (𝓝 1) ∧
      (fun k : ℕ => α k - (1 - Real.log k / k)) =o[atTop] (fun k : ℕ => Real.log k / k) ∧
      (fun k : ℕ => β k - (1 + Real.log k / k)) =o[atTop] (fun k : ℕ => Real.log k / k)

/-- For `j ≥ 0` and `k ≥ 1`, with `α = α_k` and `β = β_k`: `F_k^j(n)/n → α^j`,
`L_k^j(n)/n → β^j`, the letter `i` has frequency `α^{k+i-1}` in `x_k` for `1 ≤ i < k`, and
the letter `k` has frequency `α^{k-1} = β - 1`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 14 (`jis-2026-26.3.3-thm-14`). -/
public theorem_wanted hofstadter_limits {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {α β : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hβ : 0 < β ∧ β ^ k - β ^ (k - 1) - 1 = 0) :
    Tendsto (fun n : ℕ => ((hofstadterF k)^[j] n : ℝ) / n) atTop (𝓝 (α ^ j)) ∧
      Tendsto (fun n : ℕ => ((hofL k)^[j] n : ℝ) / n) atTop (𝓝 (β ^ j)) ∧
      (∀ i, 1 ≤ i → i < k →
        Tendsto (fun n : ℕ => (hofCount k (· = i) n : ℝ) / n) atTop (𝓝 (α ^ (k + i - 1)))) ∧
      Tendsto (fun n : ℕ => (hofCount k (· = k) n : ℝ) / n) atTop (𝓝 (α ^ (k - 1))) ∧
      α ^ (k - 1) = β - 1

/-- If `α_k^j < α_{k'}^{j'}` (`k, k' ≥ 1`, `j, j' ≥ 0`), then `F_k^j <_∞ F_{k'}^{j'}`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 16 (`jis-2026-26.3.3-cor-16`). -/
public theorem_wanted hofstadterF_iterate_eventually_lt_of_root_pow_lt {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (j j' : ℕ) {α α' : ℝ} (hα : 0 < α ∧ α ^ k + α - 1 = 0)
    (hα' : 0 < α' ∧ α' ^ k' + α' - 1 = 0) (hlt : α ^ j < α' ^ j') :
    ∀ᶠ n in atTop, (hofstadterF k)^[j] n < (hofstadterF k')^[j'] n

/-- For `k ≥ 1` (with `α = α_k`, `α' = α_{k+1}`): `F_k <_∞ F_{k+1}`,
`F_k^k >_∞ F_{k+1}^{k+1}`, `F_k^{k+1} >_∞ F_{k+1}^{k+2}`; and for `j ≥ 0`,
(a) `F_k^{k+j} >_∞ F_{k+1}^{k+j+1}` when `α ≥ j/(j+1)`, in particular when `k ≥ j^2`;
(b) `F_k^{k+j} <_∞ F_{k+1}^{k+j+1}` when `α' ≤ j/(j+1)`, in particular when `k < j`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 17 (`jis-2026-26.3.3-cor-17`). -/
public theorem_wanted hofstadterF_iterate_eventual_order_succ {k : ℕ} (hk : 1 ≤ k) {α α' : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hα' : 0 < α' ∧ α' ^ (k + 1) + α' - 1 = 0) :
    (∀ᶠ n in atTop, hofstadterF k n < hofstadterF (k + 1) n) ∧
      (∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + 1] n < (hofstadterF k)^[k] n) ∧
      (∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + 2] n < (hofstadterF k)^[k + 1] n) ∧
      (∀ j : ℕ, ((j : ℝ) / (j + 1) ≤ α ∨ j ^ 2 ≤ k) →
        ∀ᶠ n in atTop, (hofstadterF (k + 1))^[k + j + 1] n < (hofstadterF k)^[k + j] n) ∧
      (∀ j : ℕ, (α' ≤ (j : ℝ) / (j + 1) ∨ k < j) →
        ∀ᶠ n in atTop, (hofstadterF k)^[k + j] n < (hofstadterF (k + 1))^[k + j + 1] n)

open Classical in
/-- For `k ≥ 1` let `U_k(n) = #{0 ≤ j < n : |F_k^{-1}({j})| = 1}`. For `n > 0`,
`U_k(n) = 2n - 1 - L_k(n-1) = n - F_k^{k-1}(n-1)`, and `U_k(n)/n → 1 - α_k^{k-1} = 2 - β_k`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 18 (`jis-2026-26.3.3-prop-18`). -/
public theorem_wanted hofstadter_single_antecedent_count {k : ℕ} (hk : 1 ≤ k) {α β : ℝ}
    (hα : 0 < α ∧ α ^ k + α - 1 = 0) (hβ : 0 < β ∧ β ^ k - β ^ (k - 1) - 1 = 0) :
    (∀ n, 0 < n →
      ((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card =
          2 * n - 1 - hofL k (n - 1) ∧
        ((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card =
          n - (hofstadterF k)^[k - 1] (n - 1)) ∧
      Tendsto (fun n : ℕ =>
          (((Finset.range n).filter fun j => Nat.card {m // hofstadterF k m = j} = 1).card : ℝ) /
            n) atTop (𝓝 (1 - α ^ (k - 1))) ∧
      1 - α ^ (k - 1) = 2 - β

/-- For `j, j' ≥ 0` and `k, k' ≥ 1`, `L_k^j ≤ L_{k'}^{j'}` iff `F_{k'}^{j'} ≤ F_k^j`; and for
every `n`: (a) `L_k^j(n) ≤ L_{k'}^{j'}(n)` iff `F_{k'}^{j'}(m) ≤ F_k^j(m)` with `m = L_k^j(n)`;
(b) `L_k^j(n) < L_{k'}^{j'}(n)` iff `F_{k'}^{j'}(m) < F_k^j(m)` with `m = L_{k'}^{j'}(n)`;
(c) `L_k^j(m) ≤ L_{k'}^{j'}(m)` for `m = F_k^j(n)` implies `F_{k'}^{j'}(n) ≤ F_k^j(n)`;
(d) `F_k^j(n) < F_{k'}^{j'}(n)` implies `L_{k'}^{j'}(m) < L_k^j(m)` for `m = F_k^j(n)`.
In (d) the paper prints `m = F_{k'}^{j'}(n)`; its proof derives (d) as the contrapositive of
(c), which gives `m = F_k^j(n)`. The printed form fails for `k = 1, j = 1, k' = 4, j' = 2,
n = 8`: `F_1(8) = 4 < F_4^2(8) = 5`, but `L_4^2(5) = L_1(5) = 10`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 19 (`jis-2026-26.3.3-prop-19`). -/
public theorem_wanted hofL_iterate_le_iff_hofstadterF_iterate_le {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (j j' : ℕ) :
    ((hofL k)^[j] ≤ (hofL k')^[j'] ↔ (hofstadterF k')^[j'] ≤ (hofstadterF k)^[j]) ∧
      ∀ n,
        ((hofL k)^[j] n ≤ (hofL k')^[j'] n ↔
          (hofstadterF k')^[j'] ((hofL k)^[j] n) ≤ (hofstadterF k)^[j] ((hofL k)^[j] n)) ∧
        ((hofL k)^[j] n < (hofL k')^[j'] n ↔
          (hofstadterF k')^[j'] ((hofL k')^[j'] n) < (hofstadterF k)^[j] ((hofL k')^[j'] n)) ∧
        ((hofL k)^[j] ((hofstadterF k)^[j] n) ≤ (hofL k')^[j'] ((hofstadterF k)^[j] n) →
          (hofstadterF k')^[j'] n ≤ (hofstadterF k)^[j] n) ∧
        ((hofstadterF k)^[j] n < (hofstadterF k')^[j'] n →
          (hofL k')^[j'] ((hofstadterF k)^[j] n) < (hofL k)^[j] ((hofstadterF k)^[j] n))

/-- For `k, n ≥ 1` and `0 ≤ j ≤ k`: `L_k(n) ≥ L_{k+1}(n)`, i.e.
`C_k^{(=k)}(n) ≥ C_{k+1}^{(=k+1)}(n)`, and `L_k^j(n) < L_{k+1}^{j+1}(n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 20 (`jis-2026-26.3.3-thm-20`). -/
public theorem_wanted hofL_succ_comparison {k n j : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : j ≤ k) :
    hofL (k + 1) n ≤ hofL k n ∧ hofCount (k + 1) (· = k + 1) n ≤ hofCount k (· = k) n ∧
      (hofL k)^[j] n < (hofL (k + 1))^[j + 1] n

/-- For `k ≥ 1` and `j ≥ 0`, `L_k^j ≥ L_{k+1}^j`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Corollary 21 (`jis-2026-26.3.3-cor-21`). -/
public theorem_wanted hofL_iterate_succ_le {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (hofL (k + 1))^[j] ≤ (hofL k)^[j]

/-- For `j ≥ 0` and `k ≥ 1`, `F_k^j ≤ F_{k+1}^j`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 22 (`jis-2026-26.3.3-thm-22`). -/
public theorem_wanted hofstadterF_iterate_le_succ {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (hofstadterF k)^[j] ≤ (hofstadterF (k + 1))^[j]

/-- For `k ≥ 1` and `0 ≤ j ≤ k`, `F_k^j ≥ F_{k+1}^{j+1}`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Theorem 23 (`jis-2026-26.3.3-thm-23`). -/
public theorem_wanted hofstadterF_iterate_succ_le_iterate {k j : ℕ} (hk : 1 ≤ k) (hj : j ≤ k) :
    (hofstadterF (k + 1))^[j + 1] ≤ (hofstadterF k)^[j]

/-- For `k ≥ 1`: `L_{k+1}^{j+1}(1) - L_k^j(1) = 1` for `0 ≤ j ≤ 2k`, and
`= -(j-2k-1)(j-2k+2)/2` for `2k ≤ j ≤ 3k` (stated with the `2` cleared, in `ℤ`); in particular
`L_{k+1}^{2k+2}(1) = L_k^{2k+1}(1)`; and `L_{k+1}^{j+1}(1) < L_k^j(1)` for `j ≥ 2k + 2`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Lemma 24 (`jis-2026-26.3.3-lem-24`). -/
public theorem_wanted hofL_iterate_one_succ_sub {k : ℕ} (hk : 1 ≤ k) :
    (∀ j, j ≤ 2 * k → ((hofL (k + 1))^[j + 1] 1 : ℤ) - (hofL k)^[j] 1 = 1) ∧
      (∀ j, 2 * k ≤ j → j ≤ 3 * k →
        2 * (((hofL (k + 1))^[j + 1] 1 : ℤ) - (hofL k)^[j] 1) =
          -(((j : ℤ) - 2 * k - 1) * ((j : ℤ) - 2 * k + 2))) ∧
      (hofL (k + 1))^[2 * k + 2] 1 = (hofL k)^[2 * k + 1] 1 ∧
      (∀ j, 2 * k + 2 ≤ j → (hofL (k + 1))^[j + 1] 1 < (hofL k)^[j] 1)

/-- For `k ≥ 1` and `j ≥ k + 2`, `L_k^j(n_j) > L_{k+1}^{j+1}(n_j)` where `n_j = 2k + 3 - j` if
`k + 2 ≤ j ≤ 2k + 2` and `n_j = 1` if `j ≥ 2k + 2`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Lemma 25 (`jis-2026-26.3.3-lem-25`). -/
public theorem_wanted hofL_iterate_witness_gt {k : ℕ} (hk : 1 ≤ k) :
    (∀ j, k + 2 ≤ j → j ≤ 2 * k + 2 →
      (hofL (k + 1))^[j + 1] (2 * k + 3 - j) < (hofL k)^[j] (2 * k + 3 - j)) ∧
      (∀ j, 2 * k + 2 ≤ j → (hofL (k + 1))^[j + 1] 1 < (hofL k)^[j] 1)

/-- For `k ≥ 1` and `n ≥ 0`, `C_k^{(=1)}(n) ≥ C_{k+1}^{(=1)}(n)`.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 26 (`jis-2026-26.3.3-prop-26`). -/
public theorem_wanted hofCount_one_succ_le {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    hofCount (k + 1) (· = 1) n ≤ hofCount k (· = 1) n

/-- For `3 ≤ i < k`: `C_k^{(=i)}(n) < C_{k+1}^{(=i)}(n)` at `n = i + L_k^{2k+2}(1)`, and
`C_k^{(=i)}(n) > C_{k+1}^{(=i)}(n)` at `n = i + L_{k+1}^{k+i}(1)`; so the letter counts of
`x_k` and `x_{k+1}` are not ordered for these letters.

Source: Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3,
Proposition 27 (`jis-2026-26.3.3-prop-27`). -/
public theorem_wanted hofCount_eq_witnesses {i k : ℕ} (hi : 3 ≤ i) (hik : i < k) :
    hofCount k (· = i) (i + (hofL k)^[2 * k + 2] 1) <
        hofCount (k + 1) (· = i) (i + (hofL k)^[2 * k + 2] 1) ∧
      hofCount (k + 1) (· = i) (i + (hofL (k + 1))^[k + i] 1) <
        hofCount k (· = i) (i + (hofL (k + 1))^[k + i] 1)

end

end MetaMathlibExt
