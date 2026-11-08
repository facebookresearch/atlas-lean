/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Free
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.List.OfFn
public import MathlibExt.Combinatorics.SemigroupLargeness

/-!
# Infinitary Hales–Jewett theorems for variable words

Statements quoted in Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary
Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74. A variable word over an alphabet `A` is
a list over `Option A` in which the variable `none` occurs; `w(a)` replaces every occurrence of
the variable by the letter `a`. Theorem 1.1 (Hales–Jewett) and Theorem 1.7 (`n`-variable words)
are Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension` and
`Combinatorics.Subspace.exists_mono_in_high_dimension`.

Section 3 of the paper fixes an increasing sequence of finite alphabets `A_0 ⊆ A_1 ⊆ ⋯` with
union `A`. Its statements are rendered with `A : ℕ → Finset α`, `Monotone A`, and the covering
hypothesis `∀ x, ∃ i, x ∈ A i`, so that the ambient type `α` is the alphabet `A` itself and the
semigroup `S_0` of nonempty words over `A` under concatenation is `FreeSemigroup α`. An
`n`-variable word (an element of `S_n`) is an element `w` of `FreeSemigroup (α ⊕ Fin n)` in which
every variable `Sum.inr i` occurs, and `w(a⃗)` is `FreeSemigroup.map (Sum.elim id a⃗) w`. Words
are indexed from `0` rather than `1`; since the alphabets increase, a sequence indexed from `1`
with `w_i` evaluated over `A_i` shifts to one indexed from `0` with `w_i` evaluated over `A_i`
(and conversely), so the shift does not change the statements. Products `x₀ x₁ ⋯ x_l` in a
semigroup are written as left folds `List.foldl (· * ·) x₀ [x₁, …, x_l]`. The largeness
notions (piecewise syndetic sets, `J`-sets, central sets, `C`-sets) are the reusable
definitions of `MathlibExt.Combinatorics.SemigroupLargeness`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Infinitary Hales–Jewett theorem. For a finite alphabet `A` and any finite coloring of the
words over `A`, there is a sequence `(w_n)` of variable words over `A` such that all words
`w_{m₁}(a₁) w_{m₂}(a₂) ⋯ w_{m_l}(a_l)` with `l ≥ 1`, `m₁ < ⋯ < m_l` and `a_i ∈ A` have the same
color.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.2 (Bergelson, Blass and Hindman). -/
public theorem_wanted infinitary_halesJewett {A κ : Type*} [Finite A] [Finite κ]
    (c : List A → κ) :
    ∃ (w : ℕ → List (Option A)) (k : κ), (∀ n, none ∈ w n) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → A), 1 ≤ l → StrictMono m →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

/-- Karagiannis's infinitary Hales–Jewett theorem for an increasing sequence of finite alphabets
`A_0 ⊆ A_1 ⊆ ⋯` with union `A`. For any finite coloring of the words over `A`, there is a
sequence `(w_n)` of variable words over `A` such that all words
`w_{m₁}(a₁) w_{m₂}(a₂) ⋯ w_{m_l}(a_l)` with `l ≥ 1`, `m₁ < ⋯ < m_l` and `a_i ∈ A_{m_i}` have the
same color. The coloring is given on all lists over the ambient type; only words over `A` are
evaluated.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 1.8 (Karagiannis). -/
public theorem_wanted infinitary_halesJewett_increasing_alphabets {α κ : Type*} [Finite κ]
    (A : ℕ → Finset α) (hA : Monotone A) (c : List α → κ) :
    ∃ (w : ℕ → List (Option α)) (k : κ),
      (∀ n, none ∈ w n ∧ ∀ x : α, some x ∈ w n → ∃ i, x ∈ A i) ∧
      ∀ (l : ℕ) (m : Fin l → ℕ) (a : Fin l → α), 1 ≤ l → StrictMono m →
        (∀ i, a i ∈ A (m i)) →
        c (List.ofFn fun i => (w (m i)).map fun o => o.getD (a i)).flatten = k

/-- A version of the Hales–Jewett theorem. Let `A_0 ⊆ A_1 ⊆ ⋯` be finite alphabets with union
`A`, and let `D ⊆ S_0` be piecewise syndetic in the semigroup `S_0` of words over `A`. For all
`m, n` there is an `n`-variable word `w` over `A` with `w(a⃗) ∈ D` for every `a⃗ ∈ A_m^n`. The
paper's family `F = {h_a⃗}` of substitution homomorphisms carries no extra hypothesis and is
omitted; `n = 0` is admitted (then the claim is `D ≠ ∅`).

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.3. -/
public theorem_wanted exists_variableWord_subst_mem_of_isMulPiecewiseSyndetic {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulPiecewiseSyndetic D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D

/-- The `J`-set version of Lemma 3.3: with `A_0 ⊆ A_1 ⊆ ⋯` and `S_0` as there, if `D ⊆ S_0` is a
`J`-set then for all `m, n` there is an `n`-variable word `w` over `A` with `w(a⃗) ∈ D` for every
`a⃗ ∈ A_m^n`. The family `F = {h_a⃗}` is omitted as in Lemma 3.3; `n = 0` is admitted. The
alphabet is assumed nonempty (`[Nonempty α]`): over the empty alphabet `S_0` is empty, every subset
is vacuously a `J`-set, and no word exists.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.4. -/
public theorem_wanted exists_variableWord_subst_mem_of_isMulJSet {α : Type*} [Nonempty α]
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D

/-- Infinitary Hales–Jewett configurations in central sets. With `A_0 ⊆ A_1 ⊆ ⋯` and `S_0` as in
Lemma 3.3, if `D ⊆ S_0` is central then for each `n` there is a sequence `(w_i)` of `n`-variable
words over `A` such that `w_{m_0}(a⃗_0) w_{m_1}(a⃗_1) ⋯ w_{m_l}(a⃗_l) ∈ D` whenever
`m_0 < m_1 < ⋯ < m_l` and `a⃗_j ∈ A_{m_j}^n`. The statement's duplicate binder `l` is read once;
`n` (free in the statement, fixed in the proof) is universally quantified, `n = 0` admitted.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.5. -/
public theorem_wanted exists_variableWords_prod_mem_of_isCentralSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCentralSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D

/-- The `C`-set version of Theorem 3.5: if `D ⊆ S_0` is a `C`-set then for each `n` there is a
sequence `(w_i)` of `n`-variable words over `A` with
`w_{m_0}(a⃗_0) ⋯ w_{m_l}(a⃗_l) ∈ D` whenever `m_0 < ⋯ < m_l` and `a⃗_j ∈ A_{m_j}^n`.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.6. -/
public theorem_wanted exists_variableWords_prod_mem_of_isCSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D

/-- Variable-count sums in `J`-sets. With `A_0 ⊆ A_1 ⊆ ⋯` and `S_0` as in Lemma 3.3, let `D ⊆ S_0`
be a `J`-set and `(x_j)` a sequence of positive integers. There is a sequence `(w_k)` of variable
words over `A` (the variable is `Sum.inr 0`) with `w_k(a) ∈ D` for all `k` and `a ∈ A_k`, and with
`∑_{k ∈ G} τ(w_k) ∈ FS(⟨x_j⟩)` for every nonempty finite `G`, where `τ(w) = |w|_v` counts the
occurrences of the variable and `FS(⟨x_j⟩)` is the set of sums of `x_j` over nonempty finite index
sets.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.7. -/
public theorem_wanted exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ k a, a ∈ A k → FreeSemigroup.map (Sum.elim id fun _ => a) (w k) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j

/-- The `C`-set version of Theorem 3.7: if `D ⊆ S_0` is a `C`-set and `(x_j)` is a sequence of
positive integers, there is a sequence `(w_k)` of variable words over `A` with
`w_{n_0}(a_0) ⋯ w_{n_l}(a_l) ∈ D` whenever `n_0 < ⋯ < n_l` and `a_j ∈ A_{n_j}`, and with
`∑_{k ∈ G} τ(w_k) ∈ FS(⟨x_j⟩)` for every nonempty finite `G`, `τ(w) = |w|_v`. The product over
`G = {n_1, …, n_l}` is taken in increasing order of the indices.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.8. -/
public theorem_wanted exists_variableWords_prod_mem_sum_count_mem_finiteSums_of_isCSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → α), StrictMono m →
        (∀ j, a j ∈ A (m j)) →
        (List.ofFn fun j : Fin l =>
            FreeSemigroup.map (Sum.elim id fun _ => a j.succ) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id fun _ => a 0) (w (m 0))) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j

/-- Variable patterns in `J`-sets. With `A_0 ⊆ A_1 ⊆ ⋯` and `S_0` as in Lemma 3.3, let
`1 ≤ k < n`, let `T` be the semigroup of words over `{v_1, …, v_k}` (here `Fin k`, words as
lists, product = concatenation) in which every `v_i` occurs, and for an `n`-variable word `w` let
`τ(w)` delete the letters of `A` and the variables `v_i`, `i > k`. For a sequence `(y_t)` in `T`
and a `J`-set `D ⊆ S_0` there is a sequence `(w_m)` of `n`-variable words over `A` with
`w_m(a⃗) ∈ D` for all `m` and `a⃗ ∈ A_m^n`, and with `τ(w_{m_0}) ⋯ τ(w_{m_l}) ∈ FP(⟨y_t⟩)` for all
`m_0 < ⋯ < m_l`, where `FP(⟨y_t⟩)` is the set of products `y_{t_0} ⋯ y_{t_r}`, `t_0 < ⋯ < t_r`.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.9. -/
public theorem_wanted exists_variableWords_subst_mem_prod_pattern_mem_finiteProducts_of_isMulJSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) (y : ℕ → List (Fin k)) (hy : ∀ t i, i ∈ y t)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ m i, Sum.inr i ∈ (w m).head :: (w m).tail) ∧
      (∀ m (a : Fin n → α), (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) (w m) ∈ D) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ), StrictMono m →
        ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧
          (List.ofFn fun j => ((w (m j)).head :: (w (m j)).tail).filterMap
              (Sum.elim (fun _ => none) fun i : Fin n =>
                if h : (i : ℕ) < k then some ⟨i, h⟩ else none)).flatten =
            (List.ofFn fun j => y (t j)).flatten

/-- The `C`-set version of Theorem 3.9: with `k, n, T, τ, (y_t)` as there and a `C`-set
`C ⊆ S_0`, there is a sequence `(w_m)` of `n`-variable words over `A` such that for all
`m_0 < ⋯ < m_l`, `w_{m_0}(a⃗_0) ⋯ w_{m_l}(a⃗_l) ∈ C` for all `a⃗_j ∈ A_{m_j}^n`, and
`τ(w_{m_0}) ⋯ τ(w_{m_l}) ∈ FP(⟨y_t⟩)`.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.10. -/
public theorem_wanted exists_variableWords_prod_mem_prod_pattern_mem_finiteProducts_of_isCSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) (y : ℕ → List (Fin k)) (hy : ∀ t i, i ∈ y t)
    {C : Set (FreeSemigroup α)} (hC : IsCSet C) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ m i, Sum.inr i ∈ (w m).head :: (w m).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ), StrictMono m →
        (∀ a : Fin (l + 1) → Fin n → α, (∀ j i, a j i ∈ A (m j)) →
          (List.ofFn fun j : Fin l =>
              FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
            (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ C) ∧
        ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧
          (List.ofFn fun j => ((w (m j)).head :: (w (m j)).tail).filterMap
              (Sum.elim (fun _ => none) fun i : Fin n =>
                if h : (i : ℕ) < k then some ⟨i, h⟩ else none)).flatten =
            (List.ofFn fun j => y (t j)).flatten

end

end MetaMathlibExt
