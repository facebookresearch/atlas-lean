/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Free
public import MathlibExt.Combinatorics.SemigroupLargeness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing

/-!
# Hales–Jewett configurations in large sets of words

Every piecewise syndetic set or J-set of nonempty words contains all substitutions of a variable
word over any given finite level of an increasing alphabet. In a J-set a sequence of words can
realize ordered finite products of prescribed variable patterns or finite sums of prescribed counts.
In a C-set one can choose the words so that all ordered products of their substitutions belong
to the set.

For an increasing sequence of finite alphabets with union `A`, a C-set of nonempty words over
`A`, and a sequence of positive integers, one sequence of one-variable words has both
properties: all nonempty increasing products of substitutions by letters from the respective
alphabet levels lie in the C-set, and the total variable count over any nonempty finite set of
levels is a nonempty finite sum from the input sequence.

## References

- Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales-Jewett Theorem*,
  INTEGERS **24** (2024), Article A74, pp. 1–12, §3. Corollary 3.8 combines the idempotent
  induction of Theorem 3.5 with the variable-count condition of Theorem 3.7.
- Aninda Chakraborty and Sayan Goswami, *Hales-Jewett type configurations in small sets*,
  European Journal of Combinatorics **104** (2022), Article 103539, Lemma 2.1, the
  J-set transference argument cited in Fact 3.1 of the preceding paper.
- Neil Hindman, Dona Strauss, and Luca Q. Zamboni, *Combining extensions of the Hales-Jewett
  Theorem with Ramsey Theory in other structures*, Electronic Journal of Combinatorics
  **26** (2019), no. 4, Article P4.23, Corollary 16 (the fixed-alphabet pattern result).

The proof of Corollary 3.8 reuses `exists_variableWords_prod_mem_of_isCSet_aux` and shares the
one-stage count construction and index pairing with
`exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet`, both in this module.
-/

namespace MetaMathlibExt

namespace VariableWordPattern

variable {α : Type*} {k n : ℕ}

private abbrev letters (w : FreeSemigroup (α ⊕ Fin n)) := w.head :: w.tail

private theorem letters_mul (u v : FreeSemigroup (α ⊕ Fin n)) :
    letters (u * v) = letters u ++ letters v := rfl

private abbrev embed : FreeSemigroup α →ₙ* FreeSemigroup (α ⊕ Fin n) := FreeSemigroup.map Sum.inl

-- Interleave the coefficient words from a J-set witness with the selected variable words.
private def interleave {r : ℕ} (b : Fin (r + 2) → FreeSemigroup α)
    (v : Fin (r + 1) → FreeSemigroup (α ⊕ Fin n)) :=
  (List.ofFn fun j : Fin r => embed (b j.succ.castSucc) * v j.succ).foldl (· * ·)
    (embed (b 0) * v 0) * embed (b (Fin.last (r + 1)))

private theorem mem_interleave {r : ℕ} (b : Fin (r + 2) → FreeSemigroup α)
    (v : Fin (r + 1) → FreeSemigroup (α ⊕ Fin n)) {x} (hx : x ∈ letters (v 0)) :
    x ∈ letters (interleave b v) := by
  rw [interleave, letters_mul]
  apply List.mem_append_left
  apply List.foldlRecOn (motive := fun u => x ∈ letters u) _ (· * ·)
  · rw [letters_mul]
    exact List.mem_append_right _ hx
  · intro u hu w _
    rw [letters_mul]
    exact List.mem_append_left _ hu

private theorem exists_interleave (A : ℕ → Finset α) (hA : Monotone A)
    (hcover : ∀ x, ∃ i, x ∈ A i) (c : α) (m : ℕ) (block : ℕ → FreeSemigroup (α ⊕ Fin n))
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ (r : ℕ) (b : Fin (r + 2) → FreeSemigroup α) (t : Fin (r + 1) → ℕ), StrictMono t ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) →
        FreeSemigroup.map (Sum.elim id a) (interleave b (block ∘ t)) ∈ D := by
  classical
  obtain ⟨q, hq⟩ := hcover c
  -- Enlarge the level to include c, so the family of substitutions is nonempty.
  let tuples := Fintype.piFinset fun _ : Fin n => A (max m q)
  have htuples : tuples.Nonempty :=
    ⟨fun _ => c, Fintype.mem_piFinset.mpr fun _ => hA (le_max_right _ _) hq⟩
  let subst (a : Fin n → α) := FreeSemigroup.map (Sum.elim id a)
  let seq (a : Fin n → α) (j : ℕ) := subst a (block j)
  obtain ⟨r, b, t, ht, hb⟩ := hD (tuples.image seq) (htuples.image seq)
  refine ⟨r, b, t, ht, fun a ha => ?_⟩
  have hfix (u : FreeSemigroup α) : subst a (embed u) = u := by
    induction u with simp [subst, embed, *]
  have hfold (xs : List (FreeSemigroup (α ⊕ Fin n))) (u) :
      subst a (xs.foldl (· * ·) u) = (xs.map (subst a)).foldl (· * ·) (subst a u) := by
    rw [List.foldl_map]
    exact (List.foldl_hom (subst a) fun x y => (map_mul (subst a) x y).symm).symm
  have ha' : a ∈ tuples := Fintype.mem_piFinset.mpr fun i => hA (le_max_left _ _) (ha i)
  change subst a _ ∈ D
  simpa only [interleave, map_mul, hfold, List.map_ofFn, Function.comp_def, hfix, seq] using
    hb (seq a) (Finset.mem_image_of_mem seq ha')

end VariableWordPattern

open VariableWordPattern

-- The free semigroup homomorphism maps the head and tail letter by letter.
private theorem VariableWordPattern.map_mk {α β : Type*} (f : α → β) (c : α) (cs : List α) :
    FreeSemigroup.map f ⟨c, cs⟩ = ⟨f c, cs.map f⟩ := by
  induction cs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    change FreeSemigroup.map f (FreeSemigroup.of c * ⟨b, bs⟩) = _
    rw [map_mul, FreeSemigroup.map_of, ih]
    rfl

/-- **Piecewise syndetic sets contain Hales–Jewett configurations.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is piecewise syndetic, then for all $m, n \in \mathbb{N}$ there is an
$n$-variable word $w$ over $A$ with $w(\vec a) \in D$ for every $\vec a \in A_m^n$.

For $n = 0$ the claim is that $D$ is nonempty.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.3. -/
public theorem exists_variableWord_subst_mem_of_isMulPiecewiseSyndetic {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulPiecewiseSyndetic D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  classical
  obtain ⟨G, hG⟩ := hD
  obtain ⟨seed, _⟩ := hG ∅
  obtain ⟨q, hq⟩ := hcover seed.head
  let B := A (max m q)
  let c : B := ⟨seed.head, hA (le_max_right m q) hq⟩
  obtain ⟨N, hN⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin B G (Fin n)
  -- Give each cube point a fixed first letter, so its word is nonempty even when N = 0.
  let word (v : Fin N → B) : FreeSemigroup α := ⟨c, List.ofFn fun j => (v j).val⟩
  obtain ⟨x, hx⟩ := hG (Finset.univ.image word)
  have exists_prefix (v : Fin N → B) : ∃ t : G, t.val * (word v * x) ∈ D := by
    obtain ⟨t, ht, hmem⟩ := hx (word v) (Finset.mem_image_of_mem word (Finset.mem_univ v))
    exact ⟨⟨t, ht⟩, hmem⟩
  choose color hcolor using exists_prefix
  -- On the monochromatic subspace one prefix works for all substitutions.
  obtain ⟨l, t, ht⟩ := hN color
  let letter (j : Fin N) : α ⊕ Fin n := (l.idxFun j).map Subtype.val id
  let middle : FreeSemigroup (α ⊕ Fin n) := ⟨Sum.inl c.val, List.ofFn letter⟩
  refine ⟨embed t.val * (middle * embed x), ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := l.proper i
    change Sum.inr i ∈ letters (embed t.val * (middle * embed x))
    rw [letters_mul]
    apply List.mem_append_right
    rw [letters_mul]
    exact List.mem_append_left _ (.tail _ (List.mem_ofFn.mpr ⟨j, by simp [letter, hj]⟩))
  · intro a ha
    let b (i : Fin n) : B := ⟨a i, hA (le_max_left m q) (ha i)⟩
    have hletter (j : Fin N) : (Sum.elim id a) (letter j) = (l b j).val := by
      cases hj : l.idxFun j <;> simp [letter, Combinatorics.Subspace.apply_def, hj, b]
    have hmiddle : FreeSemigroup.map (Sum.elim id a) middle = word (l b) := by
      simp [middle, map_mk, List.map_ofFn, Function.comp_def, hletter, word]
    have hfix (u : FreeSemigroup α) : FreeSemigroup.map (Sum.elim id a) (embed u) = u := by
      induction u with simp [embed, *]
    simpa only [map_mul, hfix, hmiddle, ht b] using hcolor (l b)

/-- **J-sets contain Hales–Jewett configurations.** Let $A_0 \subseteq A_1 \subseteq \cdots$ be
finite sets whose union $A$ is nonempty, and let $S_0$ be the semigroup of nonempty finite words
over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable word over $A$ is a nonempty
finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which
every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$
is obtained from $w$ by replacing each $v_i$ by $a_i$. If $D \subseteq S_0$ is a $J$-set, then
for all $m, n \in \mathbb{N}$ there is an $n$-variable word $w$ over $A$ with $w(\vec a) \in D$
for every $\vec a \in A_m^n$.

The alphabet must be nonempty: over the empty alphabet every subset of $S_0 = \emptyset$ is
vacuously a $J$-set, and there is no $0$-variable word.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Lemma 3.4. -/
public theorem exists_variableWord_subst_mem_of_isMulJSet {α : Type*} [Nonempty α]
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (m n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
      ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  obtain ⟨c⟩ := ‹Nonempty α›
  let block : FreeSemigroup (α ⊕ Fin n) := ⟨Sum.inl c, List.ofFn Sum.inr⟩
  obtain ⟨r, b, t, _, hmem⟩ := exists_interleave A hA hcover c m (fun _ => block) hD
  exact ⟨interleave b (fun _ => block),
    fun i => mem_interleave b _ (.tail _ (List.mem_ofFn.mpr ⟨i, rfl⟩)), hmem⟩

namespace VariableWordPattern

variable {α : Type*} {k n : ℕ}

private def project (k : ℕ) : α ⊕ Fin n → Option (Fin k) :=
  Sum.elim (fun _ => none) fun i => if h : (i : ℕ) < k then some ⟨i, h⟩ else none

private abbrev pattern (k : ℕ) (w : FreeSemigroup (α ⊕ Fin n)) :=
  (letters w).filterMap (project k)

private theorem pattern_mul (u v : FreeSemigroup (α ⊕ Fin n)) :
    pattern k (u * v) = pattern k u ++ pattern k v := by
  simp only [pattern, letters_mul, List.filterMap_append]

-- Lift a prescribed pattern to the first k variables and append the missing high variables.
private theorem exists_word (hk : 1 ≤ k) (hkn : k ≤ n)
    (p : List (Fin k)) (hp : ∀ i, i ∈ p) :
    ∃ w : FreeSemigroup (α ⊕ Fin n), (∀ i, Sum.inr i ∈ letters w) ∧ pattern k w = p := by
  let low (i : Fin k) : α ⊕ Fin n := Sum.inr (i.castLE hkn)
  let high := (List.finRange n).filter fun i : Fin n => k ≤ i.val
  let xs := p.map low ++ high.map (Sum.inr : Fin n → α ⊕ Fin n)
  have hvars (i : Fin n) : Sum.inr i ∈ xs := by
    by_cases hi : (i : ℕ) < k
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨i, hi⟩, hp _, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr
        ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true (by omega)⟩, rfl⟩)
  have hlow : project (α := α) k ∘ low = some := by
    funext i
    simp [project, low, i.isLt]
  have hhigh : (high.map (Sum.inr : Fin n → α ⊕ Fin n)).filterMap (project k) = [] := by
    rw [List.filterMap_map, List.filterMap_eq_nil_iff]
    intro i hi
    have h : k ≤ i.val := of_decide_eq_true (List.mem_filter.mp hi).2
    simp [project, h.not_gt]
  have hpat : xs.filterMap (project k) = p := by
    dsimp only [xs]
    rw [List.filterMap_append, hhigh, List.filterMap_map, hlow, List.filterMap_some,
      List.append_nil]
  cases he : xs with
  | nil => simpa [he] using hvars ⟨0, by omega⟩
  | cons x rest =>
    rw [he] at hvars hpat
    exact ⟨⟨x, rest⟩, hvars, hpat⟩

private theorem pattern_fold (xs : List (FreeSemigroup (α ⊕ Fin n))) (u) :
    pattern k (xs.foldl (· * ·) u) = pattern k u ++ xs.flatMap (pattern k) := by
  induction xs generalizing u with
  | nil => simp
  | cons v xs ih => simp [ih, pattern_mul, List.append_assoc]

private theorem pattern_interleave {r : ℕ} (b : Fin (r + 2) → FreeSemigroup α)
    (v : Fin (r + 1) → FreeSemigroup (α ⊕ Fin n)) :
    pattern k (interleave b v) = (List.ofFn fun j => pattern k (v j)).flatten := by
  have hconst (u : FreeSemigroup α) : pattern k (embed (n := n) u) = [] := by
    induction u with
    | ih1 x => rfl
    | ih2 x w hx ih => rw [map_mul, pattern_mul, hx, ih, List.nil_append]
  rw [interleave, pattern_mul, hconst, List.append_nil, pattern_fold, List.flatMap_def,
    List.map_ofFn, List.ofFn_succ (f := fun j => pattern k (v j))]
  simp only [Function.comp_def, pattern_mul, hconst, List.nil_append, List.flatten_cons]

-- Realize one level using only indices in the tail starting at s.
private theorem exists_stage (A : ℕ → Finset α) (hA : Monotone A)
    (hcover : ∀ x, ∃ i, x ∈ A i) (hk : 1 ≤ k) (hkn : k ≤ n)
    (y : ℕ → List (Fin k)) (hy : ∀ t i, i ∈ y t) {D : Set (FreeSemigroup α)}
    (hD : IsMulJSet D) (m s : ℕ) :
    ∃ (w : FreeSemigroup (α ⊕ Fin n)) (r : ℕ) (t : Fin (r + 1) → ℕ),
      StrictMono t ∧ s ≤ t 0 ∧ (∀ i, Sum.inr i ∈ letters w) ∧
      (∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D) ∧
      pattern k w = (List.ofFn fun j => y (t j)).flatten := by
  classical
  choose block hvars hpat using fun j => exists_word (α := α) hk hkn (y j) (hy j)
  by_cases hα : Nonempty α
  · obtain ⟨c⟩ := hα
    obtain ⟨r, b, t, ht, hmem⟩ :=
      exists_interleave A hA hcover c m (fun j => block (s + j)) hD
    let v (j : Fin (r + 1)) := block (s + t j)
    refine ⟨interleave b v, r, fun j => s + t j, fun _ _ h => Nat.add_lt_add_left (ht h) _,
      Nat.le_add_right _ _, fun i => mem_interleave b v (hvars _ i), hmem, ?_⟩
    simp only [pattern_interleave, v, hpat]
  · refine ⟨block s, 0, fun _ => s, Fin.strictMono_iff_lt_succ.mpr (fun i => i.elim0),
      le_rfl, hvars s,
      fun a _ => (hα ⟨a ⟨0, by omega⟩⟩).elim, ?_⟩
    simpa [List.ofFn_succ] using hpat s

-- Concatenate the nonempty index blocks of an increasing sequence of stages.
private theorem exists_ordered_pattern_product (y : ℕ → List (Fin k))
    (w : ℕ → FreeSemigroup (α ⊕ Fin n)) (start r : ℕ → ℕ) (t : ∀ m, Fin (r m + 1) → ℕ)
    (ht : ∀ m, StrictMono (t m)) (hstart : ∀ m, start m ≤ t m 0)
    (hend : ∀ m, t m (Fin.last (r m)) < start (m + 1))
    (hpat : ∀ m, pattern k (w m) = (List.ofFn fun j => y (t m j)).flatten)
    {l : ℕ} (m : Fin (l + 1) → ℕ) (hm : StrictMono m) :
    ∃ (r' : ℕ) (t' : Fin (r' + 1) → ℕ), StrictMono t' ∧
      (List.ofFn fun j => pattern k (w (m j))).flatten = (List.ofFn fun j => y (t' j)).flatten := by
  let indices (i : ℕ) := List.ofFn (t i)
  have hbounds {i a} (ha : a ∈ indices i) : start i ≤ a ∧ a < start (i + 1) := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨(hstart i).trans ((ht i).monotone (Fin.zero_le j)),
      ((ht i).monotone (Fin.le_last j)).trans_lt (hend i)⟩
  have hmono : Monotone start := monotone_nat_of_le_succ fun i => by
    have h := hbounds (i := i) (List.mem_ofFn.mpr ⟨0, rfl⟩)
    exact h.1.trans h.2.le
  let chunks := List.ofFn fun j => indices (m j)
  have hsorted : chunks.flatten.Pairwise (· < ·) := by
    apply List.pairwise_flatten.mpr
    constructor
    · exact List.forall_mem_ofFn_iff.mpr fun j => List.pairwise_ofFn.mpr (ht (m j))
    · apply List.pairwise_ofFn.mpr
      intro i j hij a ha b hb
      exact (hbounds ha).2.trans_le
        ((hmono (Nat.succ_le_of_lt (hm hij))).trans (hbounds hb).1)
  have hne : chunks.flatten ≠ [] := by
    intro he
    have h := List.flatten_eq_nil_iff.mp he _ (List.mem_ofFn.mpr ⟨0, rfl⟩)
    simp [indices] at h
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  rw [he] at hsorted
  refine ⟨as.length, (a :: as).get, fun _ _ hij => List.pairwise_iff_get.mp hsorted _ _ hij, ?_⟩
  change (List.ofFn fun j => pattern k (w (m j))).flatten =
    (List.ofFn (y ∘ (a :: as).get)).flatten
  rw [← List.map_ofFn, List.ofFn_get, ← he]
  simp only [chunks, indices, List.map_flatten, List.flatten_flatten, List.map_ofFn,
    Function.comp_def, hpat]

end VariableWordPattern

/-- **Variable patterns of variable words in J-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. Let $1 \le k < n$. An $n$-variable word over $A$ is a nonempty finite word
over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which every $v_i$
occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$ is obtained
from $w$ by replacing each $v_i$ by $a_i$, and $\tau(w)$ is the word over
$\{v_0, \dots, v_{k-1}\}$ obtained from $w$ by deleting the letters of $A$ and the variables $v_i$
with $i \ge k$. Let $y_0, y_1, \dots$ be finite words over $\{v_0, \dots, v_{k-1}\}$ in each of
which every $v_i$ with $i < k$ occurs. If $D \subseteq S_0$ is a $J$-set, then there is a
sequence $w_0, w_1, \dots$ of $n$-variable words over $A$ such that $w_m(\vec a) \in D$ for all
$m \in \mathbb{N}$ and $\vec a \in A_m^n$, and such that for all $l \in \mathbb{N}$ and
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ there are $r \in \mathbb{N}$ and
$t_0 < t_1 < \cdots < t_r$ in $\mathbb{N}$ with
$\tau(w_{m_0}) \tau(w_{m_1}) \cdots \tau(w_{m_l}) = y_{t_0} y_{t_1} \cdots y_{t_r}$, where
juxtaposition is concatenation of words.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.9. -/
public theorem exists_variableWords_subst_mem_prod_pattern_mem_finiteProducts_of_isMulJSet
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
            (List.ofFn fun j => y (t j)).flatten := by
  classical
  choose word r t ht hstart hvars hmem hpat using exists_stage A hA hcover hk hkn.le y hy hD
  -- Start each search strictly after the last index used by the preceding stage.
  let start : ℕ → ℕ := Nat.rec 0 fun m s => t m s (Fin.last (r m s)) + 1
  refine ⟨fun m => word m (start m), fun m => hvars m _, fun m => hmem m _, ?_⟩
  intro l m hm
  exact exists_ordered_pattern_product y _ start (fun m => r m (start m)) (fun m => t m (start m))
    (fun m => ht m _) (fun m => hstart m _) (fun _ => Nat.lt_succ_self _) (fun m => hpat m _) m hm

private theorem exists_count_stage {α : Type*} (A : ℕ → Finset α) (hA : Monotone A)
    (hcover : ∀ x, ∃ i, x ∈ A i) {D : Set (FreeSemigroup α)} (hD : IsMulJSet D)
    (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) (m : ℕ) :
    ∃ w : FreeSemigroup (α ⊕ Fin 1),
      (∃ H : Finset ℕ, H.Nonempty ∧ (letters w).countP Sum.isRight = ∑ j ∈ H, x j) ∧
      (∀ i, Sum.inr i ∈ letters w) ∧
      ∀ a : Fin 1 → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ D := by
  let runs (j : ℕ) := List.replicate (x j) (0 : Fin 1)
  have hruns (j : ℕ) (i : Fin 1) : i ∈ runs j :=
    List.mem_replicate.mpr ⟨(hx _).ne', Subsingleton.elim _ _⟩
  obtain ⟨w, r, t, ht, _, hvars, hmem, hpat⟩ :=
    exists_stage A hA hcover (k := 1) (n := 1) le_rfl le_rfl runs hruns hD m 0
  refine ⟨w, ⟨Finset.univ.image t, Finset.univ_nonempty.image t, ?_⟩, hvars, hmem⟩
  have hright : (fun a : α ⊕ Fin 1 => (project 1 a).isSome) = Sum.isRight := by
    funext a
    cases a <;> simp [project]
  rw [Finset.sum_image ht.injective.injOn]
  simpa only [pattern, List.length_filterMap_eq_countP, hright, List.length_flatten,
    List.map_ofFn, Function.comp_def, runs, List.length_replicate, List.sum_ofFn] using
    congrArg List.length hpat

-- Pair the level and its local input index so that the sum never reuses an input index.
private theorem exists_sum_eq_of_pair_blocks (x c : ℕ → ℕ)
    (hblocks : ∀ m, ∃ H : Finset ℕ, H.Nonempty ∧ c m = ∑ j ∈ H, x (Nat.pair m j))
    (G : Finset ℕ) (hG : G.Nonempty) :
    ∃ H : Finset ℕ, H.Nonempty ∧ ∑ m ∈ G, c m = ∑ j ∈ H, x j := by
  classical
  choose block hne hsum using hblocks
  let pair := ((Equiv.sigmaEquivProd ℕ ℕ).trans Nat.pairEquiv).toEmbedding
  obtain ⟨m, hm⟩ := hG
  refine ⟨(G.sigma block).map pair, (Finset.sigma_nonempty.mpr ⟨m, hm, hne m⟩).map, ?_⟩
  rw [Finset.sum_map, Finset.sum_sigma]
  exact Finset.sum_congr rfl fun m _ => hsum m

/-- **Variable-count sums of variable words in J-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. A variable word over $A$ is a nonempty finite word over $A \cup \{v\}$, for a
variable $v \notin A$, in which $v$ occurs; for $a \in A$, the word $w(a) \in S_0$ is obtained from
$w$ by replacing each occurrence of $v$ by $a$, and $|w|_v$ is the number of occurrences of $v$ in
$w$. If $D \subseteq S_0$ is a $J$-set and $x_0, x_1, \dots$ are positive integers, then there is
a sequence $w_0, w_1, \dots$ of variable words over $A$ such that $w_k(a) \in D$ for all
$k \in \mathbb{N}$ and $a \in A_k$, and such that for every nonempty finite $G \subseteq \mathbb{N}$
there is a nonempty finite $H \subseteq \mathbb{N}$ with
$\sum_{k \in G} |w_k|_v = \sum_{j \in H} x_j$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Theorem 3.7. -/
public theorem exists_variableWords_subst_mem_sum_count_mem_finiteSums_of_isMulJSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsMulJSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ k a, a ∈ A k → FreeSemigroup.map (Sum.elim id fun _ => a) (w k) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j := by
  choose w hw using fun m => exists_count_stage A hA hcover hD (fun j => x (Nat.pair m j))
    (fun j => hx (Nat.pair m j)) m
  exact ⟨w, fun m => (hw m).2.1 0, fun m a ha => (hw m).2.2 (fun _ => a) (fun _ => ha),
    exists_sum_eq_of_pair_blocks x _ (fun m => (hw m).1)⟩

-- If each factor sends the next set into the current one by left multiplication,
-- then a product along any increasing subsequence belongs to its first set.
private theorem foldl_mem_of_left_mul {S : Type*} [Semigroup S] {B : ℕ → Set S}
    (hB : Antitone B) {l : ℕ} (m : Fin (l + 1) → ℕ) (x : Fin (l + 1) → S)
    (hm : StrictMono m) (hx : ∀ j, x j ∈ B (m j) ∧ ∀ y ∈ B (m j + 1), x j * y ∈ B (m j)) :
    (List.ofFn fun j : Fin l => x j.succ).foldl (· * ·) (x 0) ∈ B (m 0) := by
  induction l with
  | zero => simpa using (hx 0).1
  | succ l ih =>
    rw [List.ofFn_succ, List.foldl_cons, List.foldl_assoc]
    apply (hx 0).2
    have hlt : m 0 < m (0 : Fin (l + 1)).succ := hm (Nat.zero_lt_succ _)
    exact hB hlt
      (ih (m ∘ Fin.succ) (x ∘ Fin.succ) (hm.comp Fin.strictMono_succ) fun j => hx j.succ)

-- A J-set stage can carry auxiliary state independently of the decreasing ultrafilter sets.
private theorem exists_variableWords_prod_mem_of_isCSet_aux {α σ : Type*} {n : ℕ}
    (A : ℕ → Finset α) {D : Set (FreeSemigroup α)} (hD : IsCSet D) (initial : σ)
    (P : ℕ → σ → σ → FreeSemigroup (α ⊕ Fin n) → Prop)
    (stage : ∀ (m : ℕ) (s : σ) (B : Set (FreeSemigroup α)), IsMulJSet B →
      ∃ (w : FreeSemigroup (α ⊕ Fin n)) (t : σ), P m s t w ∧
        (∀ i, Sum.inr i ∈ letters w) ∧
        ∀ a : Fin n → α, (∀ i, a i ∈ A m) → FreeSemigroup.map (Sum.elim id a) w ∈ B) :
    ∃ (w : ℕ → FreeSemigroup (α ⊕ Fin n)) (s : ℕ → σ),
      (∀ m, P m (s m) (s (m + 1)) (w m)) ∧ (∀ m i, Sum.inr i ∈ letters (w m)) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D := by
  classical
  let := Ultrafilter.semigroup (M := FreeSemigroup α)
  obtain ⟨p, hid, hJ, hD⟩ := hD
  let State := {B : Set (FreeSemigroup α) // B ∈ p} × σ
  let eval (w : FreeSemigroup (α ⊕ Fin n)) (a : Fin n → α) :=
    FreeSemigroup.map (Sum.elim id a) w
  -- Choose the word inside a large set and reserve a large set for every possible tail.
  have step (m : ℕ) (s : State) :
      ∃ (w : FreeSemigroup (α ⊕ Fin n)) (t : State),
        t.1.val ⊆ s.1.val ∧ P m s.2 t.2 w ∧ (∀ i, Sum.inr i ∈ letters w) ∧
        ∀ a : Fin n → α, (∀ i, a i ∈ A m) →
          eval w a ∈ s.1.val ∧ ∀ y ∈ t.1.val, eval w a * y ∈ s.1.val := by
    let good := s.1.val ∩ {x | {y | x * y ∈ s.1.val} ∈ p}
    have hgood : good ∈ p :=
      Filter.inter_mem s.1.property (show s.1.val ∈ p * p by
        simpa only [hid] using s.1.property)
    obtain ⟨w, t, hP, hvar, hw⟩ := stage m s.2 good (hJ good hgood)
    let tuples := Fintype.piFinset fun _ : Fin n => A m
    let tails := {y | ∀ a ∈ tuples, eval w a * y ∈ s.1.val}
    have ht : tails ∈ p :=
      (Filter.eventually_all_finset tuples).2 fun a ha => (hw a (Fintype.mem_piFinset.mp ha)).2
    refine ⟨w, (⟨s.1.val ∩ tails, Filter.inter_mem s.1.property ht⟩, t), Set.inter_subset_left,
      hP, hvar, fun a ha => ⟨(hw a ha).1, fun y hy => ?_⟩⟩
    exact hy.2 a (Fintype.mem_piFinset.mpr ha)
  choose word next hsub hP hvars hmem using step
  let states : ℕ → State := Nat.rec (⟨D, hD⟩, initial) next
  have hanti : Antitone (fun m => (states m).1.val) :=
    antitone_nat_of_succ_le fun m => hsub m (states m)
  refine ⟨fun m => word m (states m), fun m => (states m).2, fun m => hP m (states m),
    fun m => hvars m _, fun l m a hm ha => ?_⟩
  apply hanti (Nat.zero_le (m 0))
  exact foldl_mem_of_left_mul hanti m (fun j => eval (word (m j) (states (m j))) (a j)) hm
    fun j => hmem (m j) (states (m j)) (a j) (ha j)

/-- **Infinitary Hales–Jewett configurations in C-sets.** Let
$A_0 \subseteq A_1 \subseteq \cdots$ be finite sets with union $A$, and let $S_0$ be the semigroup
of nonempty finite words over $A$ under concatenation. For $n \in \mathbb{N}$, an $n$-variable
word over $A$ is a nonempty finite word over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct
variables $v_i \notin A$, in which every $v_i$ occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in
$A^n$, the word $w(\vec a) \in S_0$ is obtained from $w$ by replacing each $v_i$ by $a_i$. If
$D \subseteq S_0$ is a $C$-set, then for every $n \in \mathbb{N}$ there is a sequence
$w_0, w_1, \dots$ of $n$-variable words over $A$ such that
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l) \in D$ for all $l \in \mathbb{N}$,
all $m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $\vec a_j \in A_{m_j}^n$,
$j = 0, \dots, l$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.6. -/
public theorem exists_variableWords_prod_mem_of_isCSet {α : Type*}
    (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i) (n : ℕ)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin n), (∀ k i, Sum.inr i ∈ (w k).head :: (w k).tail) ∧
      ∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → Fin n → α), StrictMono m →
        (∀ j i, a j i ∈ A (m j)) →
        (List.ofFn fun j : Fin l => FreeSemigroup.map (Sum.elim id (a j.succ)) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id (a 0)) (w (m 0))) ∈ D := by
  have hα : Nonempty α := by
    obtain ⟨p, _, _, hmem⟩ := hD
    exact ⟨(Ultrafilter.nonempty_of_mem hmem).some.head⟩
  obtain ⟨w, _, _, hvars, hmem⟩ := exists_variableWords_prod_mem_of_isCSet_aux A hD ()
    (fun _ _ _ _ => True) (n := n) (by
      intro m _ B hB
      obtain ⟨w, hvars, hmem⟩ := exists_variableWord_subst_mem_of_isMulJSet A hA hcover m n hB
      exact ⟨w, (), trivial, hvars, hmem⟩)
  exact ⟨w, hvars, hmem⟩

/-- **Variable patterns of variable words in C-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. Let $1 \le k < n$. An $n$-variable word over $A$ is a nonempty finite word
over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which every $v_i$
occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$ is obtained
from $w$ by replacing each $v_i$ by $a_i$, and $\tau(w)$ is the word over
$\{v_0, \dots, v_{k-1}\}$ obtained from $w$ by deleting the letters of $A$ and the variables $v_i$
with $i \ge k$. Let $y_0, y_1, \dots$ be finite words over $\{v_0, \dots, v_{k-1}\}$ in each of
which every $v_i$ with $i < k$ occurs. If $C \subseteq S_0$ is a $C$-set, then there is a
sequence $w_0, w_1, \dots$ of $n$-variable words over $A$ such that for all $l \in \mathbb{N}$ and
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$, the word
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l)$ lies in $C$ for all
$\vec a_j \in A_{m_j}^n$, $j = 0, \dots, l$, and there are $r \in \mathbb{N}$ and
$t_0 < t_1 < \cdots < t_r$ in $\mathbb{N}$ with
$\tau(w_{m_0}) \tau(w_{m_1}) \cdots \tau(w_{m_l}) = y_{t_0} y_{t_1} \cdots y_{t_r}$, where
juxtaposition is concatenation of words.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.10. -/
public theorem exists_variableWords_prod_mem_prod_pattern_mem_finiteProducts_of_isCSet
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
            (List.ofFn fun j => y (t j)).flatten := by
  classical
  -- The auxiliary state bounds the input indices from below, independently of substitutions.
  let P (s next : ℕ) (w : FreeSemigroup (α ⊕ Fin n)) : Prop :=
    ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧ s ≤ t 0 ∧
      t (Fin.last r) < next ∧ pattern k w = (List.ofFn fun j => y (t j)).flatten
  obtain ⟨w, start, hblocks, hvars, hmem⟩ :=
    exists_variableWords_prod_mem_of_isCSet_aux A hC 0 (fun _ => P) (by
      intro m s B hB
      obtain ⟨w, r, t, ht, hs, hvars, hmem, hpat⟩ := exists_stage A hA hcover hk hkn.le y hy hB m s
      exact ⟨w, t (Fin.last r) + 1, ⟨r, t, ht, hs, Nat.lt_succ_self _, hpat⟩, hvars, hmem⟩)
  change ∀ m, ∃ (r : ℕ) (t : Fin (r + 1) → ℕ), StrictMono t ∧ start m ≤ t 0 ∧
    t (Fin.last r) < start (m + 1) ∧ pattern k (w m) = (List.ofFn fun j => y (t j)).flatten
    at hblocks
  choose r t ht hstart hend hpat using hblocks
  exact ⟨w, hvars, fun l m hm => ⟨fun a => hmem l m a hm,
    exists_ordered_pattern_product y w start r t ht hstart hend hpat m hm⟩⟩

/-- **Variable-count sums of variable words in C-sets.** Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. A variable word over $A$ is a nonempty finite word over $A \cup \{v\}$, for a
variable $v \notin A$, in which $v$ occurs; for $a \in A$, the word $w(a) \in S_0$ is obtained from
$w$ by replacing each occurrence of $v$ by $a$, and $|w|_v$ is the number of occurrences of $v$ in
$w$. If $D \subseteq S_0$ is a $C$-set and $x_0, x_1, \dots$ are positive integers, then there is
a sequence $w_0, w_1, \dots$ of variable words over $A$ such that
$w_{m_0}(a_0) w_{m_1}(a_1) \cdots w_{m_l}(a_l) \in D$ for all $l \in \mathbb{N}$, all
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $a_j \in A_{m_j}$, $j = 0, \dots, l$, and such
that for every nonempty finite $G \subseteq \mathbb{N}$ there is a nonempty finite
$H \subseteq \mathbb{N}$ with $\sum_{k \in G} |w_k|_v = \sum_{j \in H} x_j$.

Source: Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett
Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.8. -/
public theorem exists_variableWords_prod_mem_sum_count_mem_finiteSums_of_isCSet
    {α : Type*} (A : ℕ → Finset α) (hA : Monotone A) (hcover : ∀ x, ∃ i, x ∈ A i)
    {D : Set (FreeSemigroup α)} (hD : IsCSet D) (x : ℕ → ℕ) (hx : ∀ j, 0 < x j) :
    ∃ w : ℕ → FreeSemigroup (α ⊕ Fin 1), (∀ k, Sum.inr 0 ∈ (w k).head :: (w k).tail) ∧
      (∀ (l : ℕ) (m : Fin (l + 1) → ℕ) (a : Fin (l + 1) → α), StrictMono m →
        (∀ j, a j ∈ A (m j)) →
        (List.ofFn fun j : Fin l =>
            FreeSemigroup.map (Sum.elim id fun _ => a j.succ) (w (m j.succ))).foldl
          (· * ·) (FreeSemigroup.map (Sum.elim id fun _ => a 0) (w (m 0))) ∈ D) ∧
      ∀ G : Finset ℕ, G.Nonempty → ∃ H : Finset ℕ, H.Nonempty ∧
        ∑ k ∈ G, ((w k).head :: (w k).tail).countP Sum.isRight = ∑ j ∈ H, x j := by
  let P (m : ℕ) (w : FreeSemigroup (α ⊕ Fin 1)) : Prop :=
    ∃ H : Finset ℕ, H.Nonempty ∧ (letters w).countP Sum.isRight = ∑ j ∈ H, x (Nat.pair m j)
  obtain ⟨w, _, hblocks, hvars, hmem⟩ :=
    exists_variableWords_prod_mem_of_isCSet_aux A hD () (fun m _ _ => P m) (by
      intro m _ B hB
      obtain ⟨w, hcount, hvars, hmem⟩ :=
        exists_count_stage A hA hcover hB (fun j => x (Nat.pair m j)) (fun j => hx (Nat.pair m j)) m
      exact ⟨w, (), hcount, hvars, hmem⟩)
  exact ⟨w, fun m => hvars m 0, fun l m a hm ha => hmem l m (fun j _ => a j) hm (fun j _ => ha j),
    exists_sum_eq_of_pair_blocks x _ hblocks⟩

end MetaMathlibExt
