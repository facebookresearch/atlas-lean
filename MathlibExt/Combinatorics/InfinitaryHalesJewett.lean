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
  let indices (m : ℕ) := List.ofFn (t m (start m))
  have hbounds {m a} (ha : a ∈ indices m) : start m ≤ a ∧ a < start (m + 1) := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨(hstart m _).trans ((ht m _).monotone (Fin.zero_le j)),
      Nat.lt_succ_of_le ((ht m _).monotone (Fin.le_last j))⟩
  have hmono : Monotone start := monotone_nat_of_le_succ fun m => by
    have h := hbounds (m := m) (List.mem_ofFn.mpr ⟨0, rfl⟩)
    exact h.1.trans h.2.le
  refine ⟨fun m => word m (start m), fun m => hvars m _, fun m => hmem m _, ?_⟩
  intro l m hm
  let chunks := List.ofFn fun j => indices (m j)
  have hsorted : chunks.flatten.Pairwise (· < ·) := by
    apply List.pairwise_flatten.mpr
    constructor
    · exact List.forall_mem_ofFn_iff.mpr fun j => List.pairwise_ofFn.mpr (ht (m j) _)
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
  change (List.ofFn fun j => pattern k (word (m j) (start (m j)))).flatten =
    (List.ofFn (y ∘ (a :: as).get)).flatten
  rw [← List.map_ofFn, List.ofFn_get, ← he]
  simp only [chunks, indices, List.map_flatten, List.flatten_flatten, List.map_ofFn,
    Function.comp_def, hpat]

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
  classical
  -- Allocate disjoint input indices to the levels. At level m, the j-th pattern consists
  -- of x (Nat.pair m j) copies of the sole variable.
  let runs (m j : ℕ) := List.replicate (x (Nat.pair m j)) (0 : Fin 1)
  have hruns (m j : ℕ) (i : Fin 1) : i ∈ runs m j :=
    List.mem_replicate.mpr ⟨(hx _).ne', Subsingleton.elim _ _⟩
  choose w r t ht _ hvar hmem hpat using fun m =>
    exists_stage A hA hcover (k := 1) (n := 1) le_rfl le_rfl (runs m) (hruns m) hD m 0
  let index (m : ℕ) (j : Fin (r m + 1)) := Nat.pair m (t m j)
  let block (m : ℕ) := Finset.univ.image (index m)
  have hright : (fun a : α ⊕ Fin 1 => (project 1 a).isSome) = Sum.isRight := by
    funext a
    cases a <;> simp [project]
  have hcount (m : ℕ) : (letters (w m)).countP Sum.isRight = ∑ j ∈ block m, x j := by
    have hinj : Function.Injective (index m) :=
      fun _ _ h => (ht m).injective (Nat.pair_eq_pair.mp h).2
    rw [Finset.sum_image hinj.injOn]
    simpa only [pattern, List.length_filterMap_eq_countP, hright, List.length_flatten,
      List.map_ofFn, Function.comp_def, runs, List.length_replicate, List.sum_ofFn, index] using
      congrArg List.length (hpat m)
  refine ⟨w, fun m => hvar m 0, fun m a ha => hmem m (fun _ => a) (fun _ => ha), ?_⟩
  intro G hG
  refine ⟨G.biUnion block, Finset.biUnion_nonempty.mpr
    ⟨hG.choose, hG.choose_spec, Finset.univ_nonempty.image _⟩, ?_⟩
  have hdisjoint : (G : Set ℕ).PairwiseDisjoint block := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i', _, he⟩ := Finset.mem_image.mp hj'
    exact hab (Nat.pair_eq_pair.mp he.symm).1
  rw [Finset.sum_biUnion hdisjoint]
  exact Finset.sum_congr rfl fun m _ => hcount m

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
  classical
  let := Ultrafilter.semigroup (M := FreeSemigroup α)
  obtain ⟨p, hid, hJ, hD⟩ := hD
  have : Nonempty α := ⟨(Ultrafilter.nonempty_of_mem hD).some.head⟩
  let eval (w : FreeSemigroup (α ⊕ Fin n)) (a : Fin n → α) :=
    FreeSemigroup.map (Sum.elim id a) w
  -- Choose the word inside a large set and reserve a large set for every possible tail.
  have step (k : ℕ) (s : {B : Set (FreeSemigroup α) // B ∈ p}) :
      ∃ (w : FreeSemigroup (α ⊕ Fin n)) (t : {B : Set (FreeSemigroup α) // B ∈ p}),
        t.val ⊆ s.val ∧ (∀ i, Sum.inr i ∈ w.head :: w.tail) ∧
        ∀ a : Fin n → α, (∀ i, a i ∈ A k) →
          eval w a ∈ s.val ∧ ∀ y ∈ t.val, eval w a * y ∈ s.val := by
    let good := s.val ∩ {x | {y | x * y ∈ s.val} ∈ p}
    have hgood : good ∈ p :=
      Filter.inter_mem s.property (show s.val ∈ p * p by simpa only [hid] using s.property)
    obtain ⟨w, hvar, hw⟩ := exists_variableWord_subst_mem_of_isMulJSet A hA hcover k n
      (hJ good hgood)
    let tuples := Fintype.piFinset fun _ : Fin n => A k
    let tails := {y | ∀ a ∈ tuples, eval w a * y ∈ s.val}
    have ht : tails ∈ p :=
      (Filter.eventually_all_finset tuples).2 fun a ha => (hw a (Fintype.mem_piFinset.mp ha)).2
    refine ⟨w, ⟨s.val ∩ tails, Filter.inter_mem s.property ht⟩, Set.inter_subset_left,
      hvar, fun a ha => ⟨(hw a ha).1, fun y hy => ?_⟩⟩
    exact hy.2 a (Fintype.mem_piFinset.mpr ha)
  choose word next hsub hvars hmem using step
  let sets : ℕ → {B : Set (FreeSemigroup α) // B ∈ p} := Nat.rec ⟨D, hD⟩ next
  have hanti : Antitone (fun k => (sets k).val) :=
    antitone_nat_of_succ_le fun k => hsub k (sets k)
  refine ⟨fun k => word k (sets k), fun k => hvars k _, fun l m a hm ha => ?_⟩
  apply hanti (Nat.zero_le (m 0))
  exact foldl_mem_of_left_mul hanti m (fun j => eval (word (m j) (sets (m j))) (a j)) hm
    fun j => hmem (m j) (sets (m j)) (a j) (ha j)

end MetaMathlibExt
