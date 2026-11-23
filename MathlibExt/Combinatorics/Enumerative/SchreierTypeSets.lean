/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Sort

/-!
# Schreier-type sets and partitions

The number of partitions of `n` into parts greater than `l` is one more than the
number of refined Schreier sets with maximum `n + 1`.

For a partition with `k ≥ 2` parts, list its parts in decreasing order. Subtract `l`
from each part except the largest and repeat the first term of the resulting list.
These are the gaps of the set, read from largest vertex to smallest. Its minimum is
`l * k + 1` plus the difference between the two largest parts. The gap list and the
minimum thus recover the partition, leaving the one-part partition to account for the extra one.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Schreier sets.** A finite set $A$ of natural numbers is *Schreier* if $|A| \le a$ for
every $a \in A$; equivalently, $A$ is empty or $\min A \ge |A|$. -/
def IsSchreier (A : Finset ℕ) : Prop := ∀ a ∈ A, A.card ≤ a

instance instDecidableIsSchreier (A : Finset ℕ) : Decidable (IsSchreier A) := by
  unfold IsSchreier; infer_instance

/-- **Strong Schreier sets.** For a natural number $\ell$, a finite set $A$ of natural numbers is
*$\ell$-strong Schreier* if $\ell |A| + 1 \le a + \ell$ for every $a \in A$; equivalently, $A$ is
empty or $\min A \ge \ell |A| - \ell + 1$. -/
def IsStrongSchreier (l : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, l * A.card + 1 ≤ a + l

instance instDecidableIsStrongSchreier (l : ℕ) (A : Finset ℕ) :
    Decidable (IsStrongSchreier l A) := by
  unfold IsStrongSchreier; infer_instance

/-- **Sparse sets.** A finite set of natural numbers is *sparse* if the differences between
consecutive elements in increasing order are non-decreasing. -/
def IsSparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a ≤ c - b

instance instDecidableIsSparse (A : Finset ℕ) : Decidable (IsSparse A) := by
  unfold IsSparse; infer_instance

/-- **Strongly sparse sets.** A finite set of natural numbers is *strongly sparse* if the
differences between consecutive elements in increasing order are strictly increasing. -/
def IsStronglySparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a < c - b

instance instDecidableIsStronglySparse (A : Finset ℕ) : Decidable (IsStronglySparse A) := by
  unfold IsStronglySparse; infer_instance

/-- **Partitions into exactly $k$ parts.** For natural numbers $u$ and $k$, $p(u, k)$ is the
number of partitions of $u$ into exactly $k$ parts. -/
def partitionExactCount (u k : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Nat.Partition u =>
    P.parts.card = k)).card

/-- **The partition number $p(u)$.** For a natural number $u$, $p(u)$ is the number of partitions
of $u$, that is, of multisets of positive integers summing to $u$; in particular $p(0) = 1$. -/
def partitionCount (u : ℕ) : ℕ := Fintype.card (Nat.Partition u)

/-- **Number of Schreier sparse sets with given minimum and maximum.** For natural numbers $n$
and $m$, $|F_{n,m}|$ is the number of sets $F \subseteq \{1, \dots, n\}$ that are Schreier and
sparse, contain $n$, and have minimum $m$. -/
def schreierSparseMinCount (n m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F ∧ m ∈ F ∧ ∀ a ∈ F, m ≤ a)).card

/-- **Number of Schreier sparse sets with maximum $n$.** For a natural number $n$, $|F_n|$ is the
number of sets $F \subseteq \{1, \dots, n\}$ with $n \in F$ that are Schreier and sparse. -/
def schreierSparseCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F)).card

/-- **Number of sparse strong Schreier sets with maximum $n$.** For natural numbers $n$ and
$\ell$, $|A_{n,\ell}|$ is the number of sets $A \subseteq \{1, \dots, n\}$ with $n \in A$ that
are sparse and $\ell$-strong Schreier. -/
def sparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsSparse A ∧ IsStrongSchreier l A)).card

/-- **Number of strongly sparse strong Schreier sets with a given maximum.** For natural numbers
$n$ and $\ell$, $|A^s_{n,\ell}|$ is the number of sets $A \subseteq \{1, \dots, n\}$ with $n \in A$
that are strongly sparse, meaning that the differences between consecutive elements of $A$ in
increasing order are strictly increasing, and $\ell$-strong Schreier, meaning that every element
of $A$ is at least $\ell|A| - \ell + 1$. -/
def stronglySparseStrongCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => n ∈ A ∧
    IsStronglySparse A ∧ IsStrongSchreier l A)).card

/-- **Number of strong Schreier sets with a given maximum.** For natural numbers $n$ and $\ell$,
$|B_{n,\ell}|$ is the number of sets $B \subseteq \{1, \dots, n\}$ with $n \in B$ that are
$\ell$-strong Schreier, that is, every element of $B$ is at least $\ell|B| - \ell + 1$. -/
def strongSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    IsStrongSchreier l B)).card

/-- **Number of strong Schreier sets of given size with maximum $n$.** For natural numbers $n$,
$\ell$ and $m$, $|B_{n,\ell,m}|$ is the number of $\ell$-strong Schreier sets
$B \subseteq \{1, \dots, n\}$ with $n \in B$ and exactly $m$ elements. -/
def strongSchreierCardCount (n l m : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun B => n ∈ B ∧
    B.card = m ∧ IsStrongSchreier l B)).card

/-- **Partitions with all parts at least a given size.** For natural numbers $n$ and $\ell$,
$|E_{n,\ell}|$ is the number of partitions of $n$ all of whose parts are at least $\ell$. -/
def partitionMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x)).card

/-- **Partitions into distinct parts at least $\ell$.** For natural numbers $n$ and $\ell$, let
$E^d_{n,\ell}$ be the set of partitions of $n$ into pairwise distinct parts, each at least
$\ell$. This is its number of elements $|E^d_{n,\ell}|$. -/
def partitionDistinctMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x) ∩
    Nat.Partition.distincts n).card

/-- **Partitions with a given number of parts, all at least a given size.** For natural numbers
$n$, $\ell$ and $k$, $|E_{n,\ell,k}|$ is the number of partitions of $n$ into exactly $k$ parts,
all of which are at least $\ell$. -/
def partitionMinPartExactCount (n l k : ℕ) : ℕ :=
  ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k)).card

/-- **Partitions with a given gap between the two largest parts.** For natural numbers $n$,
$\ell$, $k$ and $q$, $|E_{n,\ell,k,q}|$ is the number of partitions of $n$ into exactly $k$ parts,
all at least $\ell$, whose largest part exceeds the second largest part (counted with
multiplicity) by exactly $q$; such a partition has at least two parts, so the count is $0$ for
$k < 2$. -/
noncomputable def partitionMinPartGapCount (n l k q : ℕ) : ℕ := by
  classical
  exact ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k ∧
      ∃ b : ℕ, ∃ rest : Multiset ℕ,
        P.parts = (b + q) ::ₘ b ::ₘ rest ∧
          ∀ x ∈ rest, x ≤ b)).card

/-- **Partitions avoiding parts from 2 up to a bound.** For natural numbers $n$ and $\ell$,
$|G_{n,\ell}|$ is the number of partitions of $n$ none of whose parts lies in
$\{2, \dots, \ell\}$. -/
def partitionNoSmallPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => ¬ (2 ≤ x ∧ x ≤ l))).card

/-- **Partitions avoiding parts from 2 up to a bound and large even parts.** For natural numbers
$n$ and $\ell$, $|H_{n,\ell}|$ is the number of partitions of $n$ none of whose parts lies in
$\{2, \dots, \ell\}$ and none of whose parts is an even number greater than $2\ell$. -/
def partitionNoSmallNoEvenCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n
    (fun x => ¬ (2 ≤ x ∧ x ≤ l) ∧ (Even x → x ≤ 2 * l))).card

/-- **Compositions with exactly $s$ parts, each at least $v$.** For natural numbers $u$, $v$
and $s$, $c(u, v, s)$ is the number of compositions of $u$ (ordered sequences of positive
integers summing to $u$) into exactly $s$ parts, each at least $v$. -/
def compositionMinPartExactCount (u v s : ℕ) : ℕ :=
  Fintype.card {c : Composition u //
    (∀ x ∈ c.blocks, v ≤ x) ∧ c.length = s}

/-- **Compositions with parts at least $v$.** For natural numbers $u$ and $v$, $c(u, v)$ is the
number of compositions of $u$ (ordered sequences of positive integers summing to $u$) all of
whose parts are at least $v$. -/
def compositionMinPartCount (u v : ℕ) : ℕ :=
  Fintype.card {c : Composition u // ∀ x ∈ c.blocks, v ≤ x}

/-- **The refined Schreier family $F_{n,\ell}$.** For natural numbers $n$ and $\ell$, a finite
set $A$ of natural numbers belongs to $F_{n,\ell}$ if $n + 1$ is the largest element of $A$,
$A$ has at least three elements, $A$ is sparse and $\ell$-strong Schreier, and the two largest
elements $a < b$ of $A$ below $n + 1$ satisfy $n + 1 + a = 2b$. -/
def IsRefinedSchreier (n l : ℕ) (A : Finset ℕ) : Prop :=
  n + 1 ∈ A ∧ (∀ x ∈ A, x ≤ n + 1) ∧ 3 ≤ A.card ∧ IsSparse A ∧
    IsStrongSchreier l A ∧
      ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b < n + 1 ∧
        (∀ x ∈ A, x ≤ b ∨ x = n + 1) ∧
          (∀ x ∈ A, x ≤ a ∨ x = b ∨ x = n + 1) ∧
            n + 1 + a = 2 * b

instance instDecidableIsRefinedSchreier (n l : ℕ) (A : Finset ℕ) :
    Decidable (IsRefinedSchreier n l A) := by
  unfold IsRefinedSchreier; infer_instance

/-- **Refined Schreier count.** For natural numbers $n$ and $\ell$, $|F_{n,\ell}|$ is the number of
finite sets $A$ of natural numbers such that $n + 1 \in A$, every element of $A$ is at most
$n + 1$, $A$ has at least three elements, $A$ is sparse and $\ell$-strong Schreier, and the two
largest elements $a < b$ of $A$ below $n + 1$ satisfy $n + 1 + a = 2b$. Every such set is
contained in $\{0, \dots, n + 1\}$. -/
def refinedSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (IsRefinedSchreier n l)).card

/-- **Refined Schreier sets with a given number of elements.** For natural numbers $n$ and
$\ell$, let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has
largest element $n + 1$ and at least three elements, $A$ is sparse (the differences of
consecutive elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. For a natural number $k$, $|F_{n,\ell,k}|$ is the
number of sets in $F_{n,\ell}$ with exactly $k$ elements. -/
def refinedSchreierCardCount (n l k : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k)).card

/-- **Refined Schreier sets with a given size and minimum.** For natural numbers $n$ and
$\ell$, let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has
largest element $n + 1$ and at least three elements, $A$ is sparse (the differences of
consecutive elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. For natural numbers $k$ and $q$, $|F_{n,\ell,k,q}|$
is the number of sets in $F_{n,\ell}$ with exactly $k$ elements whose smallest element is
$q$. -/
def refinedSchreierCardMinCount (n l k q : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k ∧
      q ∈ A ∧ ∀ x ∈ A, q ≤ x)).card

-- List vertices from largest to smallest, specifying their minimum and successive gaps.
private def vertices (m : ℕ) : List ℕ → List ℕ
  | [] => [m]
  | d :: ds => (m + (d :: ds).sum) :: vertices m ds

private theorem vertices_eq_cons (m : ℕ) (ds : List ℕ) :
    ∃ xs, vertices m ds = (m + ds.sum) :: xs := by
  cases ds with
  | nil => exact ⟨[], by simp [vertices]⟩
  | cons d ds => exact ⟨_, rfl⟩

private theorem vertices_head (m : ℕ) (ds : List ℕ) :
    m + ds.sum ∈ vertices m ds := by
  cases ds <;> simp [vertices]

private theorem vertices_bounds {m x : ℕ} {ds : List ℕ} (hx : x ∈ vertices m ds) :
    m ≤ x ∧ x ≤ m + ds.sum := by
  induction ds with
  | nil => simp_all [vertices]
  | cons d ds ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have := ih hx
      simp only [List.sum_cons]
      omega

private theorem vertices_min (m : ℕ) (ds : List ℕ) : m ∈ vertices m ds := by
  induction ds with
  | nil => simp [vertices]
  | cons d ds ih => exact List.mem_cons_of_mem _ ih

private theorem vertices_length (m : ℕ) (ds : List ℕ) :
    (vertices m ds).length = ds.length + 1 := by
  induction ds <;> simp_all [vertices]

private theorem vertices_desc (m : ℕ) {ds : List ℕ} (hp : ∀ d ∈ ds, 0 < d) :
    (vertices m ds).Pairwise (· > ·) := by
  induction ds with
  | nil => simp [vertices]
  | cons d ds ih =>
    refine List.pairwise_cons.mpr ⟨?_, ih (fun x hx => hp x (by simp [hx]))⟩
    intro x hx
    have := (vertices_bounds hx).2
    have := hp d (by simp)
    simp only [List.sum_cons]
    omega

private theorem exists_vertices (x : ℕ) (xs : List ℕ) (hs : (x :: xs).Pairwise (· > ·)) :
    ∃ m ds, vertices m ds = x :: xs ∧ ∀ d ∈ ds, 0 < d := by
  induction xs generalizing x with
  | nil => exact ⟨x, [], rfl, by simp⟩
  | cons y ys ih =>
    obtain ⟨m, ds, he, hp⟩ := ih y hs.tail
    have hxy := List.rel_of_pairwise_cons hs (by simp : y ∈ y :: ys)
    have hy : m + ds.sum = y := by
      cases ds <;> simp_all [vertices]
    refine ⟨m, (x - y) :: ds, ?_, ?_⟩
    · simp [vertices, he, List.sum_cons, show m + (x - y + ds.sum) = x by omega]
    · simpa using And.intro (show 0 < x - y by omega) hp

private theorem vertices_inj {m m' : ℕ} {ds es : List ℕ}
    (h : vertices m ds = vertices m' es) : m = m' ∧ ds = es := by
  induction ds generalizing es with
  | nil =>
    cases es with
    | nil => simpa [vertices] using h
    | cons e es =>
      have := congrArg List.length h
      simp [vertices_length] at this
  | cons d ds ih =>
    cases es with
    | nil =>
      have := congrArg List.length h
      simp [vertices_length] at this
    | cons e es =>
      obtain ⟨ht, hs⟩ := List.cons.inj h
      obtain ⟨rfl, rfl⟩ := ih hs
      simp [List.sum_cons] at ht
      simp [ht]

private theorem sparse_step {c b a : ℕ} {xs : List ℕ} (hc : b < c) (hb : a < b)
    (ht : ∀ x ∈ xs, x < a) :
    IsSparse (c :: b :: a :: xs).toFinset ↔
      b - a ≤ c - b ∧ IsSparse (b :: a :: xs).toFinset := by
  simp only [IsSparse, List.mem_toFinset, List.mem_cons]
  constructor
  · intro h
    constructor
    · apply h a (by simp) b (by simp) c (by simp) hb hc <;> grind
    · intro u hu v hv w hw huv hvw h₁ h₂
      apply h u (Or.inr hu) v (Or.inr hv) w (Or.inr hw) huv hvw <;> grind
  · rintro ⟨hgap, h⟩ u hu v hv w hw huv hvw h₁ h₂
    rcases hw with rfl | hw
    · have : v = b := by grind
      have : u = a := by grind
      omega
    · apply h u (by grind) v (by grind) w hw huv hvw <;> grind

private theorem sparse_vertices_iff (m : ℕ) (ds : List ℕ) (hp : ∀ d ∈ ds, 0 < d) :
    IsSparse (vertices m ds).toFinset ↔ ds.Pairwise (· ≥ ·) := by
  induction ds with
  | nil => simp [vertices, IsSparse]
  | cons d ds ih =>
    cases ds with
    | nil =>
      simp only [vertices, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
        or_false, List.pairwise_cons, IsSparse]
      grind
    | cons e es =>
      obtain ⟨xs, hxs⟩ := vertices_eq_cons m es
      have hdesc := vertices_desc m (ds := es) (fun x hx => hp x (by simp [hx]))
      rw [hxs] at hdesc
      have he := hp e (by simp)
      have hd := hp d (by simp)
      specialize ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      simp only [vertices, List.sum_cons, hxs] at ih ⊢
      rw [sparse_step (by omega) (by omega) (List.pairwise_cons.mp hdesc).1, ih]
      simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> refine ⟨?_, ?_⟩ <;> grind

private theorem top_gaps_iff {c b a : ℕ} {xs : List ℕ} (hc : b < c) (hb : a < b)
    (ht : ∀ x ∈ xs, x < a) :
    (∃ u ∈ c :: b :: a :: xs, ∃ v ∈ c :: b :: a :: xs, u < v ∧ v < c ∧
      (∀ x ∈ c :: b :: a :: xs, x ≤ v ∨ x = c) ∧
      (∀ x ∈ c :: b :: a :: xs, x ≤ u ∨ x = v ∨ x = c) ∧ c + u = 2 * v) ↔
      c + a = 2 * b := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨u, hu, v, hv, huv, hvc, h₁, h₂, he⟩
    specialize h₁ b (by simp)
    specialize h₂ a (by simp)
    have : v = b := by grind
    have : u = a := by grind
    omega
  · intro he
    exact ⟨a, by simp, b, by simp, hb, hc, by grind, by grind, he⟩

private theorem refined_vertices_iff {n l m : ℕ} {ds : List ℕ} (hp : ∀ d ∈ ds, 0 < d) :
    IsRefinedSchreier n l (vertices m ds).toFinset ↔
      m + ds.sum = n + 1 ∧ l * ds.length + 1 ≤ m ∧ ds.Pairwise (· ≥ ·) ∧
        ∃ d es, ds = d :: d :: es := by
  have hcard := List.toFinset_card_of_nodup (vertices_desc m hp).nodup
  rw [vertices_length] at hcard
  have hmax : n + 1 ∈ vertices m ds ∧ (∀ x ∈ vertices m ds, x ≤ n + 1) ↔
      m + ds.sum = n + 1 := by
    constructor
    · rintro ⟨h, hh⟩
      exact le_antisymm (hh _ (vertices_head ..)) (vertices_bounds h).2
    · intro he
      rw [← he]
      exact ⟨vertices_head .., fun _ h => (vertices_bounds h).2⟩
  have hstrong : IsStrongSchreier l (vertices m ds).toFinset ↔ l * ds.length + 1 ≤ m := by
    simp only [IsStrongSchreier, hcard, List.mem_toFinset, Nat.mul_succ]
    constructor
    · intro h
      have := h m (vertices_min ..)
      omega
    · intro h x hx
      have := (vertices_bounds hx).1
      omega
  simp only [IsRefinedSchreier, hcard, List.mem_toFinset, hstrong, sparse_vertices_iff m ds hp]
  rw [← and_assoc, hmax]
  refine and_congr_right fun h => ?_
  cases ds with
  | nil => simp
  | cons d ds =>
    cases ds with
    | nil => simp
    | cons e es =>
      obtain ⟨xs, hxs⟩ := vertices_eq_cons m es
      have hd := hp d (by simp)
      have he := hp e (by simp)
      have hdesc := vertices_desc m (ds := es) (fun x hx => hp x (by simp [hx]))
      rw [hxs] at hdesc
      rw [← h]
      simp only [vertices, hxs, List.sum_cons, List.length_cons, List.cons.injEq]
      rw [top_gaps_iff (by omega) (by omega) (List.pairwise_cons.mp hdesc).1]
      grind

-- The common parameters are the excess of the largest part over the second largest,
-- and the other parts (in decreasing order) after subtracting l.
@[ext] private structure Parameters (n l : ℕ) where
  excess : ℕ
  gap : ℕ
  rest : List ℕ
  pos : ∀ x ∈ gap :: rest, 0 < x
  desc : (gap :: rest).Pairwise (· ≥ ·)
  total : l * (rest.length + 2) + excess + (gap :: gap :: rest).sum = n

private def partList (l r d : ℕ) (ds : List ℕ) : List ℕ :=
  (d + l + r) :: (d :: ds).map (· + l)

private theorem partList_sum (l r d : ℕ) (ds : List ℕ) :
    (partList l r d ds).sum = l * (ds.length + 2) + r + (d :: d :: ds).sum := by
  have h : (ds.map (· + l)).sum = l * ds.length + ds.sum := by
    induction ds <;> simp_all [Nat.mul_succ]
    omega
  simp [partList, h, Nat.mul_add]
  omega

private theorem partList_desc {l r d : ℕ} {ds : List ℕ} (hs : (d :: ds).Pairwise (· ≥ ·)) :
    (partList l r d ds).Pairwise (· ≥ ·) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    have := List.pairwise_cons.mp hs
    grind
  · exact List.pairwise_map.mpr (hs.imp (by intro a b hab; exact Nat.add_le_add_right hab l))

private abbrev largePartitions (n l : ℕ) :=
  (Nat.Partition.restricted n (fun x => l + 1 ≤ x)).erase (Nat.Partition.indiscrete n)

private abbrev refinedFamily (n l : ℕ) :=
  (Finset.Icc 0 (n + 1)).powerset.filter (IsRefinedSchreier n l)

private theorem mem_refinedFamily {n l : ℕ} {A : Finset ℕ} :
    A ∈ refinedFamily n l ↔ IsRefinedSchreier n l A := by
  simp only [refinedFamily, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  intro h x hx
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, h.2.1 x hx⟩

private def Parameters.partition {n l : ℕ} (s : Parameters n l) : ↥(largePartitions n l) := by
  let ps := partList l s.excess s.gap s.rest
  have hbound : ∀ x ∈ ps, l + 1 ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := s.pos s.gap (by simp)
      omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := s.pos y hy
      omega
  let p : Nat.Partition n :=
    ⟨ps, fun hx => by have := hbound _ hx; omega, (partList_sum ..).trans s.total⟩
  refine ⟨p, Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbound⟩⟩⟩
  intro he
  have hn : n ≠ 0 := by
    have := s.pos s.gap (by simp)
    have := s.total
    simp only [List.sum_cons] at this
    omega
  have hc := congrArg (fun q : Nat.Partition n => q.parts.card) he
  simp [p, ps, partList, Nat.Partition.indiscrete_parts hn] at hc

private theorem Parameters.partition_injective {n l : ℕ} :
    Function.Injective (Parameters.partition (n := n) (l := l)) := by
  intro s t h
  have he := congrArg (fun p : ↥(largePartitions n l) => p.val.parts) h
  change (↑(partList l s.excess s.gap s.rest) : Multiset ℕ) = ↑(partList l t.excess t.gap t.rest)
    at he
  have hh := (Multiset.coe_eq_coe.mp he).eq_of_pairwise'
    (partList_desc s.desc) (partList_desc t.desc)
  simp only [partList, List.map_cons, List.cons.injEq] at hh
  obtain ⟨h₁, h₂, h₃⟩ := hh
  apply Parameters.ext
  · omega
  · omega
  · exact List.map_injective_iff.mpr (add_left_injective l) h₃

private theorem Parameters.partition_surjective {n l : ℕ} (hn : l + 1 ≤ n) :
    Function.Surjective (Parameters.partition (n := n) (l := l)) := by
  rintro ⟨p, hp⟩
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hp
  have bound := (Finset.mem_filter.mp hmem).2
  let ps := p.parts.sort (· ≥ ·)
  have hs : ps.Pairwise (· ≥ ·) := Multiset.pairwise_sort ..
  have he : (ps : Multiset ℕ) = p.parts := Multiset.sort_eq ..
  have hsum : ps.sum = n := (congrArg Multiset.sum he).trans p.parts_sum
  have hbound (x) (hx : x ∈ ps) : l + 1 ≤ x := bound x ((Multiset.mem_sort _).mp hx)
  obtain ⟨x, y, ys, hps⟩ : ∃ x y ys, ps = x :: y :: ys := by
    cases h : ps with
    | nil => simp [h] at hsum; omega
    | cons x xs =>
      cases xs with
      | nil =>
        exfalso
        apply hne (Nat.Partition.ext ?_)
        rw [← he, h, Nat.Partition.indiscrete_parts (by omega)]
        simp [h] at hsum
        simp [hsum]
      | cons y ys => exact ⟨x, y, ys, rfl⟩
  rw [hps] at hs hbound
  have hy := hbound y (by simp)
  have hyx := List.rel_of_pairwise_cons hs (by simp : y ∈ y :: ys)
  let ds := ys.map (· - l)
  have htail : ((y - l) :: ds) = (y :: ys).map (· - l) := rfl
  have hlist : partList l (x - y) (y - l) ds = ps := by
    rw [hps, partList, htail, List.map_map]
    congr 1
    · omega
    · exact List.map_congr_left (fun z hz => by
        have := hbound z (List.mem_cons_of_mem _ hz)
        dsimp
        omega) |>.trans (List.map_id _)
  let s : Parameters n l :=
    { excess := x - y
      gap := y - l
      rest := ds
      pos := by
        rw [htail]
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        have := hbound w (List.mem_cons_of_mem _ hw)
        omega
      desc := by
        rw [htail, List.pairwise_map]
        exact hs.tail.imp (fun hab => Nat.sub_le_sub_right hab l)
      total := by rw [← partList_sum, hlist, hsum] }
  refine ⟨s, Subtype.ext (Nat.Partition.ext ?_)⟩
  exact (congrArg (fun t : List ℕ => (t : Multiset ℕ)) hlist).trans he

private def Parameters.minimum {n l : ℕ} (s : Parameters n l) : ℕ :=
  l * (s.rest.length + 2) + 1 + s.excess

private theorem Parameters.gaps_pos {n l : ℕ} (s : Parameters n l) :
    ∀ x ∈ s.gap :: s.gap :: s.rest, 0 < x := by
  simpa only [List.forall_mem_cons, and_self_left] using s.pos

private def Parameters.vertexSet {n l : ℕ} (s : Parameters n l) : ↥(refinedFamily n l) := by
  refine ⟨(vertices s.minimum (s.gap :: s.gap :: s.rest)).toFinset,
    mem_refinedFamily.mpr ((refined_vertices_iff s.gaps_pos).mpr ⟨?_, ?_, ?_, _, _, rfl⟩)⟩
  · unfold Parameters.minimum
    have := s.total
    omega
  · simp [Parameters.minimum]
  · exact List.pairwise_cons.mpr ⟨by simpa using (List.pairwise_cons.mp s.desc).1, s.desc⟩

private theorem Parameters.vertexSet_sort {n l : ℕ} (s : Parameters n l) :
    s.vertexSet.val.sort (· ≥ ·) = vertices s.minimum (s.gap :: s.gap :: s.rest) := by
  have h := vertices_desc s.minimum s.gaps_pos
  exact (List.toFinset_sort (· ≥ ·) h.nodup).mpr (h.imp (fun hab => Nat.le_of_lt hab))

private theorem Parameters.vertexSet_injective {n l : ℕ} :
    Function.Injective (Parameters.vertexSet (n := n) (l := l)) := by
  intro s t h
  have he := congrArg (fun A : ↥(refinedFamily n l) => A.val.sort (· ≥ ·)) h
  simp only [Parameters.vertexSet_sort] at he
  obtain ⟨hm, hs⟩ := vertices_inj he
  obtain ⟨hd, _, hds⟩ := List.cons.inj hs |>.imp_right List.cons.inj
  simp only [Parameters.minimum, hds, Nat.add_left_cancel_iff] at hm
  exact Parameters.ext hm hd hds

private theorem Parameters.vertexSet_surjective {n l : ℕ} :
    Function.Surjective (Parameters.vertexSet (n := n) (l := l)) := by
  rintro ⟨A, hA⟩
  have href := mem_refinedFamily.mp hA
  let vs := A.sort (· ≥ ·)
  obtain ⟨x, xs, hvs⟩ : ∃ x xs, vs = x :: xs := by
    cases h : vs with
    | nil =>
      have hlen : vs.length = A.card := A.length_sort _
      have := href.2.2.1
      simp [h] at hlen
      omega
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hdesc : vs.Pairwise (· > ·) := A.sortedGT_sort.pairwise
  obtain ⟨m, gs, hgs, hp⟩ := exists_vertices x xs (hvs ▸ hdesc)
  have hset : (vertices m gs).toFinset = A := by rw [hgs, ← hvs]; exact A.sort_toFinset _
  obtain ⟨hmax, hmin, hsort, d, ds, rfl⟩ := (refined_vertices_iff hp).mp (hset ▸ href)
  change l * (ds.length + 2) + 1 ≤ m at hmin
  let s : Parameters n l :=
    { excess := m - (l * (ds.length + 2) + 1)
      gap := d
      rest := ds
      pos := fun z hz => hp z (List.mem_cons_of_mem _ hz)
      desc := hsort.tail
      total := by omega }
  have hm : s.minimum = m := by unfold Parameters.minimum; dsimp [s]; omega
  exact ⟨s, Subtype.ext (by change (vertices s.minimum (d :: d :: ds)).toFinset = A; rwa [hm])⟩

/-- **Partitions into large parts and the refined Schreier family.** Let $n$ and $\ell$ be
natural numbers with $n \ge \ell + 1$. Let $F_{n,\ell}$ be the family of finite sets $A$ of
natural numbers such that $A$ has largest element $n + 1$ and at least three elements, $A$ is
sparse (the differences of consecutive elements, in increasing order, are non-decreasing) and
$\ell$-strong Schreier ($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and
third largest elements $b > a$ of $A$ satisfy $n + 1 + a = 2b$. Then the number
$|E_{n,\ell+1}|$ of partitions of $n$ into parts that are all at least $\ell + 1$ equals
$|F_{n,\ell}| + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 13. -/
theorem partitionMinPartCount_eq_refined_add_one (n l : ℕ)
    (hn : l + 1 ≤ n) :
    partitionMinPartCount n (l + 1) = refinedSchreierCount n l + 1 := by
  have hsingle : Nat.Partition.indiscrete n ∈ Nat.Partition.restricted n (fun x => l + 1 ≤ x) := by
    simpa [Nat.Partition.restricted, Nat.Partition.indiscrete_parts (show n ≠ 0 by omega)]
  let ep := Equiv.ofBijective _ ⟨Parameters.partition_injective, Parameters.partition_surjective hn⟩
  let ev : Parameters n l ≃ ↥(refinedFamily n l) :=
    Equiv.ofBijective _ ⟨Parameters.vertexSet_injective, Parameters.vertexSet_surjective⟩
  have e := ep.symm.trans ev
  rw [partitionMinPartCount, ← Finset.card_erase_add_one hsingle]
  congr 1
  simpa only [Fintype.card_coe, largePartitions, refinedSchreierCount, refinedFamily] using
    Fintype.card_congr e

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted
