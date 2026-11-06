/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.PNat.Basic

/-!
# Arithmetic progressions in CR-sets

Statements from Dibyendu De and Pintu Debnath, *Abundance of Arithmetic
Progressions in CR-Sets*, INTEGERS 25 (2025), Article A4 (arXiv:2211.12372).

The paper works in a commutative semigroup `(S, +)`; finite sums in `S` are written
as left folds `List.foldl (· + ·) s l`, so no additive identity is needed. The
progression `a, a + b, …, a + l b` is written `(· + b)^[i] a` for `i ≤ l`. The
paper's `ℕ` is the positive integers, modelled by `ℕ+`.

Ultrafilters are multiplied with Mathlib's `Ultrafilter.semigroup`, for which
`A ∈ p * q` iff `{x | {y | x * y ∈ A} ∈ q} ∈ p`; this is the paper's convention,
and `q ↦ q * p` is continuous (`Ultrafilter.continuous_mul_left`), so `βS` is the
paper's compact right topological semigroup.

`MetaMathlibExt.IsPiecewiseSyndetic` (WantedExt/Combinatorics/PiecewiseSyndeticWanted.lean)
is specific to `ℕ^t` with its cube geometry; Theorem 1 here needs `ℤ` and `ℤ × ℤ`,
so the general semigroup notion of the paper is defined separately.
-/

namespace MetaMathlibExt

@[expose] public section

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

section Largeness

variable {S : Type*} [AddCommSemigroup S]

/-- **Thick set in a commutative semigroup.** A subset $A$ of a commutative semigroup $(S, +)$ is
thick when for every finite set $E \subseteq S$ there is an $x \in S$ with $E + x \subseteq A$,
that is, $e + x \in A$ for every $e \in E$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
def IsAddThick (A : Set S) : Prop :=
  ∀ E : Finset S, ∃ x : S, ∀ e ∈ E, e + x ∈ A

/-- **Piecewise syndetic set in a commutative semigroup.** A subset $A$ of a commutative semigroup
$(S, +)$ is piecewise syndetic when there is a finite set $F \subseteq S$ such that the union
$\bigcup_{t \in F} (-t + A)$ is thick, where $-t + A = \{s \in S : t + s \in A\}$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
def IsAddPiecewiseSyndetic (A : Set S) : Prop :=
  ∃ F : Finset S, IsAddThick (⋃ t ∈ F, {s : S | t + s ∈ A})

/-- **J-sets in commutative semigroups.** Let $S$ be a commutative semigroup and let
$\mathbb{N} = \{0, 1, 2, \dots\}$. A set $A \subseteq S$ is a $J$-set when for every finite set
$F$ of sequences $f \colon \mathbb{N} \to S$ there are $a \in S$ and a nonempty finite set
$H \subseteq \mathbb{N}$ such that $a + \sum_{n \in H} f(n) \in A$ for every $f \in F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
def IsJSet (A : Set S) : Prop :=
  ∀ F : Finset (ℕ → S), ∃ a : S, ∃ H : List ℕ, H.Nodup ∧ H ≠ [] ∧
    ∀ f ∈ F, (H.map f).foldl (· + ·) a ∈ A

/-- **CR-set.** A subset $A$ of a commutative semigroup $(S, +)$ is a CR-set (combinatorially rich)
when for every natural number $n$, including $n = 0$, there is a natural number $r$ such that for
every $r \times n$ matrix $(m_{ij})$ with entries in $S$ there are a nonempty set
$\alpha \subseteq \{1, \ldots, r\}$ and an element $s \in S$ such that
$s + \sum_{i \in \alpha} m_{ij} \in A$ for every column $j \in \{1, \ldots, n\}$.

The paper takes $n \ge 1$. Allowing $n = 0$ adds the requirement that $S$ be nonempty, the
paper's implicit convention: over an empty $S$ every case $n \ge 1$ holds vacuously (take
$r = 1$; there is no matrix), so without it $\emptyset$ would be a CR-set of the empty
semigroup. Over a nonempty $S$ the two definitions agree.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
def IsCRSet (A : Set S) : Prop :=
  ∀ n : ℕ, ∃ r : ℕ, ∀ M : Fin r → Fin n → S, ∃ α : Finset (Fin r), α.Nonempty ∧
    ∃ s : S, ∀ j, (α.toList.map fun i => M i j).foldl (· + ·) s ∈ A

/-- **Essential CR-set.** Let $(S, +)$ be a commutative semigroup, and add ultrafilters on $S$ by
the rule that $E \in p + q$ if and only if $\{x \in S : \{y \in S : x + y \in E\} \in q\} \in p$.
A subset $A$ of $S$ is an essential CR-set when there is an ultrafilter $p$ on $S$ with
$p + p = p$, all of whose members are CR-sets, such that $A \in p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of essential CR-sets before Theorem 7). -/
def IsEssentialCRSet (A : Set S) : Prop :=
  ∃ p : Ultrafilter S, p + p = p ∧ (∀ B ∈ p, IsCRSet B) ∧ A ∈ p

/-- **The whole commutative semigroup is thick.** If $S$ is a nonempty commutative semigroup,
then $S$ itself is a thick subset of $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem isAddThick_univ [Nonempty S] : IsAddThick (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, fun _ _ => Set.mem_univ _⟩

/-- **The empty set is not thick.** In a nonempty commutative semigroup, the empty set is not
thick.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of thick sets). -/
theorem not_isAddThick_empty [Nonempty S] : ¬ IsAddThick (∅ : Set S) := by
  intro h
  obtain ⟨x, hx⟩ := h {Classical.arbitrary S}
  exact hx _ (Finset.mem_singleton_self _)

/-- **The whole commutative semigroup is piecewise syndetic.** If $S$ is a nonempty commutative
semigroup, then $S$ itself is a piecewise syndetic subset of $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 1 (definition of piecewise syndetic sets). -/
theorem isAddPiecewiseSyndetic_univ [Nonempty S] :
    IsAddPiecewiseSyndetic (Set.univ : Set S) :=
  ⟨{Classical.arbitrary S}, fun _ => ⟨Classical.arbitrary S, fun _ _ => by simp⟩⟩

/-- **The whole semigroup is a J-set.** In every nonempty commutative semigroup $S$, the set $S$
itself is a $J$-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 1. -/
theorem isJSet_univ [Nonempty S] : IsJSet (Set.univ : Set S) :=
  fun _ => ⟨Classical.arbitrary S, [0], List.nodup_singleton 0, List.cons_ne_nil _ _,
    fun _ _ => Set.mem_univ _⟩

/-- **The whole commutative semigroup is a CR-set.** If $S$ is a nonempty commutative semigroup,
then $S$ itself is a CR-set in $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
theorem isCRSet_univ [Nonempty S] : IsCRSet (Set.univ : Set S) :=
  fun _ => ⟨1, fun _ => ⟨Finset.univ, Finset.univ_nonempty, Classical.arbitrary S,
    fun _ => Set.mem_univ _⟩⟩

/-- **The empty set is not a CR-set.** In every commutative semigroup, the empty set is not a
CR-set.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Definition 2. -/
theorem not_isCRSet_empty : ¬ IsCRSet (∅ : Set S) := by
  intro h
  obtain ⟨r₀, hr₀⟩ := h 0
  obtain ⟨-, -, s, -⟩ := hr₀ fun _ => Fin.elim0
  obtain ⟨r, hr⟩ := h 1
  obtain ⟨α, -, t, ht⟩ := hr fun _ _ => s
  exact ht 0

end Largeness

section Families

variable {S : Type*}

/-- **Families with the Ramsey property.** Let $S$ be a set. A collection $F$ of subsets of $S$ is
a family with the Ramsey property when $F$ is nonempty, $\emptyset \notin F$, $F$ is closed under
supersets (if $A \in F$ and $A \subseteq B$, then $B \in F$), and whenever $A \cup B \in F$, then
$A \in F$ or $B \in F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (families and the Ramsey property). -/
def IsRamseyFamily (F : Set (Set S)) : Prop :=
  F.Nonempty ∧ ∅ ∉ F ∧ (∀ A B, A ∈ F → A ⊆ B → B ∈ F) ∧
    ∀ A B, A ∪ B ∈ F → A ∈ F ∨ B ∈ F

/-- **The set β(F) of ultrafilters inside a family.** For a family $\mathcal F$ of subsets of a
set $S$, $\beta(\mathcal F)$ is the set of ultrafilters $p$ on $S$ all of whose members lie in
$\mathcal F$, that is, $A \in \mathcal F$ for every $A \in p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
def betaFamily (F : Set (Set S)) : Set (Ultrafilter S) :=
  {p | ∀ A ∈ p, A ∈ F}

/-- **Membership in β(F).** Let $F$ be a collection of subsets of a set $S$ and let $p$ be an
ultrafilter on $S$. Then $p \in \beta(F)$ if and only if every member of $p$ belongs to $F$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem mem_betaFamily {F : Set (Set S)} {p : Ultrafilter S} :
    p ∈ betaFamily F ↔ ∀ A ∈ p, A ∈ F :=
  Iff.rfl

/-- **β of the nonempty sets is all of βS.** For every set $S$, every ultrafilter on $S$ lies in
$\beta(\mathcal F)$, where $\mathcal F$ is the family of all nonempty subsets of $S$; that is,
$\beta(\mathcal F) = \beta S$, the set of all ultrafilters on $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Section 2 (definition of `β(F)`). -/
theorem betaFamily_nonempty_sets :
    betaFamily {A : Set S | A.Nonempty} = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hA => Ultrafilter.nonempty_of_mem hA

/-- **Ultrafilters inside a Ramsey family form a closed set.** Let $F$ be a family of subsets of a
set $S$ with the Ramsey property. Then the set $\beta(F)$ of ultrafilters on $S$ all of whose
members lie in $F$ is closed in the space $\beta S$ of all ultrafilters on $S$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted isClosed_betaFamily {F : Set (Set S)} (hF : IsRamseyFamily F) :
    IsClosed (betaFamily F)

/-- **Theorem 3, part 2: a Ramsey family is the union of its ultrafilters.** Let $F$ be a family
of subsets of a set $S$ with the Ramsey property, and let $\beta(F)$ be the set of ultrafilters on
$S$ all of whose members lie in $F$. Then a set $A \subseteq S$ lies in $F$ if and only if
$A \in p$ for some $p \in \beta(F)$; that is, $F = \bigcup \beta(F)$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted mem_iff_exists_mem_betaFamily {F : Set (Set S)} (hF : IsRamseyFamily F)
    (A : Set S) : A ∈ F ↔ ∃ p ∈ betaFamily F, A ∈ p

/-- **Nonempty closed sets of ultrafilters come from Ramsey families.** Let $S$ be a set, let
$\beta S$ be the space of ultrafilters on $S$, and let $K$ be a nonempty closed subset of
$\beta S$. Let $\mathcal F_K$ be the collection of the sets $E \subseteq S$ with $E \in p$ for
some $p \in K$. Then $\mathcal F_K$ is a family with the Ramsey property, and
$\beta(\mathcal F_K) = K$, where $\beta(\mathcal F_K)$ is the set of ultrafilters on $S$ all of
whose members lie in $\mathcal F_K$.

The paper omits $K \ne \emptyset$; for $K = \emptyset$ the collection $\mathcal F_K$ is empty,
hence not a family.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted isRamseyFamily_and_betaFamily_eq_of_isClosed {K : Set (Ultrafilter S)}
    (hK : IsClosed K) (hne : K.Nonempty) :
    IsRamseyFamily {E : Set S | ∃ p ∈ K, E ∈ p} ∧ betaFamily {E : Set S | ∃ p ∈ K, E ∈ p} = K

/-- **β(F) contains an idempotent when it is a subsemigroup.** Let $S$ be a semigroup and
$\mathcal F$ a family of subsets of $S$ with the Ramsey property, and multiply ultrafilters on
$S$ by $E \in pq$ iff $\{x \in S : \{y \in S : xy \in E\} \in q\} \in p$. If
$pq \in \beta(\mathcal F)$ for all $p, q \in \beta(\mathcal F)$, then there is
$p \in \beta(\mathcal F)$ with $pp = p$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 3 (`integers-2025-A4-thm-3`). -/
public theorem_wanted exists_idempotent_mem_betaFamily [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) :
    ∃ p ∈ betaFamily F, p * p = p

/-- **Left-ideal criterion for β(F).** Let $S$ be a semigroup and $\mathcal F$ a family of subsets
of $S$ with the Ramsey property. Multiply ultrafilters on $S$ by $E \in pq$ iff
$\{x \in S : \{y \in S : xy \in E\} \in q\} \in p$. Then $pq \in \beta(\mathcal F)$ for every
ultrafilter $p$ on $S$ and every $q \in \beta(\mathcal F)$ (that is, $\beta(\mathcal F)$ is a
left ideal of $\beta S$) if and only if $sE = \{se : e \in E\}$ lies in $\mathcal F$ for every
$s \in S$ and every $E \in \mathcal F$.

The paper's second sentence (right ideal iff right shift-invariant) is omitted: with this
convention it fails. Let $L$ be a minimal left ideal of $\beta\mathbb{N}$ and $\mathcal F_L$ the
family of sets belonging to some member of $L$. By the left half $\mathcal F_L$ is
shift-invariant ($\mathbb{N}$ is commutative), yet $L$ is not a right ideal, since a two-sided
ideal contains the smallest ideal $K(\beta\mathbb{N})$, a union of more than one minimal left
ideal.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 4 (`integers-2025-A4-thm-4`). -/
public theorem_wanted betaFamily_isLeftIdeal_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p : Ultrafilter S, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ s : S, ∀ E ∈ F, (fun e => s * e) '' E ∈ F

/-- **Subsemigroup criterion for β(F).** Let $S$ be a semigroup and $\mathcal F$ a family of
subsets of $S$ with the Ramsey property. For $x \in S$ and $E \subseteq S$ write
$x^{-1}E = \{y \in S : xy \in E\}$, and multiply ultrafilters on $S$ by $E \in pq$ iff
$\{x \in S : x^{-1}E \in q\} \in p$. Then $pq \in \beta(\mathcal F)$ for all
$p, q \in \beta(\mathcal F)$ if and only if every $E \subseteq S$ has the following property: if
there is $A \in \mathcal F$ such that $\bigcap_{x \in H} x^{-1}E \in \mathcal F$ for every finite
$H \subseteq A$, then $E \in \mathcal F$.

The source's intersection $\bigcap_{q \in H} x^{-1}E$ is read as $\bigcap_{x \in H} x^{-1}E$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 5 (`integers-2025-A4-thm-5`). -/
public theorem_wanted betaFamily_isSubsemigroup_iff [Semigroup S] {F : Set (Set S)}
    (hF : IsRamseyFamily F) :
    (∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) ↔
      ∀ E : Set S, (∃ A ∈ F, ∀ H : Finset S, ↑H ⊆ A →
        (⋂ x ∈ H, {y : S | x * y ∈ E}) ∈ F) → E ∈ F

/-- **Decreasing shift-closed sequences give essential sets.** Let $S$ be a semigroup and let $F$
be a family of subsets of $S$ with the Ramsey property, and write $\beta(F)$ for the set of
ultrafilters on $S$ all of whose members lie in $F$. For $x \in S$ and $E \subseteq S$ write
$x^{-1}E = \{y \in S : xy \in E\}$, and multiply ultrafilters on $S$ by the rule that
$E \in p \cdot q$ if and only if $\{x \in S : x^{-1}E \in q\} \in p$. Suppose that
$p \cdot q \in \beta(F)$ whenever $p, q \in \beta(F)$. Let $A \subseteq S$, and let
$C_0 \supseteq C_1 \supseteq C_2 \supseteq \cdots$ be members of $F$ contained in $A$ such that
for every $n$ and every $x \in C_n$ there is an $m$ with $C_m \subseteq x^{-1}C_n$. Then some
$p \in \beta(F)$ satisfies $p \cdot p = p$ and $A \in p$; that is, $A$ is an essential $F$-set.

This is the implication (d) ⇒ (a) of the paper's Theorem 6; statements (b) (trees of functions)
and (c) (downward directed families) are omitted. The sequence is indexed from $0$ rather
than $1$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem_wanted exists_idempotent_mem_of_decreasing_sequence [Semigroup S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (C : ℕ → Set S) (hanti : Antitone C) (hCA : ∀ n, C n ⊆ A)
    (hshift : ∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) (hCF : ∀ n, C n ∈ F) :
    ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p

/-- **Essential F-sets contain shift-closed decreasing sequences (countable case).** Let $S$ be
a countable semigroup and $\mathcal F$ a family of subsets of $S$ with the Ramsey property. For
$x \in S$ and $E \subseteq S$ write $x^{-1}E = \{y \in S : xy \in E\}$, multiply ultrafilters on
$S$ by $E \in pq$ iff $\{x \in S : x^{-1}E \in q\} \in p$, and assume $pq \in \beta(\mathcal F)$
for all $p, q \in \beta(\mathcal F)$. If $A \subseteq S$ belongs to some $p \in \beta(\mathcal F)$
with $pp = p$ (an essential $\mathcal F$-set), then there are sets $C_0 \supseteq C_1 \supseteq
C_2 \supseteq \cdots$ in $\mathcal F$, all contained in $A$, such that for every $n$ and every
$x \in C_n$ there is $m$ with $C_m \subseteq x^{-1}C_n$.

Statements (b) (trees of functions) and (c) (downward directed families) of the paper are
omitted. The sequence is indexed from $0$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 6 (`integers-2025-A4-thm-6`). -/
public theorem_wanted exists_decreasing_sequence_of_idempotent_mem [Semigroup S] [Countable S]
    {F : Set (Set S)} (hF : IsRamseyFamily F)
    (hsub : ∀ p ∈ betaFamily F, ∀ q ∈ betaFamily F, p * q ∈ betaFamily F) {A : Set S}
    (hA : ∃ p ∈ betaFamily F, p * p = p ∧ A ∈ p) :
    ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x * y ∈ C n}) ∧ ∀ n, C n ∈ F

end Families

/-- **Furstenberg–Glasner theorem on progressions in piecewise syndetic sets.** If
$S \subseteq \mathbb{Z}$ is piecewise syndetic, then for every natural number $k$ the set of pairs
$(a, d) \in \mathbb{Z} \times \mathbb{Z}$ such that $a + i d \in S$ for all $i = 0, 1, \dots, k$
is piecewise syndetic in $\mathbb{Z} \times \mathbb{Z}$.

The paper takes $k \ge 1$; the case $k = 0$ is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 1 (`integers-2025-A4-thm-1`). -/
public theorem_wanted IsAddPiecewiseSyndetic.arithmeticProgressions_int {S : Set ℤ}
    (hS : IsAddPiecewiseSyndetic S) (k : ℕ) :
    IsAddPiecewiseSyndetic {p : ℤ × ℤ | ∀ i ≤ k, p.1 + i * p.2 ∈ S}

/-- **Debnath–Goswami theorem on progressions in J-sets.** Let $\mathbb{N}^+$ denote the
positive integers under addition. If $S \subseteq \mathbb{N}^+$ is a $J$-set, then for every
natural number $k$ the set of pairs $(a, d) \in \mathbb{N}^+ \times \mathbb{N}^+$ such that
$a + i d \in S$ for all $i = 0, 1, \dots, k$ is a $J$-set in $\mathbb{N}^+ \times \mathbb{N}^+$.

The paper writes $\mathbb{N}$ for the positive integers and takes $k \ge 1$; the case $k = 0$ is
included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 2 (`integers-2025-A4-thm-2`). -/
public theorem_wanted IsJSet.arithmeticProgressions_pnat {S : Set ℕ+} (hS : IsJSet S) (k : ℕ) :
    IsJSet {p : ℕ+ × ℕ+ | ∀ i ≤ k, (· + p.2)^[i] p.1 ∈ S}

/-- **Essential CR-sets via decreasing sequences.** Let $S$ be a countable commutative semigroup
and let $A \subseteq S$. Then $A$ is an essential CR-set if and only if there is a decreasing
sequence $C_0 \supseteq C_1 \supseteq C_2 \supseteq \cdots$ of CR-sets contained in $A$ such that
for every $n$ and every $x \in C_n$ there is an $m$ with $C_m \subseteq -x + C_n$, where
$-x + C_n = \{y \in S : x + y \in C_n\}$.

The sequence is indexed from $0$ rather than $1$.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 7 (`integers-2025-A4-thm-7`). -/
public theorem_wanted isEssentialCRSet_iff_exists_decreasing_sequence {S : Type*}
    [AddCommSemigroup S] [Countable S] (A : Set S) :
    IsEssentialCRSet A ↔ ∃ C : ℕ → Set S, Antitone C ∧ (∀ n, C n ⊆ A) ∧
      (∀ n, ∀ x ∈ C n, ∃ m, C m ⊆ {y : S | x + y ∈ C n}) ∧ ∀ n, IsCRSet (C n)

/-- **Arithmetic progressions in CR-sets.** If $A$ is a CR-set in a commutative semigroup
$(S, +)$ and $l$ is a natural number, then the set of pairs $(a, b) \in S \times S$ such that
$a, a + b, a + 2b, \dots, a + lb$ all lie in $A$ is a CR-set in $S \times S$. Here $a + ib$ is
$a$ followed by $i$ additions of $b$, since $S$ need not have a zero.

The paper takes $l \ge 1$; the case $l = 0$ is included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 8 (`integers-2025-A4-thm-8`). -/
public theorem_wanted IsCRSet.arithmeticProgressions {S : Type*} [AddCommSemigroup S]
    {A : Set S} (hA : IsCRSet A) (l : ℕ) :
    IsCRSet {p : S × S | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A}

/-- **Arithmetic progressions in essential CR-sets of the positive integers.** Let $\mathbb{N}^+$
denote the positive integers under addition. If $A \subseteq \mathbb{N}^+$ is an essential CR-set
and $l$ is a natural number, then the set of pairs $(a, b) \in \mathbb{N}^+ \times \mathbb{N}^+$
such that $a + i b \in A$ for all $i = 0, 1, \dots, l$ is an essential CR-set in
$\mathbb{N}^+ \times \mathbb{N}^+$.

The paper writes $\mathbb{N}$ for the positive integers and takes $l \ge 1$; the case $l = 0$ is
included.

Source: De and Debnath, *Abundance of Arithmetic Progressions in CR-Sets*, INTEGERS
25 (2025), Article A4, Theorem 9 (`integers-2025-A4-thm-9`). -/
public theorem_wanted IsEssentialCRSet.arithmeticProgressions_pnat {A : Set ℕ+}
    (hA : IsEssentialCRSet A) (l : ℕ) :
    IsEssentialCRSet {p : ℕ+ × ℕ+ | ∀ i ≤ l, (· + p.2)^[i] p.1 ∈ A}

end

end MetaMathlibExt
