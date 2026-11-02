/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Difference representation function.** For a finite subset $A$ of an abelian group $G$ and
an element $x \in G$, the difference representation function $r_{A-A}(x)$ is the number of
ordered pairs $(a, a') \in A \times A$ with $a - a' = x$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public def subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (x : G) :
    ℕ :=
  ((A ×ˢ A).filter fun p => p.1 - p.2 = x).card

/-- **The $g$-difference basis number.** For a finite set $A \subseteq \mathbb{Z}$ and
$x \in \mathbb{Z}$, write $r_{A-A}(x)$ for the number of ordered pairs $(a, a') \in A \times A$
with $a - a' = x$. For natural numbers $g$ and $n$, a finite set $A \subseteq \mathbb{Z}$ is a
$g$-difference basis for $[n] = \{1, \dots, n\}$ if $r_{A-A}(x) \ge g$ for every $x \in [n]$, and
$\eta_g(n)$ is the least size of such a set.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public noncomputable def diffBasisNumber (g n : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset ℤ, A.card = k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, g ≤ subRepCount A x}

/-- **Difference basis number of an abelian group.** For an abelian group $G$ and
$g \in \mathbb{N}$, a $g$-difference basis of $G$ is a finite set $A \subseteq G$ such that every
$x \in G$ equals $a - a'$ for at least $g$ ordered pairs $(a, a') \in A \times A$. The difference
basis number $\eta_g(G)$ is the least size of a $g$-difference basis of $G$, and $0$ if $G$ has
none.

There is no $g$-difference basis when $G$ is infinite and $g \ge 1$, or when $G$ is finite and
$g > |G|$, since each element is $a - a'$ for at most $|A| \le |G|$ pairs; in these cases the
value $0$ is a convention. When $G$ is finite and $g \le |G|$, the set $A = G$ is a
$g$-difference basis, so $\eta_g(G)$ is a true minimum. This is the paper's $\eta_g(S)$ with
$S = G$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 3. -/
public noncomputable def groupDiffBasisNumber (g : ℕ) (G : Type*) [AddCommGroup G]
    [DecidableEq G] : ℕ :=
  sInf {k | ∃ A : Finset G, A.card = k ∧ ∀ x : G, g ≤ subRepCount A x}

/-- **Maximal sets with bounded difference multiplicities.** For a finite set
$A \subseteq \mathbb{Z}$ and $x \in \mathbb{Z}$, write $r_{A-A}(x)$ for the number of ordered
pairs $(a, a') \in A \times A$ with $a - a' = x$. For natural numbers $g$ and $n$, $\alpha_g(n)$
is the largest size of a set $A \subseteq [n] = \{1, \dots, n\}$ with $r_{A-A}(x) \le g$ for
every nonzero integer $x$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Sections 1 and 4. -/
public noncomputable def boundedDiffSetNumber (g n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℤ, A ⊆ Finset.Icc (1 : ℤ) n ∧ A.card = k ∧
    ∀ x : ℤ, x ≠ 0 → subRepCount A x ≤ g}

/-- **Representations of zero as a difference.** For every finite subset $A$ of an abelian
group, $r_{A-A}(0) = |A|$: the number of ordered pairs $(a, a') \in A \times A$ with
$a - a' = 0$ equals the number of elements of $A$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem subRepCount_zero {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    subRepCount A 0 = A.card := by
  rw [← Finset.diag_card A, Finset.diag_eq_filter]
  simp only [subRepCount, sub_eq_zero]

private theorem two_le_card_of_subRepCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} {x : G} (hx : x ≠ 0) (h : 1 ≤ subRepCount A x) : 2 ≤ A.card := by
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨h1, h2⟩, hpx⟩ := hp
  have hne : p.1 ≠ p.2 := fun he => hx (by rw [← hpx, he, sub_self])
  exact Finset.one_lt_card.mpr ⟨p.1, h1, p.2, h2, hne⟩

/-- **The value $\eta_1(1) = 2$.** Let $\eta_1(1)$ be the least size of a finite set
$A \subseteq \mathbb{Z}$ containing elements $a, a'$ with $a - a' = 1$. Then $\eta_1(1) = 2$: such a
set needs two elements, and $\{0, 1\}$ is one.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 1. -/
public theorem diffBasisNumber_one_one : diffBasisNumber 1 1 = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset ℤ, A.card = k ∧
      ∀ x ∈ Finset.Icc (1 : ℤ) (1 : ℕ), 1 ≤ subRepCount A x} := by
    refine ⟨{0, 1}, by decide, fun x hx => ?_⟩
    have : x = 1 := by simp at hx; omega
    subst this
    decide
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount one_ne_zero (hA 1 (by simp))

/-- **Difference basis number of $\mathbb{Z}/3\mathbb{Z}$.** The least size
$\eta_1(\mathbb{Z}/3\mathbb{Z})$ of a set $A \subseteq \mathbb{Z}/3\mathbb{Z}$ such that every
element of $\mathbb{Z}/3\mathbb{Z}$ is a difference $a - a'$ of two elements of $A$ equals $2$:
the set $\{0, 1\}$ has differences $0, 1, 2$, and one element is not enough.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 3. -/
public theorem groupDiffBasisNumber_one_zmod_three : groupDiffBasisNumber 1 (ZMod 3) = 2 := by
  have hmem : 2 ∈ {k | ∃ A : Finset (ZMod 3), A.card = k ∧
      ∀ x : ZMod 3, 1 ≤ subRepCount A x} := ⟨{0, 1}, by decide, by decide⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨2, hmem⟩ ?_)
  rintro k ⟨A, rfl, hA⟩
  exact two_le_card_of_subRepCount (by decide) (hA 1)

/-- **Trivial upper bound for sets with bounded difference multiplicities.** For natural numbers
$g$ and $n$, let $\alpha_g(n)$ be the largest size of a set $A \subseteq [n] = \{1, \dots, n\}$
such that every nonzero integer $x$ is the difference $a - a'$ of at most $g$ ordered pairs
$(a, a') \in A \times A$. Then $\alpha_g(n) \le n$, since these sets are subsets of $[n]$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_le (g n : ℕ) : boundedDiffSetNumber g n ≤ n := by
  refine csSup_le ⟨0, ∅, by simp, by simp, by simp [subRepCount]⟩ ?_
  rintro k ⟨A, hA, rfl, -⟩
  simpa using Finset.card_le_card hA

/-- **The value $\alpha_g(1) = 1$.** For natural numbers $g$ and $n$, let $\alpha_g(n)$ be the
largest size of a set $A \subseteq \{1, \dots, n\}$ such that every nonzero integer $x$ is the
difference $a - a'$ of at most $g$ ordered pairs $(a, a') \in A \times A$. Then for every natural
number $g$ we have $\alpha_g(1) = 1$: the singleton $\{1\}$ has no nonzero differences.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Section 4. -/
public theorem boundedDiffSetNumber_one (g : ℕ) : boundedDiffSetNumber g 1 = 1 := by
  refine le_antisymm (boundedDiffSetNumber_le g 1) (le_csSup ⟨1, ?_⟩ ?_)
  · rintro k ⟨A, hA, rfl, -⟩
    simpa using Finset.card_le_card hA
  · refine ⟨{1}, by simp, rfl, fun x hx => ?_⟩
    have : subRepCount ({1} : Finset ℤ) x = 0 := by
      simp [subRepCount, Finset.filter_singleton, Ne.symm hx]
    omega

/-- **Trivial lower bound for difference bases of an interval.** Let $g, n \in \mathbb{N}$ with
$n > 1$, and let $\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that
every $x \in \{1, \dots, n\}$ equals $a - a'$ for at least $g$ ordered pairs
$(a, a') \in A \times A$. Then $\eta_g(n) / \sqrt{n} \ge \sqrt{2g}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 1 (`integers-2025-A77-lem-1`). -/
public theorem_wanted sqrt_two_mul_le_diffBasisNumber_div_sqrt (g n : ℕ) (hn : 1 < n) :
    Real.sqrt (2 * g) ≤ (diffBasisNumber g n : ℝ) / Real.sqrt n

/-- **Rédei–Rényi difference basis.** Let $n \ge 1$ and $k = \lceil \sqrt{n} \rceil$. The set
of integers $B_n = \{1, \dots, k - 1\} \cup \{k, 2k, \dots, k^2, (k + 1)k\}$ has $2k$ elements,
and every $x \in \{1, \dots, n\}$ is a difference $b - b'$ of two elements of $B_n$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 2 (`integers-2025-A77-lem-2`). -/
public theorem_wanted redeiRenyi_diffBasis (n : ℕ) (hn : 0 < n) :
    let k : ℕ := ⌈Real.sqrt n⌉₊
    let B : Finset ℤ :=
      Finset.Icc 1 ((k : ℤ) - 1) ∪ (Finset.Icc (1 : ℤ) (k + 1)).image (· * (k : ℤ))
    B.card = 2 * k ∧ ∀ x ∈ Finset.Icc (1 : ℤ) n, 1 ≤ subRepCount B x

/-- **Upper bound for the $g$-difference basis number.** For natural numbers $g$ and $n$, let
$\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, n\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. Then for all natural numbers $g$ and $n$,

$$\frac{\eta_g(n)}{\sqrt{n}} \le 2\left(1 + \frac{1}{\sqrt{n}}\right) g,$$

where for $n = 0$ both quotients are read with the convention that division by $0$ gives $0$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 1 (`integers-2025-A77-cor-1`). -/
public theorem_wanted diffBasisNumber_div_sqrt_le (g n : ℕ) :
    (diffBasisNumber g n : ℝ) / Real.sqrt n ≤ 2 * (1 + 1 / Real.sqrt n) * g

/-- **Comparing $g$-difference bases with difference bases.** For natural numbers $g$ and $n$,
let $\eta_g(n)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, n\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. If $n > 1$ and $g \ge 1$, then
$\eta_1(n) \le \eta_g(n) \le g\,\eta_1(n)$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 2 (`integers-2025-A77-cor-2`). -/
public theorem_wanted diffBasisNumber_one_le_and_le_mul (g n : ℕ) (hn : 1 < n) (hg : 1 ≤ g) :
    diffBasisNumber 1 n ≤ diffBasisNumber g n ∧ diffBasisNumber g n ≤ g * diffBasisNumber 1 n

/-- **Kravitz's question: the normalized difference basis numbers converge.** For a finite set
$A$ of integers and an integer $x$, write $r_{A-A}(x)$ for the number of ordered pairs
$(a, a') \in A \times A$ with $a - a' = x$. For every integer $g \ge 1$, let $\eta_g(n)$ be the
least size of a finite set $A$ of integers with $r_{A-A}(x) \ge g$ for every integer
$x \in [1, n]$. Then there is a real number $c > 0$ with $\eta_g(n) / \sqrt{n} \to c$ as
$n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 1 (`integers-2025-A77-thm-1`). -/
public theorem_wanted tendsto_diffBasisNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (diffBasisNumber g n : ℝ) / Real.sqrt n) atTop (𝓝 c)

/-- **Singer product construction of difference bases.** Let $g, q, v \in \mathbb{N}$ and
$m = q^2 + q + 1$. Let $a_0, \dots, a_q$ be integers in $\{1, \dots, m\}$ such that every
$r \in \{1, \dots, m - 1\}$ is congruent modulo $m$ to $a_i - a_j$ for exactly one ordered pair
$(i, j)$ with $i \ne j$ (a Singer difference set modulo $m$). Let $B$ be a finite set of
integers such that every $x \in \{1, \dots, v\}$ equals $b - b'$ for at least $g$ ordered pairs
$(b, b') \in B \times B$. Then, with $F = \{a_i + mb : 0 \le i \le q,\ b \in B\}$, every
$s \in \{1, \dots, mv\}$ equals $f - f'$ for at least $g$ ordered pairs $(f, f') \in F \times F$.

All $q + 1$ Singer elements are used; the paper prints $1 \le i \le q$, for which the statement
fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 4 (`integers-2025-A77-lem-4`). -/
public theorem_wanted singer_product_diffBasis (g q v : ℕ) (a : Fin (q + 1) → ℤ)
    (ha : ∀ i, a i ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q + 1))
    (hsinger : ∀ r ∈ Finset.Icc (1 : ℤ) (q ^ 2 + q),
      ∃! ij : Fin (q + 1) × Fin (q + 1),
        ij.1 ≠ ij.2 ∧ a ij.1 - a ij.2 ≡ r [ZMOD (q ^ 2 + q + 1 : ℤ)])
    (B : Finset ℤ) (hB : ∀ x ∈ Finset.Icc (1 : ℤ) v, g ≤ subRepCount B x) :
    ∀ s ∈ Finset.Icc (1 : ℤ) ((q ^ 2 + q + 1) * v),
      g ≤ subRepCount
        ((Finset.univ ×ˢ B).image fun ib : Fin (q + 1) × ℤ => a ib.1 + (q ^ 2 + q + 1) * ib.2) s

/-- **Scaling bound for the $g$-difference basis number.** For natural numbers $g$ and $m$, let
$\eta_g(m)$ be the least size of a finite set $A \subseteq \mathbb{Z}$ such that every
$x \in \{1, \dots, m\}$ is the difference $a - a'$ of at least $g$ ordered pairs
$(a, a') \in A \times A$. If $q$ is a prime and $n$ and $v$ are natural numbers with
$n \le q^2 v$, then $\eta_g(n) \le (q + 1)\,\eta_g(v)$.

For $v \ge 1$ the hypothesis $n \le q^2 v$ says $\sqrt{n/v} \le q$. Corrected reading: the paper
prints the factor $q$, obtained from the misprinted Lemma 4; its proof gives $q + 1$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Corollary 3 (`integers-2025-A77-cor-3`). -/
public theorem_wanted diffBasisNumber_le_succ_mul (g q n v : ℕ) (hq : q.Prime)
    (hn : n ≤ q ^ 2 * v) :
    diffBasisNumber g n ≤ (q + 1) * diffBasisNumber g v

/-- **Products of difference bases.** Let $G_1, G_2$ be abelian groups, $g_1, g_2 \in \mathbb{N}$,
and $A_1 \subseteq G_1$, $A_2 \subseteq G_2$ finite sets. If every element of $G_1$ equals $a - a'$
for at least $g_1$ ordered pairs $(a, a') \in A_1 \times A_1$, and every element of $G_2$ equals
$a - a'$ for at least $g_2$ ordered pairs $(a, a') \in A_2 \times A_2$, then every element of
$G_1 \times G_2$ equals $z - z'$ for at least $g_1 g_2$ ordered pairs
$(z, z') \in (A_1 \times A_2) \times (A_1 \times A_2)$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem_wanted subRepCount_prod_ge {G₁ G₂ : Type*} [AddCommGroup G₁] [AddCommGroup G₂]
    [DecidableEq G₁] [DecidableEq G₂] (g₁ g₂ : ℕ) (A₁ : Finset G₁) (A₂ : Finset G₂)
    (h₁ : ∀ x, g₁ ≤ subRepCount A₁ x) (h₂ : ∀ x, g₂ ≤ subRepCount A₂ x) :
    ∀ x : G₁ × G₂, g₁ * g₂ ≤ subRepCount (A₁ ×ˢ A₂) x

/-- **Difference bases of the integers modulo a prime.** For every prime $p$, the least size
$\eta_1(\mathbb{Z}/p\mathbb{Z})$ of a set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ such that every
residue modulo $p$ is a difference $a - a'$ of two elements of $A$ satisfies
$\eta_1(\mathbb{Z}/p\mathbb{Z}) \le 2 \lceil \sqrt{p} \rceil$.

The bound comes from reducing the Rédei–Rényi set modulo $p$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, equation (5) after Lemma 5 (`integers-2025-A77-lem-5`). -/
public theorem_wanted groupDiffBasisNumber_zmod_le (p : ℕ) [Fact p.Prime] :
    groupDiffBasisNumber 1 (ZMod p) ≤ 2 * ⌈Real.sqrt p⌉₊

/-- **Difference bases of the square of a finite field.** For an abelian group $G$ let
$\eta_1(G)$ be the least size of a set $A \subseteq G$ such that every element of $G$ is a
difference $a - a'$ of two elements of $A$. If $K$ is a finite field with $q$ elements whose
characteristic is not $2$, then $\eta_1(K \times K) \le q + \eta_1(K)$, where $K$ and
$K \times K$ are taken as additive groups.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 6 (`integers-2025-A77-lem-6`). -/
public theorem_wanted groupDiffBasisNumber_prod_self_le {K : Type*} [Field K] [Finite K]
    [DecidableEq K] (hK : ringChar K ≠ 2) :
    groupDiffBasisNumber 1 (K × K) ≤ Nat.card K + groupDiffBasisNumber 1 K

/-- **Square-root bound for difference bases of finite fields.** For every finite field $K$ with
$q$ elements, the least size $\eta_1(K)$ of a set $A \subseteq K$ such that every element of $K$
is a difference $a - a'$ of two elements of $A$ satisfies $\eta_1(K) \le 100 \sqrt{q}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 7 (`integers-2025-A77-lem-7`). -/
public theorem_wanted groupDiffBasisNumber_le_hundred_sqrt {K : Type*} [Field K] [Finite K]
    [DecidableEq K] :
    (groupDiffBasisNumber 1 K : ℝ) ≤ 100 * Real.sqrt (Nat.card K)

open Classical in
/-- **Difference bases of $\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}$.** Let $p$ be an odd prime.
For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write $r_{A-A}(x)$ for the
number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let $\eta_1(G)$ be the
least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge 1$ for every $x \in G$. Then
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) / p^t \to 1$ as $t \to \infty$, that is,
$\eta_1(\mathbb{F}_{p^t} \times \mathbb{F}_{p^t}) = (1 + o(1))\, p^t$, where $\mathbb{F}_{p^t}$
is the field with $p^t$ elements.

The restriction to odd $p$ is deliberate: for $p = 2$ the claim fails.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 8 (`integers-2025-A77-lem-8`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_galoisField_prod (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) :
    Tendsto (fun t : ℕ =>
        (groupDiffBasisNumber 1 (GaloisField p t × GaloisField p t) : ℝ) / (p : ℝ) ^ t)
      atTop (𝓝 1)

/-- **Even and odd limits for difference bases of $\mathbb{F}_p^n$.** Let $p$ be an odd prime and
$g \ge 1$ an integer. For a finite abelian group $G$, a set $A \subseteq G$ and $x \in G$, write
$r_{A-A}(x)$ for the number of ordered pairs $(a, a') \in A \times A$ with $a - a' = x$, and let
$\eta_g(G)$ be the least size of a set $A \subseteq G$ with $r_{A-A}(x) \ge g$ for every $x \in G$.
Then there are real numbers $L_e > 0$ and $L_o > 0$ such that, as $k \to \infty$,
$\eta_g(\mathbb{F}_p^{2k}) / \sqrt{p^{2k}} \to L_e$ and
$\eta_g(\mathbb{F}_p^{2k+1}) / \sqrt{p^{2k+1}} \to L_o$, where $\mathbb{F}_p^n$ is the additive
group of $n$-tuples over the field $\mathbb{F}_p$ with $p$ elements.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 2 (`integers-2025-A77-thm-2`). -/
public theorem_wanted tendsto_groupDiffBasisNumber_even_odd (p g : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hg : 0 < g) :
    (∃ Le : ℝ, 0 < Le ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k) → ZMod p) : ℝ) / Real.sqrt ((p : ℝ) ^ (2 * k)))
      atTop (𝓝 Le)) ∧
    (∃ Lo : ℝ, 0 < Lo ∧ Tendsto (fun k : ℕ =>
        (groupDiffBasisNumber g (Fin (2 * k + 1) → ZMod p) : ℝ) /
          Real.sqrt ((p : ℝ) ^ (2 * k + 1)))
      atTop (𝓝 Lo))

/-- **Nonzero differences of the Bose–Chowla set avoid the subgroup of order $g$.** Let $q$
and $g$ be natural numbers with $g \mid q - 1$, let $K$ be a finite field with $q^2$ elements, and
let $\theta \in K$ be a primitive $(q^2 - 1)$-th root of unity, that is, a generator of $K^\times$.
If $a$ and $b$ are natural numbers less than $q^2 - 1$ with
$(\theta^a - \theta)^q = \theta^a - \theta$ and $(\theta^b - \theta)^q = \theta^b - \theta$, and
$(q^2 - 1)/g$ divides $a - b$, then $a = b$.

Equivalently, let $\mathbb{F}_q = \{x \in K : x^q = x\}$, let
$B_q = \{a \in \mathbb{Z}/(q^2 - 1) : \theta^a - \theta \in \mathbb{F}_q\}$ be the Bose–Chowla set
and let $H$ be the subgroup of $\mathbb{Z}/(q^2 - 1)$ generated by $(q^2 - 1)/g$; then
$(B_q - B_q) \cap H = \{0\}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Lemma 9 (`integers-2025-A77-lem-9`), quoting Bose–Chowla and
Brandão–Debarre–Tait / Gómez–Trujillo–Tait. -/
public theorem_wanted boseChowla_sub_mem_subgroup_eq {K : Type*} [Field K] [Finite K]
    (q g : ℕ) (hK : Nat.card K = q ^ 2) (hgq : g ∣ q - 1) (θ : K)
    (hθ : IsPrimitiveRoot θ (q ^ 2 - 1)) (a b : ℕ) (ha : a < q ^ 2 - 1) (hb : b < q ^ 2 - 1)
    (hBa : (θ ^ a - θ) ^ q = θ ^ a - θ) (hBb : (θ ^ b - θ) ^ q = θ ^ b - θ)
    (hab : (((q ^ 2 - 1) / g : ℕ) : ℤ) ∣ (a : ℤ) - b) :
    a = b

/-- **Upper bound for sets with bounded difference multiplicities.** For natural numbers $g$ and
$n$, let $\alpha_g(n)$ be the largest size of a set $A \subseteq \{1, \dots, n\}$ such that every
nonzero integer $x$ is the difference $a - a'$ of at most $g$ ordered pairs
$(a, a') \in A \times A$. If $g \ge 1$, then for every real $\varepsilon > 0$ we have
$\alpha_g(n) \le (1 + \varepsilon)\sqrt{gn}$ for all sufficiently large $n$; that is,
$\alpha_g(n) \le (1 + o(1))\sqrt{gn}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 1 (`integers-2025-A77-prop-1`). -/
public theorem_wanted boundedDiffSetNumber_le_one_add_mul_sqrt (g : ℕ) (hg : 0 < g) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (boundedDiffSetNumber g n : ℝ) ≤ (1 + ε) * Real.sqrt (g * n)

/-- **Lower-bound construction for sets with bounded difference multiplicities.** For every
integer $g \ge 1$ there are finite sets $A_n \subseteq \{1, \dots, n\}$ of integers, one for each
$n \in \mathbb{N}$, such that for every $n$ each nonzero integer $x$ equals $a - a'$ for at most
$g$ ordered pairs $(a, a') \in A_n \times A_n$, and $|A_n| / \sqrt{gn} \to 1$ as $n \to \infty$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Proposition 2 (`integers-2025-A77-prop-2`). -/
public theorem_wanted exists_boundedDiffSet_card_div_sqrt_tendsto (g : ℕ) (hg : 0 < g) :
    ∃ A : ℕ → Finset ℤ,
      (∀ n, A n ⊆ Finset.Icc (1 : ℤ) n ∧ ∀ x : ℤ, x ≠ 0 → subRepCount (A n) x ≤ g) ∧
      Tendsto (fun n : ℕ => ((A n).card : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

/-- **Asymptotics of the largest sets with bounded difference counts.** For a finite set $A$ of
integers and an integer $x$, write $r_{A-A}(x)$ for the number of ordered pairs
$(a, a') \in A \times A$ with $a - a' = x$. For every integer $g \ge 1$, let $\alpha_g(n)$ be the
largest size of a set $A$ of integers in the interval $[1, n]$ with $r_{A-A}(x) \le g$ for every
nonzero integer $x$. Then $\alpha_g(n) / \sqrt{gn} \to 1$ as $n \to \infty$, that is,
$\alpha_g(n) = (1 + o_g(1)) \sqrt{gn}$.

Source: Eric Schmutz and Michael Tait, *Cardinalities of g-Difference Sets*, INTEGERS 25
(2025), Article A77, Theorem 3 (`integers-2025-A77-thm-3`). -/
public theorem_wanted tendsto_boundedDiffSetNumber_div_sqrt (g : ℕ) (hg : 0 < g) :
    Tendsto (fun n : ℕ => (boundedDiffSetNumber g n : ℝ) / Real.sqrt (g * n)) atTop (𝓝 1)

end

end MetaMathlibExt
