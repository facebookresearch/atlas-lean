/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Homomesy of antichain cardinality under type-A rowmotion
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Antichain

@[expose] public section

namespace MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted

/-! Source record `AIM-OTHER-0019__20003212`. -/

/-!
# AIM-OTHER-0019: Type-A antichain rowmotion homomesy

Conjecture 3.3 from aim-other-notes.json notes[18]
(AIM Problem Lists, Dynamical algebraic combinatorics,
http://aimath.org/pastworkshops/dac_preworkshop.pdf).

Clause list for the formalized claim (Conjecture 3.3 only; birational remarks
for n ≤ 3 and Theorem 3.4 are context evidence, not additional targets):
- (n : ℕ): index of the type-A root poset; no lower-bound exclusion in source.
- (P : Type*) [PartialOrder P] [Finite P]: finite poset domain.
- IsTypeARootPoset P n: P is order-isomorphic to triangular pairs
  {(i,j) : Fin n × Fin n // i ≤ j} with interval-inclusion order
  (a ≤ b ↔ b.1 ≤ a.1 ∧ a.2 ≤ b.2).
- PosetAntichain P: antichains of P as Finsets satisfying IsAntichain (· ≤ ·).
- rhoPrime : PosetAntichain P → PosetAntichain P: antichain rowmotion;
  bijective with defining equation x ∈ rhoPrime(A) ↔ x minimal in complement
  of down-set of A.
- f : PosetAntichain P → ℚ: antichain-cardinality statistic; f(A) = |A|.
- IsHomomesic rhoPrime f c: Finite domain, bijective action, and one shared
  orbit-average c for every x and every period k > 0 with iterate k x = x.
- c = (n : ℚ) / 2: exact average value n/2.
-/

open scoped BigOperators

/-- **Homomesy.** Let $X$ be a type, $\sigma \colon X \to X$ a map, $f \colon X \to \mathbb{Q}$ a
function and $c \in \mathbb{Q}$. Then $f$ is homomesic under $\sigma$ with average $c$ when $X$ is
finite, $\sigma$ is bijective, and for every $x \in X$ and every $k > 0$ with $\sigma^k(x) = x$
the average $\frac{1}{k} \sum_{i=0}^{k-1} f(\sigma^i(x))$ equals $c$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsHomomesic {α : Type*} (σ : α → α) (f : α → ℚ) (c : ℚ) : Prop :=
  Finite α ∧
  Function.Bijective σ ∧
  ∀ (x : α) (k : ℕ), 0 < k → Nat.iterate σ k x = x →
    (Finset.sum (Finset.range k) (fun i => f (Nat.iterate σ i x))) / (k : ℚ) = c

/-- **Finite antichains of a poset.** For a partially ordered set $P$, the finite antichains of
$P$ are the finite subsets $A \subseteq P$ in which no element is below a different element.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def PosetAntichain (P : Type*) [PartialOrder P] :=
  { s : Finset P // IsAntichain (· ≤ ·) (s : Set P) }

/-- **Antichain cardinality statistic.** For a partially ordered set $P$, a function $f$ from the
finite antichains of $P$ to $\mathbb{Q}$ is the antichain cardinality statistic when
$f(A) = |A|$ for every finite antichain $A$ of $P$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainCardinality (P : Type*) [PartialOrder P]
    (f : PosetAntichain P → ℚ) : Prop :=
  ∀ A : PosetAntichain P, f A = (A.val.card : ℚ)

/-- **Rowmotion on antichains.** For a partially ordered set $P$, a map $\rho$ from the finite
antichains of $P$ to themselves is antichain rowmotion when $\rho$ is bijective and, for every
finite antichain $A$, $\rho(A)$ is the set of minimal elements of the complement of the down-set
of $A$: an element $x \in P$ lies in $\rho(A)$ exactly when $x \not\le a$ for all $a \in A$ and
every $y \le x$ with $y \not\le a$ for all $a \in A$ equals $x$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsAntichainRowmotion (P : Type*) [PartialOrder P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) : Prop :=
  Function.Bijective rhoPrime ∧
  ∀ (A : PosetAntichain P) (x : P),
    x ∈ (rhoPrime A).val ↔
      ((¬ ∃ a ∈ A.val, x ≤ a) ∧
        ∀ (y : P), (¬ ∃ a ∈ A.val, y ≤ a) → y ≤ x → y = x)

/-- **Type-A root poset.** A partially ordered set $P$ is a type-A root poset of rank $n$, for a
natural number $n$, when there is a bijection $a \mapsto (i_a, j_a)$ from $P$ onto the set of
pairs $(i, j)$ of integers with $0 \le i \le j < n$ such that $a \le b$ holds exactly when the
interval $[i_a, j_a]$ is contained in $[i_b, j_b]$, that is, $i_b \le i_a$ and $j_a \le j_b$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def IsTypeARootPoset (P : Type*) [PartialOrder P] (n : ℕ) : Prop :=
  ∃ e : P ≃ { p : Fin n × Fin n // p.1 ≤ p.2 },
    ∀ (a b : P), a ≤ b ↔
      ((e b).val.1 ≤ (e a).val.1 ∧ (e a).val.2 ≤ (e b).val.2)

/-- **Type-A rowmotion homomesy conjecture.** The proposition that for every natural number $n$,
every finite partially ordered set $P$ that is a type-A root poset of rank $n$ (there is a
bijection $a \mapsto (i_a, j_a)$ from $P$ onto the set of pairs $(i, j)$ of integers with
$0 \le i \le j < n$ such that $a \le b$ holds exactly when $i_b \le i_a$ and $j_a \le j_b$), and
every bijection $\rho$ of the set of finite antichains of $P$ that sends each antichain $A$ to the
set of minimal elements of the complement of the down-set of $A$, the set of finite antichains of
$P$ is finite, $\rho$ is bijective, and for every antichain $A$ and every $k > 0$ with
$\rho^k(A) = A$ the average $\frac{1}{k} \sum_{i=0}^{k-1} |\rho^i(A)|$ equals $n/2$.

Source: [AIM-OTHER-0019] Conjecture 3.3 (aim-other-notes.json notes[18];
http://aimath.org/pastworkshops/dac_preworkshop.pdf). -/
def conjecture : Prop :=
  ∀ (n : ℕ) (P : Type*) [PartialOrder P] [Finite P]
    (rhoPrime : PosetAntichain P → PosetAntichain P) (f : PosetAntichain P → ℚ),
    IsTypeARootPoset P n →
      IsAntichainRowmotion P rhoPrime →
        IsAntichainCardinality P f →
          IsHomomesic rhoPrime f ((n : ℚ) / 2)

/--
**Antichain size is homomesic under type-A rowmotion.** Let $n$ be a natural number and let $P$
be a finite partially ordered set that is a type-A root poset of rank $n$: there is a bijection
$a \mapsto (i_a, j_a)$ from $P$ onto the set of pairs $(i, j)$ of integers with $0 \le i \le j < n$
such that $a \le b$ holds exactly when $[i_a, j_a] \subseteq [i_b, j_b]$, that is, $i_b \le i_a$
and $j_a \le j_b$. Let $\rho$ be a bijection of the set of finite antichains of $P$ such that,
for every antichain $A$, $\rho(A)$ is the set of minimal elements of the complement of the
down-set of $A$. Then the set of finite antichains of $P$ is finite, $\rho$ is bijective, and for
every antichain $A$ and every $k > 0$ with $\rho^k(A) = A$,
$$\frac{1}{k} \sum_{i=0}^{k-1} |\rho^i(A)| = \frac{n}{2}.$$

This is the type-A case of Panyushev's conjecture on antichain orbits in root posets, which
Armstrong, Stump, and Thomas proved for all crystallographic root systems.

Source: D. Armstrong, C. Stump, and H. Thomas, A
uniform bijection between nonnesting and noncrossing partitions, Transactions of the American
Mathematical Society 365 (2013). Moved from
`OpenConjectures/Combinatorics/RootPosetRowmotionHomomesy`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.RootPosetRowmotionHomomesyWanted
