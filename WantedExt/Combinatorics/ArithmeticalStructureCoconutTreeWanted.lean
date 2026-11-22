/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat

namespace MetaMathlibExt

@[expose] public section

/-! Statements from Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith,
*Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82
(preprint arXiv:2406.11183, whose text supplies the definitions).

The coconut tree `CT(p, s)` has vertex type `Fin p ⊕ Fin s`: the path vertex
`v_{i+1}` is `.inl i` and the leaf `v_{ℓ_{j+1}}` is `.inr j`; the central vertex
`v_p` is `.inl ⟨p - 1, _⟩`. A structure `(d, r)` is a pair of labelings of the
vertices. Counts `|Arith(G)|` and `|SArith(G)|` are `Set.ncard` of the sets of
pairs `(d, r)`. -/

/-- An arithmetical structure on a graph `G`: positive labelings `d` and `r`
with `(diag(d) - A) r = 0`, i.e. `d_v r_v = ∑_{w ∼ v} r_w` for every vertex,
and the entries of `r` have no common factor other than `1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public def IsArithmeticalStructure {V : Type*} (G : SimpleGraph V) (d r : V → ℕ) : Prop :=
  (∀ v, 0 < d v) ∧ (∀ v, 0 < r v) ∧
    (∀ v, d v * r v = ∑ᶠ w ∈ {w | G.Adj v w}, r w) ∧
    ∀ g : ℕ, (∀ v, g ∣ r v) → g = 1

/-- On a single edge, `d = r = (1, 1)` is an arithmetical structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public theorem isArithmeticalStructure_top_fin_two :
    IsArithmeticalStructure (⊤ : SimpleGraph (Fin 2)) 1 1 := by
  refine ⟨fun _ => one_pos, fun _ => one_pos, fun v => ?_, fun g hg => Nat.dvd_one.mp (hg 0)⟩
  rcases (show v = 0 ∨ v = 1 by fin_cases v <;> simp) with rfl | rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 0 w} = {1} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 1 w} = {0} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl

/-- The coconut tree `CT(p, s)`: a path `v_1 - v_2 - ⋯ - v_p` together with `s`
leaves `v_{ℓ_1}, …, v_{ℓ_s}`, each adjacent to `v_p`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public def coconutTree (p s : ℕ) : SimpleGraph (Fin p ⊕ Fin s) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | .inl i, .inl j => i.val + 1 = j.val
    | .inl i, .inr _ => i.val + 1 = p
    | .inr _, _ => False

/-- Path vertices of `CT(p, s)` are adjacent exactly when consecutive.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inl {p s : ℕ} (i j : Fin p) :
    (coconutTree p s).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [coconutTree, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨fun hij => ?_, h⟩
    subst hij
    omega

/-- A leaf of `CT(p, s)` is adjacent to the path vertex `v_{i+1}` exactly when
`i + 1 = p`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inr {p s : ℕ} (i : Fin p) (j : Fin s) :
    (coconutTree p s).Adj (.inl i) (.inr j) ↔ i.val + 1 = p := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- Leaves of `CT(p, s)` are pairwise nonadjacent.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_not_adj_inr_inr {p s : ℕ} (j j' : Fin s) :
    ¬(coconutTree p s).Adj (.inr j) (.inr j') := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- A smooth arithmetical structure on `CT(p, s)`: an arithmetical structure
with `d_1, …, d_{p-1}, d_{ℓ_1}, …, d_{ℓ_s} ≥ 2` (no condition on `d_p`).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public def IsSmoothCoconut (p s : ℕ) (d r : Fin p ⊕ Fin s → ℕ) : Prop :=
  IsArithmeticalStructure (coconutTree p s) d r ∧
    (∀ i : Fin p, i.val + 1 < p → 2 ≤ d (.inl i)) ∧ ∀ j, 2 ≤ d (.inr j)

/-- A smooth structure has every leaf label `d_{ℓ_j} ≥ 2`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public theorem IsSmoothCoconut.two_le_leaf {p s : ℕ} {d r : Fin p ⊕ Fin s → ℕ}
    (h : IsSmoothCoconut p s d r) (j : Fin s) : 2 ≤ d (.inr j) :=
  h.2.2 j

/-- The ballot number `B(n, k) = (n - k + 1) / (n + 1) · binom(n + k, n)`
(OEIS A009766), written with truncated subtraction and exact division for
`k ≤ n + 1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public def ballotNumber (n k : ℕ) : ℕ :=
  (n + 1 - k) * (n + k).choose n / (n + 1)

/-- `B(n, 0) = 1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_zero_right (n : ℕ) : ballotNumber n 0 = 1 := by
  simp [ballotNumber]

/-- `B(n, n) = C_n`, the Catalan number.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_self (n : ℕ) : ballotNumber n n = catalan n := by
  rw [ballotNumber, show n + 1 - n = 1 by omega, one_mul, ← two_mul,
    ← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom,
    Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- The term `A(x, y)` of Theorem 1: `A(x, 0) = C_{x-1}`,
`A(x, 1) = C_{x-1} - C_{x-2}` and, for `y ≥ 2`,
`A(x, y) = ∑_{i=y+1}^{x} B(x - y - 1, x - i) |SArith(CT(i - y, y))|`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public noncomputable def coconutCountTerm (x y : ℕ) : ℕ :=
  if y = 0 then catalan (x - 1)
  else if y = 1 then catalan (x - 1) - catalan (x - 2)
  else ∑ i ∈ Finset.Icc (y + 1) x, ballotNumber (x - y - 1) (x - i) *
    Set.ncard {z : (Fin (i - y) ⊕ Fin y → ℕ) × (Fin (i - y) ⊕ Fin y → ℕ) |
      IsSmoothCoconut (i - y) y z.1 z.2}

/-- `A(x, 0) = C_{x-1}`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public theorem coconutCountTerm_zero (x : ℕ) : coconutCountTerm x 0 = catalan (x - 1) := by
  simp [coconutCountTerm]

/-- The Euclidean chain function `F(x_1, x_2)`: the number of positive terms
of the Euclidean chain `x_1, x_2, x_3, …` with
`x_{i+1} = (-x_{i-1}) mod x_i` (least nonnegative residue) while `x_i ≠ 0`, and
`0` afterwards; so `F(x, 0) = 1` and `F(x, y) = 1 + F(y, (-x) mod y)` for
`y ≠ 0`. This count of positive terms is the meaning for `x > 0`, the source's
domain. For `x = 0` the recursion is a totalization that also counts the first
term `0` (`F(0, 0) = 1`, `F(0, 1) = 2`, while the chains `0, 0` and `0, 1, 0`
have `0` and `1` positive terms); no wanted statement uses `x = 0`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public def euclideanChainLength (x y : ℕ) : ℕ :=
  if h : y = 0 then 1 else 1 + euclideanChainLength y ((y - x % y) % y)
termination_by y
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- `F(x, 0) = 1` (for `x = 0` this is the totalized value, see `euclideanChainLength`).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_zero (x : ℕ) : euclideanChainLength x 0 = 1 := by
  rw [euclideanChainLength]
  simp

/-- `F(x, y) = 1 + F(y, (-x) mod y)` for `y ≠ 0`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_of_ne_zero (x : ℕ) {y : ℕ} (hy : y ≠ 0) :
    euclideanChainLength x y = 1 + euclideanChainLength y ((y - x % y) % y) := by
  rw [euclideanChainLength]
  simp [hy]

/-- Example 4.13: `F(13, 60) = 8`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 4.13
(arXiv numbering). -/
public theorem euclideanChainLength_thirteen_sixty : euclideanChainLength 13 60 = 8 := by
  simp [euclideanChainLength_of_ne_zero, euclideanChainLength_zero]

/-- Lemma 1: for an arithmetical structure on `CT(p, s)` the following are
equivalent: (1) `d_i ≥ 2` for `1 ≤ i ≤ p - 1`; (2)
`0 < r_2 - r_1 ≤ r_3 - r_2 ≤ ⋯ ≤ r_p - r_{p-1}`; (3) `r_1 < r_2 < ⋯ < r_p`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 1
(`integers-2025-A82-lem-1`). -/
public theorem_wanted IsArithmeticalStructure.coconut_tfae {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsArithmeticalStructure (coconutTree p s) d r) :
    [∀ i : Fin p, i.val + 1 < p → 2 ≤ d (.inl i),
      (∀ hp : 1 < p, r (.inl ⟨0, by omega⟩) < r (.inl ⟨1, hp⟩)) ∧
        ∀ (i : ℕ) (hi : i + 2 < p),
          (r (.inl ⟨i + 1, by omega⟩) : ℤ) - r (.inl ⟨i, by omega⟩)
            ≤ (r (.inl ⟨i + 2, hi⟩) : ℤ) - r (.inl ⟨i + 1, by omega⟩),
      StrictMono fun i : Fin p => r (.inl i)].TFAE

/-- Lemma 2: an arithmetical structure on `CT(p, s)` (`p ≥ 1`) is smooth if
and only if `r_{ℓ_j} < r_p` for all `j` and `r_1 < r_2 < ⋯ < r_p`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 2
(`integers-2025-A82-lem-2`). -/
public theorem_wanted IsArithmeticalStructure.isSmoothCoconut_iff {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (hp : 0 < p)
    (h : IsArithmeticalStructure (coconutTree p s) d r) :
    IsSmoothCoconut p s d r ↔
      (∀ j, r (.inr j) < r (.inl ⟨p - 1, by omega⟩)) ∧ StrictMono fun i : Fin p => r (.inl i)

/-- Lemma 3: in a smooth arithmetical structure on `CT(p, s)` the leaf labels
`r_{ℓ_1}, …, r_{ℓ_s}` have no common factor other than `1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 3
(`integers-2025-A82-lem-3`). -/
public theorem_wanted IsSmoothCoconut.eq_one_of_dvd_leaves {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) {g : ℕ}
    (hg : ∀ j, g ∣ r (.inr j)) : g = 1

/-- Proposition 5: for `p ≥ 1`, the number of arithmetical structures on
`CT(p, 1) = P_{p+1}` whose leaf cannot be smoothed (`d_{ℓ_1} ≠ 1`) is
`C_p - C_{p-1}`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 5
(`integers-2025-A82-prop-5`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_one_leaf_ne_one {p : ℕ}
    (hp : 1 ≤ p) :
    Set.ncard {x : (Fin p ⊕ Fin 1 → ℕ) × (Fin p ⊕ Fin 1 → ℕ) |
      IsArithmeticalStructure (coconutTree p 1) x.1 x.2 ∧ x.1 (.inr 0) ≠ 1}
      = catalan p - catalan (p - 1)

/-- Theorem 1: for `p ≥ 1` and `s ≥ 2`,
`|Arith(CT(p, s))| = ∑_{j=0}^{s} binom(s, j) A(p + s - j, s - j)` with `A` as in
`coconutCountTerm`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1
(`integers-2025-A82-thm-1`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree {p s : ℕ} (hp : 1 ≤ p)
    (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2}
      = ∑ j ∈ Finset.range (s + 1), s.choose j * coconutCountTerm (p + s - j) (s - j)

/-- Corollary 2: for `p ≥ 2`,
`|Arith(CT(p, 2))| = 2 C_p - C_{p-1}
+ ∑_{i=3}^{p+2} B(p - 1, p + 2 - i) |SArith(CT(i - 2, 2))|`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 2
(`integers-2025-A82-cor-2`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_two {p : ℕ} (hp : 2 ≤ p) :
    Set.ncard {x : (Fin p ⊕ Fin 2 → ℕ) × (Fin p ⊕ Fin 2 → ℕ) |
      IsArithmeticalStructure (coconutTree p 2) x.1 x.2}
      = 2 * catalan p - catalan (p - 1) + ∑ i ∈ Finset.Icc 3 (p + 2),
          ballotNumber (p - 1) (p + 2 - i) *
            Set.ncard {z : (Fin (i - 2) ⊕ Fin 2 → ℕ) × (Fin (i - 2) ⊕ Fin 2 → ℕ) |
              IsSmoothCoconut (i - 2) 2 z.1 z.2}

/-- Corollary 3: for `s ≥ 2`, the star `S_s = CT(1, s)` has
`|Arith(CT(1, s))| = 1 + ∑_{j=0}^{s-2} binom(s, j) |SArith(S_{s-j})|`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 3
(`integers-2025-A82-cor-3`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_star {s : ℕ} (hs : 2 ≤ s) :
    Set.ncard {x : (Fin 1 ⊕ Fin s → ℕ) × (Fin 1 ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree 1 s) x.1 x.2}
      = 1 + ∑ j ∈ Finset.range (s - 1), s.choose j *
          Set.ncard {z : (Fin 1 ⊕ Fin (s - j) → ℕ) × (Fin 1 ⊕ Fin (s - j) → ℕ) |
            IsSmoothCoconut 1 (s - j) z.1 z.2}

/-- Proposition 6 (quoted from Archer et al.): for `x ≥ 1` and `y, k ≥ 0`,
`F(x + k y, y) = F(x, y)` and `F(x, k x + y) = F(x, y) + k`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 6
(`integers-2025-A82-prop-6`). -/
public theorem_wanted euclideanChainLength_add_mul {x : ℕ} (hx : 0 < x) (y k : ℕ) :
    euclideanChainLength (x + k * y) y = euclideanChainLength x y ∧
      euclideanChainLength x (k * x + y) = euclideanChainLength x y + k

/-- Corollary 4: for `x, y ≥ 1` with `x ∣ y`, `F(x, y) = 1 + y / x`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 4
(`integers-2025-A82-cor-4`). -/
public theorem_wanted euclideanChainLength_of_dvd {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ∣ y) : euclideanChainLength x y = 1 + y / x

/-- Corollary 5: `F(1, y) = y + 1` for `y ≥ 0`, and `F(x, 1) = 2` for `x ≥ 1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 5
(`integers-2025-A82-cor-5`). -/
public theorem_wanted euclideanChainLength_one_left_and_one_right (y : ℕ) {x : ℕ}
    (hx : 0 < x) :
    euclideanChainLength 1 y = y + 1 ∧ euclideanChainLength x 1 = 2

/-- Proposition 7: for `s ≥ 1` and `(c, a_1, …, a_s) ∈ ℕ^{s+1}` with
`a_i ∣ c`, `a_i < c` and `gcd(c, a_1, …, a_s) = 1`, there is a unique `p ≥ 1`
admitting a smooth arithmetical structure on `CT(p, s)` with `r_{ℓ_i} = a_i` and
`r_p = c`, and that structure is unique.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 7
(`integers-2025-A82-prop-7`). -/
public theorem_wanted existsUnique_isSmoothCoconut {s : ℕ} (hs : 1 ≤ s) {c : ℕ}
    (a : Fin s → ℕ) (ha : ∀ i, 0 < a i) (hdvd : ∀ i, a i ∣ c) (hlt : ∀ i, a i < c)
    (hgcd : ∀ g : ℕ, g ∣ c → (∀ i, g ∣ a i) → g = 1) :
    (∃! p : ℕ, ∃ hp : 0 < p, ∃ d r : Fin p ⊕ Fin s → ℕ, IsSmoothCoconut p s d r ∧
        (∀ i, r (.inr i) = a i) ∧ r (.inl ⟨p - 1, by omega⟩) = c) ∧
      ∀ (p : ℕ) (hp : 0 < p) (d r d' r' : Fin p ⊕ Fin s → ℕ),
        IsSmoothCoconut p s d r → (∀ i, r (.inr i) = a i) →
        r (.inl ⟨p - 1, by omega⟩) = c →
        IsSmoothCoconut p s d' r' → (∀ i, r' (.inr i) = a i) →
        r' (.inl ⟨p - 1, by omega⟩) = c → d = d' ∧ r = r'

/-- Corollary 6: the smooth arithmetical structure of Proposition 7 lives on
`CT(p, s)` with `p = F(∑_j a_j, c) - 1`; stated for every smooth arithmetical
structure on `CT(p, s)` (each is the one constructed for its own labels
`a_j = r_{ℓ_j}`, `c = r_p`).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 6
(`integers-2025-A82-cor-6`). -/
public theorem_wanted IsSmoothCoconut.eq_euclideanChainLength_sub_one {p s : ℕ}
    (hp : 0 < p) {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) :
    p = euclideanChainLength (∑ j, r (.inr j)) (r (.inl ⟨p - 1, by omega⟩)) - 1

/-- Proposition 8: a smooth arithmetical structure on `CT(p, s)` (`p ≥ 1`) has
`d_p > 1` if and only if `r_p < ∑_j r_{ℓ_j}`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 8
(`integers-2025-A82-prop-8`). -/
public theorem_wanted IsSmoothCoconut.one_lt_center_iff {p s : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) :
    1 < d (.inl ⟨p - 1, by omega⟩) ↔ r (.inl ⟨p - 1, by omega⟩) < ∑ j, r (.inr j)

/-- Corollary 7: no smooth arithmetical structure on `CT(p, 2)` (`p ≥ 1`) has
`d_p > 1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 7
(`integers-2025-A82-cor-7`). -/
public theorem_wanted IsSmoothCoconut.center_le_one_of_two {p : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin 2 → ℕ} (h : IsSmoothCoconut p 2 d r) :
    d (.inl ⟨p - 1, by omega⟩) ≤ 1

/-- Smoothing at the non-central path vertex `v_{i+1}` (zero-based `i < p`) of `CT(p + 1, s)`,
giving labels on `CT(p, s)`: the vertex is removed (`r'` and `d'` are re-indexed by
`Fin.succAbove i`) and the `d`-values of its path neighbours drop by `1`. For `i ≥ 1` this is the
degree-2 smoothing of Definition 3.1 and for `i = 0` the smoothing at `v_1` of Definition 3.4 (the
requirement `d_{i+1} = 1` is a hypothesis of the statements below).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definitions 3.1 and 3.4
(arXiv numbering). -/
public def coconutSmoothPath {p s : ℕ} (i : Fin (p + 1))
    (x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)) :
    (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) :=
  (Sum.elim
      (fun j => if j.val + 1 = i.val ∨ j.val = i.val then x.1 (.inl (i.succAbove j)) - 1
        else x.1 (.inl (i.succAbove j)))
      (fun l => x.1 (.inr l)),
    Sum.elim (fun j => x.2 (.inl (i.succAbove j))) (fun l => x.2 (.inr l)))

/-- Smoothing at the leaf `v_{ℓ_{l+1}}` of `CT(p, s + 1)`, giving labels on `CT(p, s)`: the
leaf is removed (re-indexed by `Fin.succAbove l`) and `d_p` drops by `1`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.4
(arXiv numbering). -/
public def coconutSmoothLeaf {p s : ℕ} (l : Fin (s + 1))
    (x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)) :
    (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) :=
  (Sum.elim (fun j => if j.val + 1 = p then x.1 (.inl j) - 1 else x.1 (.inl j))
      (fun m => x.1 (.inr (l.succAbove m))),
    Sum.elim (fun j => x.2 (.inl j)) (fun m => x.2 (.inr (l.succAbove m))))

/-- Subdivision at position `i + 1` (zero-based `i < p`) of `CT(p, s)`, giving labels on
`CT(p + 1, s)`: a new path vertex `v'_{i+1}` with `r' = r_i + r_{i+1}` (`r' = r_1` when `i = 0`)
and `d' = 1` is inserted, and its path neighbours' `d`-values rise by `1`; leaves are unchanged.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9
(arXiv numbering). -/
public def coconutSubdivide {p s : ℕ} (i : Fin p)
    (x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)) :
    (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ) :=
  let pd : ℕ → ℕ := fun t => if h : t < p then x.1 (.inl ⟨t, h⟩) else 0
  let pr : ℕ → ℕ := fun t => if h : t < p then x.2 (.inl ⟨t, h⟩) else 0
  (Sum.elim
      (fun j => if j.val + 1 < i.val then pd j.val
        else if j.val + 1 = i.val then pd j.val + 1
        else if j.val = i.val then 1
        else if j.val = i.val + 1 then pd (j.val - 1) + 1
        else pd (j.val - 1))
      (fun l => x.1 (.inr l)),
    Sum.elim
      (fun j => if j.val < i.val then pr j.val
        else if j.val = i.val then (if i.val = 0 then 0 else pr (i.val - 1)) + pr i.val
        else pr (j.val - 1))
      (fun l => x.2 (.inr l)))

/-- Example 3.2: smoothing `d = (3, 1, 3, 2, 2 | 2, 2, 4)`,
`r = (1, 3, 2, 3, 4 | 2, 2, 1)` on `CT(5, 3)` at `v_2` gives `d' = (2, 2, 2, 2 | 2, 2, 4)`,
`r' = (1, 2, 3, 4 | 2, 2, 1)` on `CT(4, 3)`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 3.2
(arXiv numbering). -/
public theorem coconutSmoothPath_example :
    coconutSmoothPath (p := 4) (s := 3) 1
        (Sum.elim ![3, 1, 3, 2, 2] ![2, 2, 4], Sum.elim ![1, 3, 2, 3, 4] ![2, 2, 1]) =
      (Sum.elim ![2, 2, 2, 2] ![2, 2, 4], Sum.elim ![1, 2, 3, 4] ![2, 2, 1]) := by
  decide

/-- Example 3.5: on `CT(4, 4)` with `r = (2, 2, 4, 6 | 3, 3, 2, 6)`
(so `d = (1, 3, 2, 3 | 2, 2, 3, 1)`),
smoothing at `v_1` and then at `v_{ℓ_4}` gives `d' = (2, 2, 2 | 2, 2, 3)`,
`r' = (2, 4, 6 | 3, 3, 2)` on `CT(3, 3)`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 3.5
(arXiv numbering). -/
public theorem coconutSmoothLeaf_example :
    coconutSmoothLeaf (p := 3) (s := 3) 3
        (coconutSmoothPath (p := 3) (s := 4) 0
          (Sum.elim ![1, 3, 2, 3] ![2, 2, 3, 1], Sum.elim ![2, 2, 4, 6] ![3, 3, 2, 6])) =
      (Sum.elim ![2, 2, 2] ![2, 2, 3], Sum.elim ![2, 4, 6] ![3, 3, 2]) := by
  decide

/-- Subdividing the result of Example 3.2 at position `2` recovers the original structure on
`CT(5, 3)` (subdivision inverts smoothing).

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9 and
Example 3.2 (arXiv numbering). -/
public theorem coconutSubdivide_example :
    coconutSubdivide (p := 4) (s := 3) 1
        (Sum.elim ![2, 2, 2, 2] ![2, 2, 4], Sum.elim ![1, 2, 3, 4] ![2, 2, 1]) =
      (Sum.elim ![3, 1, 3, 2, 2] ![2, 2, 4], Sum.elim ![1, 3, 2, 3, 4] ![2, 2, 1]) := by
  decide

/-- `CoconutAncestor p s x q t y`: the labels `y` on `CT(q, t)` are obtained from the labels `x` on
`CT(p, s)` by a (possibly empty) sequence of smoothing operations, each at a vertex with
`d = 1` (at a non-central path vertex, or at a leaf); `y` is an ancestor of `x` and `x` a
descendant of `y`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.7
(ancestors and descendants; arXiv numbering). -/
public inductive CoconutAncestor : (p s : ℕ) → (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) →
    (q t : ℕ) → (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ) → Prop
  | refl {p s : ℕ} (x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)) : CoconutAncestor p s x p s x
  | smoothPath {p s q t : ℕ} (x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ))
      (y : (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ)) (i : Fin (p + 1)) (hi : i.val < p)
      (hd : x.1 (.inl i) = 1) (h : CoconutAncestor p s (coconutSmoothPath i x) q t y) :
      CoconutAncestor (p + 1) s x q t y
  | smoothLeaf {p s q t : ℕ} (x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ))
      (y : (Fin q ⊕ Fin t → ℕ) × (Fin q ⊕ Fin t → ℕ)) (l : Fin (s + 1))
      (hd : x.1 (.inr l) = 1) (h : CoconutAncestor p s (coconutSmoothLeaf l x) q t y) :
      CoconutAncestor p (s + 1) x q t y

/-- Proposition 3.3 (and the `v_1` case of Proposition 3.6): if `(d, r)` is an arithmetical
structure on `CT(p + 1, s)` with `s ≥ 1` and `d_{i+1} = 1` at a non-central path vertex
(`i < p`), smoothing there gives an arithmetical structure on `CT(p, s)`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.3
(`integers-2025-A82-prop-1`) and Proposition 3.6 for `i = 1` (`integers-2025-A82-prop-2`). -/
public theorem_wanted IsArithmeticalStructure.coconutSmoothPath {p s : ℕ} (hs : 1 ≤ s)
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) (i : Fin (p + 1))
    (hi : i.val < p) (hd : x.1 (.inl i) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothPath i x).1 (coconutSmoothPath i x).2

/-- Proposition 3.6, leaf case: if `(d, r)` is an arithmetical structure on `CT(p, s + 1)` and
`d_{ℓ} = 1` at a leaf, smoothing there gives an arithmetical structure on `CT(p, s)`. The
single-edge tree `CT(1, 1)` is excluded (`2 ≤ p + s`): there `d = r = (1, 1)` and smoothing the
leaf leaves one vertex with `d' = 0`, which is not an arithmetical structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.6
(`integers-2025-A82-prop-2`). -/
public theorem_wanted IsArithmeticalStructure.coconutSmoothLeaf {p s : ℕ} (hps : 2 ≤ p + s)
    {x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p (s + 1)) x.1 x.2) (l : Fin (s + 1))
    (hd : x.1 (.inr l) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothLeaf l x).1 (coconutSmoothLeaf l x).2

/-- Proposition 3.11: subdividing an arithmetical structure on `CT(p, s)` at any position
`i + 1 ∈ {1, …, p}` gives an arithmetical structure on `CT(p + 1, s)`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.11
(`integers-2025-A82-prop-3`). -/
public theorem_wanted IsArithmeticalStructure.coconutSubdivide {p s : ℕ}
    {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p s) x.1 x.2) (i : Fin p) :
    IsArithmeticalStructure (coconutTree (p + 1) s) (coconutSubdivide i x).1
      (coconutSubdivide i x).2

/-- Lemma 3.8: every arithmetical structure on `CT(p, s)` (`s ≥ 1`) with
`d_{ℓ_1}, …, d_{ℓ_s} ≥ 2` has a unique smooth ancestor on `CT(q, s)` for some `1 ≤ q ≤ p`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 3.8
(`integers-2025-A82-lem-4`). -/
public theorem_wanted IsArithmeticalStructure.existsUnique_smooth_coconutAncestor {p s : ℕ}
    (hs : 1 ≤ s) {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p s) x.1 x.2) (hleaf : ∀ j, 2 ≤ x.1 (.inr j)) :
    ∃! y : Σ q : ℕ, (Fin q ⊕ Fin s → ℕ) × (Fin q ⊕ Fin s → ℕ),
      1 ≤ y.1 ∧ y.1 ≤ p ∧ IsSmoothCoconut y.1 s y.2.1 y.2.2 ∧ CoconutAncestor p s x y.1 s y.2

/-- Proposition 4.5: for `s ≥ 2`, `1 ≤ i ≤ p` and a smooth arithmetical structure `(d, r)` on
`CT(i, s)`, exactly `B(p - 1, p - i)` arithmetical structures on `CT(p, s)` are descendants of
`(d, r)`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 4.5
(`integers-2025-A82-prop-4`). -/
public theorem_wanted ncard_coconutDescendants {p s i : ℕ} (hs : 2 ≤ s) (hi : 1 ≤ i)
    (hip : i ≤ p) {y : (Fin i ⊕ Fin s → ℕ) × (Fin i ⊕ Fin s → ℕ)}
    (hy : IsSmoothCoconut i s y.1 y.2) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2 ∧ CoconutAncestor p s x i s y}
      = ballotNumber (p - 1) (p - i)

/-- Corollary 4.6: for `p ≥ 1` and `s ≥ 2`, the number of arithmetical structures on `CT(p, s)`
whose leaves cannot be smoothed (`d_{ℓ_j} ≥ 2` for all `j`) is
`∑_{i=1}^{p} B(p - 1, p - i) |SArith(CT(i, s))|`.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 4.6
(`integers-2025-A82-cor-1`). -/
public theorem_wanted ncard_arithmeticalStructure_coconutTree_leaves_ge_two {p s : ℕ}
    (hp : 1 ≤ p) (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2 ∧ ∀ j, 2 ≤ x.1 (.inr j)}
      = ∑ i ∈ Finset.Icc 1 p, ballotNumber (p - 1) (p - i) *
          Set.ncard {z : (Fin i ⊕ Fin s → ℕ) × (Fin i ⊕ Fin s → ℕ) | IsSmoothCoconut i s z.1 z.2}

end

end MetaMathlibExt
