/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Exact covering system digraphs of degree 2

Statements from Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and
Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107.

For a representative set `S = {(aᵢ, dᵢ)}` of an exact covering system, the exact
covering system digraph (ECSD) `G_S` has vertex set `ℤ` and an edge `n → dᵢ n + aᵢ`
for each `n` and each `i`; the paper writes it `G(d₁n + a₁, …, d_r n + a_r)`. Here it is
the relation `ecsdAdj d a` with `d a : Fin r → ℤ`, so `G(d₁n + a₁, d₂n + a₂)` is
`ecsdAdj ![d₁, d₂] ![a₁, a₂]`.

Conventions used below, following Section 1 of the paper:
* a *cyclic vertex* `m` is a vertex on a cycle, stated as
  `Relation.TransGen (ecsdAdj d a) m m`;
* the ECSD *has a single component* when every two vertices are joined in the
  underlying undirected graph, stated as `∀ m n, Relation.EqvGen (ecsdAdj d a) m n`;
* a *`k`-descendant* of `m` is the end of a directed walk of exactly `k` edges from `m`
  (`IsKDescendant`);
* a cycle `(c₁, …, c_t)` is a list of distinct vertices with consecutive edges closing
  up (`IsDigraphCycle`);
* `ord(g, a)` is `orderOf (g : ZMod a)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The edge relation of the exact covering system digraph `G(d₁n + a₁, …, d_r n + a_r)`:
there is an edge `m → n` iff `n = dᵢ m + aᵢ` for some rule `i`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `G_S`). -/
def ecsdAdj {r : ℕ} (d a : Fin r → ℤ) (m n : ℤ) : Prop :=
  ∃ i, n = d i * m + a i

/-- In a degree-2 ECSD `G(d₁n + a₁, d₂n + a₂)`, the successors of `m` are
`d₁m + a₁` and `d₂m + a₂`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `G_S`). -/
theorem ecsdAdj_two (d₁ d₂ a₁ a₂ m n : ℤ) :
    ecsdAdj ![d₁, d₂] ![a₁, a₂] m n ↔ n = d₁ * m + a₁ ∨ n = d₂ * m + a₂ := by
  simp [ecsdAdj, Fin.exists_fin_two]

/-- `IsKDescendant R k m n`: `n` is a `k`-descendant of `m` in the digraph `R`, i.e.
there is a directed walk of exactly `k` edges from `m` to `n`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `k`-descendant). -/
def IsKDescendant (R : ℤ → ℤ → Prop) : ℕ → ℤ → ℤ → Prop
  | 0, m, n => n = m
  | k + 1, m, n => ∃ x, IsKDescendant R k m x ∧ R x n

/-- The only `0`-descendant of `m` is `m` itself.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of `k`-descendant). -/
theorem isKDescendant_zero (R : ℤ → ℤ → Prop) (m n : ℤ) :
    IsKDescendant R 0 m n ↔ n = m :=
  Iff.rfl

/-- The `1`-descendants (successors) of `m` are the out-neighbours of `m`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 1
(definition of successor). -/
theorem isKDescendant_one (R : ℤ → ℤ → Prop) (m n : ℤ) :
    IsKDescendant R 1 m n ↔ R m n := by
  simp [IsKDescendant]

/-- `IsDigraphCycle R c`: the list `c = (c₁, …, c_t)` is a cycle of the digraph `R`,
i.e. it is nonempty, its entries are distinct, and `R c₁ c₂, …, R c_{t-1} c_t, R c_t c₁`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(cycles `C = (c₁, …, c_t)`). -/
def IsDigraphCycle (R : ℤ → ℤ → Prop) (c : List ℤ) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ (c ++ c.take 1).IsChain R

/-- A one-vertex list `(x)` is a cycle exactly when `x` carries a loop.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(cycles of length 1). -/
theorem isDigraphCycle_singleton (R : ℤ → ℤ → Prop) (x : ℤ) :
    IsDigraphCycle R [x] ↔ R x x := by
  simp [IsDigraphCycle]

/-- A two-vertex list `(x, y)` is a cycle exactly when `x ≠ y` and both edges
`x → y`, `y → x` are present.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Section 2
(2-cycles). -/
theorem isDigraphCycle_pair (R : ℤ → ℤ → Prop) (x y : ℤ) :
    IsDigraphCycle R [x, y] ↔ x ≠ y ∧ R x y ∧ R y x := by
  simp [IsDigraphCycle]

/-- Translating every vertex by `k` is an isomorphism `G_S ≅ G_{S'}` with
`S' = {(aᵢ - (dᵢ - 1)k, dᵢ)}`. Stated for an arbitrary finite rule list; the paper's
exact-covering hypothesis on `S` is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 1
(`integers-2026-A107-thm-1`). -/
theorem_wanted ecsdAdj_shift_relIso {r : ℕ} (d a : Fin r → ℤ) (k : ℤ) :
    ∃ e : ecsdAdj d a ≃r ecsdAdj d (fun i => a i - (d i - 1) * k), ∀ n, e n = n + k

/-- The map `n ↦ -(n + k)` is an isomorphism `G_S ≅ G_{S'}` with
`S' = {(-aᵢ + (dᵢ - 1)k, dᵢ)}`. Stated for an arbitrary finite rule list; the paper's
exact-covering hypothesis on `S` is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 2
(`integers-2026-A107-thm-2`). -/
theorem_wanted ecsdAdj_neg_shift_relIso {r : ℕ} (d a : Fin r → ℤ) (k : ℤ) :
    ∃ e : ecsdAdj d a ≃r ecsdAdj d (fun i => -a i + (d i - 1) * k), ∀ n, e n = -(n + k)

/-- Every Type 1 ECSD `G(2n + a₁, 2n + a₂)` (`a₁ - a₂` odd) is isomorphic to
`G(2n, 2n - a)` for some odd `a ∈ ℕ`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 3
(`integers-2026-A107-thm-3`). -/
theorem_wanted ecsd_type_one_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    ∃ a : ℕ, Odd a ∧ Nonempty (ecsdAdj ![2, 2] ![a₁, a₂] ≃r ecsdAdj ![2, 2] ![0, -(a : ℤ)])

/-- Every Type 2 ECSD `G(2n + a₁, -2n + a₂)` (`a₁ - a₂` odd) is isomorphic to
`G(2n, -2n + a)` for some odd `a ∈ ℕ`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 4
(`integers-2026-A107-thm-4`). -/
theorem_wanted ecsd_type_two_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    ∃ a : ℕ, Odd a ∧ Nonempty (ecsdAdj ![2, -2] ![a₁, a₂] ≃r ecsdAdj ![2, -2] ![0, (a : ℤ)])

/-- Every Type 3 ECSD `G(-2n + a₁, -2n + a₂)` (`a₁ - a₂` odd) is isomorphic to one of
Type 3.1 `G(-2n, -2n + a)` with `a ∈ ℕ` odd, Type 3.2 `G(-2n + 1, -2n + a)` with
`a ∈ ℕ` even and `a ≡ 1 (mod 3)`, or Type 3.3 `G(-2n + 1, -2n + a)` with `a ∈ ℤ` even
and `a ≡ 2 (mod 3)`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 5
(`integers-2026-A107-thm-5`). -/
theorem_wanted ecsd_type_three_relIso (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) :
    (∃ a : ℕ, Odd a ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![0, (a : ℤ)])) ∨
      (∃ a : ℕ, Even a ∧ a % 3 = 1 ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, (a : ℤ)])) ∨
      ∃ a : ℤ, Even a ∧ a % 3 = 2 ∧
        Nonempty (ecsdAdj ![-2, -2] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, a])

/-- Cycles of the Type 1 ECSD `G(2n, 2n - a)`, `a ∈ ℕ` odd: (i) the only loops are at
`0` and `a`; (ii) `m` is a cyclic vertex iff `0 ≤ m ≤ a`; (iii) `C = (2ᵏ mod a)` for
`0 ≤ k < ord(2, a)` is a cycle, every cocycle `bC = (b2ᵏ mod a)` for `1 ≤ b < a`, of
length `ord(2, a / gcd(a, b))`, is a cycle, and every cycle of length greater than 1 is
a rotation of such a cocycle; (iv) for `a = t a'`, `C` is a cycle of `G(2n, 2n - a')`
iff `tC` is a cycle of `G(2n, 2n - a)` (the paper's hypothesis that `a'` is odd follows
from `a` odd and is dropped). Residues `x mod a` are taken in `[0, a - 1]`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 6
(`integers-2026-A107-thm-6`). -/
theorem_wanted ecsd_two_two_sub_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![2, 2] ![0, -(a : ℤ)] m m ↔ m = 0 ∨ m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) m m ↔ 0 ≤ m ∧ m ≤ a) ∧
    IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)])
      ((List.range (orderOf (2 : ZMod a))).map fun k => (2 : ℤ) ^ k % a) ∧
    (∀ b : ℤ, 1 ≤ b → b < a → IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)])
      ((List.range (orderOf (2 : ZMod (a / Int.gcd a b)))).map fun k => (b * 2 ^ k) % a)) ∧
    (∀ c : List ℤ, IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) c → 1 < c.length →
      ∃ b : ℤ, 1 ≤ b ∧ b < a ∧ c ~r
        (List.range (orderOf (2 : ZMod (a / Int.gcd a b)))).map fun k => (b * 2 ^ k) % a) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![2, 2] ![0, -(a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- The `k`-descendants (`k ≥ 1`) of `m` in the Type 2 ECSD `G(2n, -2n + a)` are
`2ᵏm`, `±(2ᵏm - ba)` for `1 ≤ b < 2^(k-1)`, and `-(2ᵏm - 2^(k-1)a)`. Corrected reading:
the paper prints the last term as `-(2ᵏ - 2^(k-1)a)`, which is false (for `m = 0`,
`a = 1`, `k = 1` the descendants are `{0, 1}`, not `{0, -1}`); the factor `m` is
restored as in the paper's proof of Theorem 7. Stated for every `a ∈ ℤ` (the paper
has `a ∈ ℕ` odd).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 1
(`integers-2026-A107-prop-1`). -/
theorem_wanted ecsd_two_neg_two_descendants (a m n : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    IsKDescendant (ecsdAdj ![2, -2] ![0, a]) k m n ↔
      n = 2 ^ k * m ∨
        (∃ b : ℕ, 1 ≤ b ∧ b < 2 ^ (k - 1) ∧
          (n = 2 ^ k * m - b * a ∨ n = -(2 ^ k * m - b * a))) ∨
        n = -(2 ^ k * m - 2 ^ (k - 1) * a)

/-- Cycles of the Type 2 ECSD `G(2n, -2n + a)`, `a ∈ ℕ` odd: (i) the only loops are at
`0` and, when `3 ∣ a`, at `a / 3`; (ii) `m` is a cyclic vertex iff `0 ≤ m < a / 2`;
(iii) for `a = t a'`, `C` is a cycle of `G(2n, -2n + a')` iff `tC` is a cycle of
`G(2n, -2n + a)` (the hypothesis that `a'` is odd is dropped as implied).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 7
(`integers-2026-A107-thm-7`). -/
theorem_wanted ecsd_two_neg_two_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![2, -2] ![0, (a : ℤ)] m m ↔ m = 0 ∨ 3 * m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![2, -2] ![0, (a : ℤ)]) m m ↔ 0 ≤ m ∧ 2 * m < a) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![2, -2] ![0, (a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![2, -2] ![0, (a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- In `G(-2n + a₁, -2n + a₂)` every `k`-descendant of `m` is congruent to
`(-2)ᵏm + a₁(1 - (-2)ᵏ)/3` modulo `|a₁ - a₂|` (the quotient is exact). Stated for all
`a₁, a₂ ∈ ℤ`; the exact-covering condition is not needed.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 8
(`integers-2026-A107-thm-8`). -/
theorem_wanted ecsd_neg_two_descendant_modEq (a₁ a₂ m n : ℤ) (k : ℕ)
    (h : IsKDescendant (ecsdAdj ![-2, -2] ![a₁, a₂]) k m n) :
    n ≡ (-2) ^ k * m + a₁ * ((1 - (-2) ^ k) / 3) [ZMOD |a₁ - a₂|]

/-- Each congruence class modulo `|a₁ - a₂|` contains a cyclic vertex of the ECSD
`G(-2n + a₁, -2n + a₂)` (`a₁ - a₂` odd).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 9
(`integers-2026-A107-thm-9`). -/
theorem_wanted ecsd_neg_two_cyclic_residues (a₁ a₂ : ℤ) (h : Odd (a₁ - a₂)) (c : ℤ) :
    ∃ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![a₁, a₂]) m m ∧ m ≡ c [ZMOD |a₁ - a₂|]

/-- Cycles of the Type 3.1 ECSD `G(-2n, -2n + a)`, `a ∈ ℕ` odd: (i) the only loops are at
`0` and, when `3 ∣ a`, at `a / 3`; (ii) `m` is cyclic iff `-a/3 ≤ m ≤ 2a/3`;
(iii) if `3 ∤ a` there are `a` cyclic vertices, one in each class mod `a`; if `3 ∣ a`
there are `a + 1`, one in each class except the class of `-a/3 ≡ 2a/3`, and
`(-a/3, 2a/3)` is a 2-cycle; (iv) with `x̂` the representative of `x` mod `a` in
`(-a/3, 2a/3]`, written `(x + (a - 1)/3) % a - (a - 1)/3`, the list
`C = ((-2)ᵏ)^` for `0 ≤ k < ord(-2, a)` is a cycle, and so is each cocycle
`bC = (b(-2)ᵏ)^` of length `ord(-2, a / gcd(a, b))` for `-a/3 < b < 2a/3`,
`b ∉ {0, a/3}`; (v) for `a = t a'`, `C` is a cycle of `G(-2n, -2n + a')` iff `tC` is a
cycle of `G(-2n, -2n + a)` (the hypothesis that `a'` is odd is dropped as implied).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 10
(`integers-2026-A107-thm-10`). -/
theorem_wanted ecsd_neg_two_neg_two_cycles (a : ℕ) (ha : Odd a) :
    (∀ m : ℤ, ecsdAdj ![-2, -2] ![0, (a : ℤ)] m m ↔ m = 0 ∨ 3 * m = a) ∧
    (∀ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ↔
      -(a : ℤ) ≤ 3 * m ∧ 3 * m ≤ 2 * a) ∧
    (¬ 3 ∣ a →
      {m : ℤ | Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m}.ncard = a ∧
      ∀ c : ℤ, ∃! m : ℤ,
        Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ∧ m ≡ c [ZMOD a]) ∧
    (3 ∣ a →
      {m : ℤ | Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m}.ncard = a + 1 ∧
      (∀ c : ℤ, ¬ c ≡ 2 * ((a : ℤ) / 3) [ZMOD a] → ∃! m : ℤ,
        Relation.TransGen (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) m m ∧ m ≡ c [ZMOD a]) ∧
      IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) [-((a : ℤ) / 3), 2 * ((a : ℤ) / 3)]) ∧
    IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)])
      ((List.range (orderOf (-2 : ZMod a))).map
        fun k => ((-2) ^ k + ((a : ℤ) - 1) / 3) % a - ((a : ℤ) - 1) / 3) ∧
    (∀ b : ℤ, -(a : ℤ) < 3 * b → 3 * b < 2 * a → b ≠ 0 → 3 * b ≠ a →
      IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)])
        ((List.range (orderOf (-2 : ZMod (a / Int.gcd a b)))).map
          fun k => (b * (-2) ^ k + ((a : ℤ) - 1) / 3) % a - ((a : ℤ) - 1) / 3)) ∧
    ∀ a' t : ℕ, a = t * a' → ∀ c : List ℤ,
      (IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a' : ℤ)]) c ↔
        IsDigraphCycle (ecsdAdj ![-2, -2] ![0, (a : ℤ)]) (c.map ((t : ℤ) * ·)))

/-- For `a ∈ ℕ` even with `a ≡ 1 (mod 3)`, `m` is a cyclic vertex of the Type 3.2 ECSD
`G(-2n + 1, -2n + a)` iff `-(a - 1)/3 < m < 2a/3`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 11
(`integers-2026-A107-thm-11`). -/
theorem_wanted ecsd_type_three_two_cyclic_iff (a : ℕ) (ha : Even a) (ha3 : a % 3 = 1)
    (m : ℤ) :
    Relation.TransGen (ecsdAdj ![-2, -2] ![1, (a : ℤ)]) m m ↔
      -((a : ℤ) - 1) < 3 * m ∧ 3 * m < 2 * a

/-- For `a ∈ ℤ` even with `a ≡ 2 (mod 3)`, every cyclic vertex `m` of the Type 3.3 ECSD
`G(-2n + 1, -2n + a)` satisfies `-(a - 1)/3 < m < 2a/3` if `a ≥ 2`, and
`-2(|a| + 1)/3 < m < |a|/3 + 1` if `a ≤ -2`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 12
(`integers-2026-A107-thm-12`). -/
theorem_wanted ecsd_type_three_three_cyclic_bounds (a : ℤ) (ha : Even a) (ha3 : a % 3 = 2)
    (m : ℤ) (hm : Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m) :
    (2 ≤ a → -(a - 1) < 3 * m ∧ 3 * m < 2 * a) ∧
      (a ≤ -2 → -2 * (|a| + 1) < 3 * m ∧ 3 * m < |a| + 3)

/-- For `a ∈ ℤ` even with `a ≡ 2 (mod 3)`, every `m` in the range of Theorem 12 is a
cyclic vertex of `G(-2n + 1, -2n + a)`; every class modulo `|a - 1|` has a cyclic
representative, which is unique except for the smallest and largest cyclic vertices,
which are congruent modulo `|a - 1|` and form a 2-cycle.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 13
(`integers-2026-A107-thm-13`). -/
theorem_wanted ecsd_type_three_three_cyclic (a : ℤ) (ha : Even a) (ha3 : a % 3 = 2) :
    (∀ m : ℤ, ((2 ≤ a ∧ -(a - 1) < 3 * m ∧ 3 * m < 2 * a) ∨
        (a ≤ -2 ∧ -2 * (|a| + 1) < 3 * m ∧ 3 * m < |a| + 3)) →
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m) ∧
    (∀ c : ℤ, ∃ m : ℤ,
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m ∧ m ≡ c [ZMOD |a - 1|]) ∧
    ∃ lo hi : ℤ,
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) lo lo ∧
      Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) hi hi ∧
      (∀ m : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m → lo ≤ m ∧ m ≤ hi) ∧
      lo ≡ hi [ZMOD |a - 1|] ∧
      IsDigraphCycle (ecsdAdj ![-2, -2] ![1, a]) [lo, hi] ∧
      ∀ m m' : ℤ, Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m m →
        Relation.TransGen (ecsdAdj ![-2, -2] ![1, a]) m' m' → m ≡ m' [ZMOD |a - 1|] →
        m ≠ m' → ({m, m'} : Set ℤ) = {lo, hi}

/-- For `d ≥ 2`, `D = ±d` and an exact covering system `{(aᵢ, D) : 1 ≤ i ≤ d}`, every
integer is a sum `∑_{j=0}^k bⱼ Dʲ` with digits `bⱼ ∈ {a₁, …, a_d}` iff the ECSD `G_S`
has a single component whose cycle contains `0`. The digit-string length `k` ranges over
`ℕ` (lengths can be padded once `0` is cyclic); the uniqueness clause of the paper is
omitted.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 14
(`integers-2026-A107-thm-14`). -/
theorem_wanted ecsd_digit_representation_iff (d : ℕ) (hd : 2 ≤ d) (D : ℤ) (hD : |D| = d)
    (a : Fin d → ℤ) (hS : ∀ n : ℤ, ∃! i, D ∣ n - a i) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, ∃ i, b j = a i) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * D ^ j) ↔
      (∀ m n : ℤ, Relation.EqvGen (ecsdAdj (fun _ => D) a) m n) ∧
        Relation.TransGen (ecsdAdj (fun _ => D) a) 0 0

/-- For `a` even, the ECSD `G(-2n + 1, -2n + a)` has one component iff `a = 1 ± 3ᵐ` for
some `m ∈ ℕ₀`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 15
(`integers-2026-A107-thm-15`). -/
theorem_wanted ecsd_one_component_iff (a : ℤ) (ha : Even a) :
    (∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![-2, -2] ![1, a]) m n) ↔
      ∃ m : ℕ, a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m

/-- In the single-component ECSD `G(-2n + 1, -2n + a)` with `a = 1 ± 3ᵐ`, `m ≥ 1`, the
shortest paths from `0` to `a - 1` and from `0` to `-(a - 1)` have `|a - 1| = 3ᵐ` edges.
Restricted reading: the paper states this for every `a ∉ {0, 2}`, which is false
(for `a = 6` the shortest path from `0` to `5` has 4 edges); its proof uses that the
cycle through `0` has `|a - 1|` edges, which holds in the single-component case.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 16
(`integers-2026-A107-thm-16`). -/
theorem_wanted ecsd_path_length_to_a_sub_one (m : ℕ) (hm : 1 ≤ m) (a : ℤ)
    (ha : a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m) :
    IsLeast {k : ℕ | IsKDescendant (ecsdAdj ![-2, -2] ![1, a]) k 0 (a - 1)} (3 ^ m) ∧
      IsLeast {k : ℕ | IsKDescendant (ecsdAdj ![-2, -2] ![1, a]) k 0 (-(a - 1))} (3 ^ m)

/-- A degree-2 ECSD `G(d₁n + a₁, d₂n + a₂)` (`d₁, d₂ ∈ {2, -2}`, `a₁ - a₂` odd) has a
single component with cyclic vertex `0` iff it is `G(2n, -2n ± 1)` (in either rule
order) or it is `G(-2n + a₁, -2n + a₂)` with `|a₁ - a₂| = 3ᵐ`, `a₁, a₂ ≢ 0 (mod 3)` and
`max{|a₁|, |a₂|} ≤ 2|a₁ - a₂| - 1`. Restricted reading: Type 3 ECSDs with
`|a₁ - a₂| = 1` are excluded, where the printed statement fails (`G(-2n + 1, -2n + 2)`
has a single component with cycle `(0, 1)`, but `max{1, 2} = 2 > 2·1 - 1`); the paper's
alternative `{a₁, a₂} = {0, ±1}` lies in the excluded case and is dropped.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 17
(`integers-2026-A107-thm-17`). -/
theorem_wanted ecsd_single_component_zero_cyclic_iff (d₁ d₂ a₁ a₂ : ℤ)
    (hd₁ : d₁ = 2 ∨ d₁ = -2) (hd₂ : d₂ = 2 ∨ d₂ = -2) (ha : Odd (a₁ - a₂))
    (hne : ¬ (d₁ = -2 ∧ d₂ = -2 ∧ |a₁ - a₂| = 1)) :
    ((∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) m n) ∧
        Relation.TransGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) 0 0) ↔
      (d₁ = 2 ∧ d₂ = -2 ∧ a₁ = 0 ∧ (a₂ = 1 ∨ a₂ = -1)) ∨
        (d₁ = -2 ∧ d₂ = 2 ∧ a₂ = 0 ∧ (a₁ = 1 ∨ a₁ = -1)) ∨
        (d₁ = -2 ∧ d₂ = -2 ∧ (∃ m : ℕ, |a₁ - a₂| = 3 ^ m) ∧ ¬ 3 ∣ a₁ ∧ ¬ 3 ∣ a₂ ∧
          max |a₁| |a₂| ≤ 2 * |a₁ - a₂| - 1)

/-- Every integer is `∑_{j=0}^k bⱼ(-2)ʲ` with digits `bⱼ ∈ {1, a}` iff `a = 1 ± 3ᵐ` for
some `m ∈ ℕ₀`. The length `k` ranges over `ℕ`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Corollary 1
(`integers-2026-A107-cor-1`). -/
theorem_wanted negabinary_digits_one_a_complete_iff (a : ℤ) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, b j = 1 ∨ b j = a) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * (-2) ^ j) ↔
      ∃ m : ℕ, a = 1 + 3 ^ m ∨ a = 1 - 3 ^ m

/-- For integers `a₁, a₂` with `|a₁ - a₂| ≠ 1`, every integer is `∑_{j=0}^k bⱼ(-2)ʲ` with
digits `bⱼ ∈ {a₁, a₂}` iff `|a₁ - a₂| = 3ᵐ`, `a₁, a₂ ≢ 0 (mod 3)` and
`max{|a₁|, |a₂|} ≤ 2|a₁ - a₂| - 1`. Restricted reading: the printed statement fails for
`|a₁ - a₂| = 1` (the digits `{1, 2}` represent every integer, as `G(-2n + 1, -2n + 2)`
has one component with cycle `(0, 1)`, yet `max{1, 2} = 2 > 1`); the paper's alternative
`{a₁, a₂} = {0, ±1}` lies in the excluded case and is dropped.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Corollary 2
(`integers-2026-A107-cor-2`). -/
theorem_wanted negabinary_two_digits_complete_iff (a₁ a₂ : ℤ) (h : |a₁ - a₂| ≠ 1) :
    (∀ z : ℤ, ∃ (k : ℕ) (b : ℕ → ℤ), (∀ j ≤ k, b j = a₁ ∨ b j = a₂) ∧
        z = ∑ j ∈ Finset.range (k + 1), b j * (-2) ^ j) ↔
      (∃ m : ℕ, |a₁ - a₂| = 3 ^ m) ∧ ¬ 3 ∣ a₁ ∧ ¬ 3 ∣ a₂ ∧
        max |a₁| |a₂| ≤ 2 * |a₁ - a₂| - 1

/-- If `n ∣ (2ⁿ + 1)/3` then `3n ∣ (2^(3n) + 1)/3`, stated in the equivalent integral
form `3n ∣ 2ⁿ + 1 → 9n ∣ 2^(3n) + 1` (for `n = 0` the hypothesis fails, so positivity
is not assumed).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 1
(`integers-2026-A107-lem-1`). -/
theorem_wanted three_mul_dvd_two_pow_add_one_cube (n : ℕ) (h : 3 * n ∣ 2 ^ n + 1) :
    9 * n ∣ 2 ^ (3 * n) + 1

/-- If `n ∣ (1 - (-2)ᵏ)/3` then `3n ∣ (1 - (-2)^(3k))/3`, stated in the integral form
`3n ∣ 1 - (-2)ᵏ → 9n ∣ 1 - (-2)^(3k)` for all `n ∈ ℤ`, `k ∈ ℕ` (the paper has positive
`n`, `k`).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 2
(`integers-2026-A107-lem-2`). -/
theorem_wanted three_mul_dvd_one_sub_neg_two_pow_cube (n : ℤ) (k : ℕ)
    (h : 3 * n ∣ 1 - (-2) ^ k) : 9 * n ∣ 1 - (-2) ^ (3 * k)

/-- If `3ᵐ ∤ (2ᵏ + 1)/3` then `3^(m+1) ∤ (2^(3k) + 1)/3`, stated in the integral form
`3^(m+1) ∤ 2ᵏ + 1 → 3^(m+2) ∤ 2^(3k) + 1` for all `m, k ∈ ℕ` (equivalent for odd `k`,
where `3 ∣ 2ᵏ + 1`; for even `k` the conclusion holds since `3 ∤ 2^(3k) + 1`).

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 3
(`integers-2026-A107-lem-3`). -/
theorem_wanted three_pow_not_dvd_two_pow_add_one_cube (m k : ℕ)
    (h : ¬ 3 ^ (m + 1) ∣ 2 ^ k + 1) : ¬ 3 ^ (m + 2) ∣ 2 ^ (3 * k) + 1

/-- For `n > 3`, if `n ∣ (2ⁿ + 1)/3` (integral form `3n ∣ 2ⁿ + 1`) then `9 ∣ n`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 4
(`integers-2026-A107-lem-4`), quoting [3]. -/
theorem_wanted nine_dvd_of_three_mul_dvd_two_pow_add_one (n : ℕ) (hn : 3 < n)
    (h : 3 * n ∣ 2 ^ n + 1) : 9 ∣ n

/-- A degree-2 ECSD `G(d₁n + a₁, d₂n + a₂)` (`d₁, d₂ ∈ {2, -2}`, `a₁ - a₂` odd) with a
single component is isomorphic to `G(2n, -2n + 1)` or to `G(-2n + 1, -2n + a)` with
`a = 0`, `a = 2` or `a ≡ 1 (mod 3)`.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Proposition 2
(`integers-2026-A107-prop-2`). -/
theorem_wanted ecsd_single_component_relIso (d₁ d₂ a₁ a₂ : ℤ)
    (hd₁ : d₁ = 2 ∨ d₁ = -2) (hd₂ : d₂ = 2 ∨ d₂ = -2) (ha : Odd (a₁ - a₂))
    (h : ∀ m n : ℤ, Relation.EqvGen (ecsdAdj ![d₁, d₂] ![a₁, a₂]) m n) :
    Nonempty (ecsdAdj ![d₁, d₂] ![a₁, a₂] ≃r ecsdAdj ![2, -2] ![0, 1]) ∨
      ∃ a : ℤ, (a = 0 ∨ a = 2 ∨ a % 3 = 1) ∧
        Nonempty (ecsdAdj ![d₁, d₂] ![a₁, a₂] ≃r ecsdAdj ![-2, -2] ![1, a])

end

end MetaMathlibExt
