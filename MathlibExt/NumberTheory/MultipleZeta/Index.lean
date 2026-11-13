/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.PNat.Basic

/-!
# Multiple-zeta indices

This file defines multiple-zeta indices, admissibility for bundled and list
representations, and Hoffman blocks in a two-letter free monoid.

## Main definitions

* `MetaMathlibExt.MultipleZeta.Index`
* `MetaMathlibExt.MultipleZeta.Index.entries`
* `MetaMathlibExt.MultipleZeta.Index.weight`
* `MetaMathlibExt.MultipleZeta.Index.depth`
* `MetaMathlibExt.MultipleZeta.Index.height`
* `MetaMathlibExt.MultipleZeta.Index.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.hoffmanBlock`

## Main theorems

* `MetaMathlibExt.MultipleZeta.Index.isAdmissible_iff`
* `MetaMathlibExt.MultipleZeta.toList_hoffmanBlock`
-/

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

/-- **Multiple-zeta index.** An index is a finite sequence $(k_1, \ldots, k_r)$ of positive
integers with $r \ge 0$, so the empty sequence is allowed. It is represented as a natural
number $n$ together with a composition of $n$, that is, a sequence of positive integers with
sum $n$.

Source: clause D1 (`2608.10675:D01`, `2307.09867:D01`). -/
def Index : Type :=
  Σ _n : Nat, Composition _n

/-- **Entries of an index.** The entries of an index $(k_1, \ldots, k_r)$ form the list
$[k_1, \ldots, k_r]$ of its terms, in order.

Source: clause D2 (`2608.10675:D01`, `2307.09867:D01`). -/
def Index.entries : Index → List Nat
  | ⟨_, c⟩ => c.blocks

/-- **Weight of an index.** The weight of an index $(k_1, \ldots, k_r)$ is the sum
$k_1 + \cdots + k_r$ of its entries.

Source: clause D3 (`2307.09867:D01`). -/
def Index.weight : Index → Nat
  | ⟨n, _⟩ => n

/-- **Depth of an index.** The depth of an index $(k_1, \ldots, k_r)$ is its number of
entries $r$.

Source: clause D4 (`2608.10675:D01`, `2307.09867:D01`). -/
def Index.depth : Index → Nat
  | ⟨_, c⟩ => Composition.length c

/-- **Height of an index.** The height of an index $(k_1, \ldots, k_r)$ is the number of
positions $i$ with $1 \le i \le r$ and $k_i \ge 2$.

Source: clause D5 (`2307.09867:D01`). -/
def Index.height : Index → Nat
  | ⟨_, c⟩ => (c.blocks.filter (· ≥ 2)).length

/-- **Admissible index.** An index $(k_1, \ldots, k_r)$ is admissible when it is nonempty
($r \ge 1$) and its first entry satisfies $k_1 \ge 2$.

Source: clause D6 (`2307.09867:D01`). -/
def Index.IsAdmissible : Index → Prop
  | ⟨_, c⟩ =>
    match c.blocks with
    | [] => False
    | h :: _ => 2 ≤ h

/-- **Admissible list.** A list $[k_1, \ldots, k_r]$ of natural numbers is admissible when it
is nonempty ($r \ge 1$), $k_1 \ge 2$, and $k_i > 0$ for every $i$ with $2 \le i \le r$.

This is the admissibility condition for multiple-zeta indices in decreasing summation order.

Source: `2307.09867:D01`. -/
def IsAdmissible : List ℕ → Prop
  | [] => False
  | h :: t => 2 ≤ h ∧ ∀ x ∈ t, 0 < x

@[simp]
theorem isAdmissible_nil : ¬IsAdmissible [] := by
  simp [IsAdmissible]

@[simp]
theorem isAdmissible_cons_iff (h : ℕ) (t : List ℕ) :
    IsAdmissible (h :: t) ↔ 2 ≤ h ∧ ∀ x ∈ t, 0 < x := by
  rfl

/-- **Admissibility of an index via its entries.** An index is admissible if and only if the
list of its entries is an admissible list. -/
theorem Index.isAdmissible_iff (index : Index) :
    index.IsAdmissible ↔ MetaMathlibExt.MultipleZeta.IsAdmissible index.entries := by
  rcases index with ⟨_, c⟩
  cases hblocks : c.blocks with
  | nil => simp [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
  | cons h t =>
      simp only [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
      constructor
      · intro hh
        refine ⟨hh, fun x hx => c.blocks_pos ?_⟩
        simpa [hblocks] using List.mem_cons_of_mem h hx
      · exact fun h => h.1

/-- **Hoffman block.** For a positive integer $k$, the Hoffman block $z_k = x^{k-1} y$ is the
word in the free monoid on two letters $x$ and $y$ consisting of $k - 1$ copies of $x$ followed
by one $y$.

The free monoid is taken on the booleans, with false standing for $x$ and true for $y$.

Source: `2307.09867:D05`. -/
def hoffmanBlock (k : PNat) : FreeMonoid Bool :=
  FreeMonoid.ofList (List.replicate (k.val - 1) false ++ [true])

/-- **Hoffman block as a list.** For every positive integer $k$, the list of letters of the
Hoffman block $z_k$ consists of $k - 1$ copies of $x$ (false) followed by one $y$ (true). -/
@[simp]
theorem toList_hoffmanBlock (k : PNat) :
    FreeMonoid.toList (hoffmanBlock k) =
      List.replicate (k.val - 1) false ++ [true] := by
  simp [hoffmanBlock]

end MetaMathlibExt.MultipleZeta
