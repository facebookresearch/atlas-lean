/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.WellQuasiOrder
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutSubdivision
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree

/-!
# Counting arithmetical structures on coconut trees

We prove the coconut tree counting formula of Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith,
*Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82.

First partition by the set of leaves with label `d = 1`. Among the remaining structures,
restrict where a noncentral path vertex may have `d = 1`. Insertion and contraction at the
rightmost allowed position give a recurrence whose coefficients are ballot numbers. On a path
the recurrence starts from the single vertex and gives the Catalan numbers.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ballot numbers.** For natural numbers $n$ and $k$, the ballot number $B(n, k)$ is the
integer part of $\max(n + 1 - k, 0) \binom{n+k}{n} / (n + 1)$. For $k \le n + 1$ the division
is exact, so $B(n, k) = \frac{n - k + 1}{n + 1} \binom{n+k}{n}$ (OEIS A009766), and
$B(n, k) = 0$ for $k > n + 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public def ballotNumber (n k : ℕ) : ℕ :=
  (n + 1 - k) * (n + k).choose n / (n + 1)

/-- **Ballot numbers with second index zero.** For every natural number $n$, the ballot number
$B(n, 0)$ equals $1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_zero_right (n : ℕ) : ballotNumber n 0 = 1 := by
  simp [ballotNumber]

/-- **Diagonal ballot numbers are Catalan numbers.** For every natural number $n$, the ballot
number $B(n, n)$ equals the $n$-th Catalan number $C_n$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Section 1. -/
public theorem ballotNumber_self (n : ℕ) : ballotNumber n n = catalan n := by
  rw [ballotNumber, show n + 1 - n = 1 by omega, one_mul, ← two_mul,
    ← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom,
    Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- **Terms of the coconut tree count.** For natural numbers $x$ and $y$, the term $A(x, y)$ is
defined by $A(x, 0) = C_{x-1}$, $A(x, 1) = C_{x-1} - C_{x-2}$ and, for $y \ge 2$,

$$A(x, y) = \sum_{i=y+1}^{x} B(x - y - 1, x - i) \, |\mathrm{SArith}(CT(i - y, y))|,$$

where $C_n$ is the $n$-th Catalan number (a negative index is read as $0$), $B$ is the ballot
number, and $|\mathrm{SArith}(CT(m, y))|$ is the number of smooth arithmetical structures
$(d, r)$ on the coconut tree $CT(m, y)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public noncomputable def coconutCountTerm (x y : ℕ) : ℕ :=
  if y = 0 then catalan (x - 1)
  else if y = 1 then catalan (x - 1) - catalan (x - 2)
  else ∑ i ∈ Finset.Icc (y + 1) x, ballotNumber (x - y - 1) (x - i) *
    Set.ncard {z : (Fin (i - y) ⊕ Fin y → ℕ) × (Fin (i - y) ⊕ Fin y → ℕ) |
      IsSmoothCoconut (i - y) y z.1 z.2}

/-- **The coconut count term with second argument zero.** For every natural number $x$, the
term $A(x, 0)$ of the coconut tree count equals the Catalan number $C_{x-1}$, read as $C_0$
when $x = 0$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1. -/
public theorem coconutCountTerm_zero (x : ℕ) : coconutCountTerm x 0 = catalan (x - 1) := by
  simp [coconutCountTerm]

end

namespace ncard_arithmeticalStructure_coconutTree

open Finset

/-! ## Vertex equations -/

private abbrev Vertex (n : ℕ) (ι : Type) := Fin (n + 1) ⊕ ι
private abbrev Labels (n : ℕ) (ι : Type) := (Vertex n ι → ℕ) × (Vertex n ι → ℕ)
private abbrev center (n : ℕ) (ι : Type) : Vertex n ι := .inl (Fin.last n)

-- The path is padded on the left by zero and on the right by the sum over the leaves.
private def level (n s k : ℕ) : Set (Vertex n (Fin s)) :=
  {v | Sum.elim (fun i : Fin (n + 1) => i.val + 1) (fun _ : Fin s => n + 2) v = k}

private noncomputable def value {n : ℕ} {ι : Type} [Fintype ι]
    (r : Vertex n ι → ℕ) (k : ℕ) : ℕ :=
  if hk : 0 < k ∧ k ≤ n + 1 then r (.inl ⟨k - 1, by omega⟩)
  else if k = n + 2 then ∑ j, r (.inr j) else 0

private theorem value_zero {n : ℕ} {ι : Type} [Fintype ι] (r : Vertex n ι → ℕ) :
    value r 0 = 0 := by simp [value]

private theorem value_path {n : ℕ} {ι : Type} [Fintype ι] (r : Vertex n ι → ℕ)
    (i : Fin (n + 1)) : value r (i.val + 1) = r (.inl i) := by
  simp [value, show i.val ≤ n by omega]

private theorem value_leaves {n : ℕ} {ι : Type} [Fintype ι] (r : Vertex n ι → ℕ) :
    value r (n + 2) = ∑ j, r (.inr j) := by simp [value]

private theorem finsum_level {n s : ℕ} (r : Vertex n (Fin s) → ℕ) {k : ℕ} (hk : k ≤ n + 2) :
    (∑ᶠ w ∈ level n s k, r w) = value r k := by
  by_cases h0 : k = 0
  · subst k
    have he : level n s 0 = ∅ := by ext (i | j) <;> simp [level]
    rw [he, finsum_mem_empty, value_zero]
  by_cases ht : k = n + 2
  · subst k
    have he : level n s (n + 2) = Set.range Sum.inr := by
      ext (i | j)
      · have hi := i.isLt
        simp [level, i.isLt.ne]
      · simp [level]
    rw [he, finsum_mem_range Sum.inr_injective, finsum_eq_sum_of_fintype, value_leaves]
  let i : Fin (n + 1) := ⟨k - 1, by omega⟩
  have hi : k = i.val + 1 := by dsimp [i]; omega
  rw [hi, value_path]
  have he : level n s (i.val + 1) = {Sum.inl i} := by
    ext (j | j)
    · simp [level, Fin.ext_iff]
    · have h := i.isLt
      simp [level, show n + 2 ≠ i.val + 1 by omega]
  rw [he, finsum_mem_singleton]

private theorem path_neighborSum {n s : ℕ} (r : Vertex n (Fin s) → ℕ) (i : Fin (n + 1)) :
    (∑ᶠ w ∈ {w | (coconutTree (n + 1) s).Adj (.inl i) w}, r w) =
      value r i.val + value r (i.val + 2) := by
  have he : {w | (coconutTree (n + 1) s).Adj (.inl i) w} =
      level n s i.val ∪ level n s (i.val + 2) := by
    ext (j | j) <;> simp [level, coconutTree_adj_inl_inl, coconutTree_adj_inl_inr] <;> omega
  have hd : Disjoint (level n s i.val) (level n s (i.val + 2)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    simp only [level, Set.mem_ofPred_eq] at hw hw'
    omega
  rw [he, finsum_mem_union hd (Set.toFinite _) (Set.toFinite _), finsum_level (hk := by omega),
    finsum_level (hk := by omega)]

private theorem leaf_neighborSum {n s : ℕ} (r : Vertex n (Fin s) → ℕ) (j : Fin s) :
    (∑ᶠ w ∈ {w | (coconutTree (n + 1) s).Adj (.inr j) w}, r w) = r (center n (Fin s)) := by
  have he : {w | (coconutTree (n + 1) s).Adj (.inr j) w} = {center n (Fin s)} := by
    ext (i | l)
    · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
      simp [Fin.ext_iff]
    · simp [coconutTree_not_adj_inr_inr]
  rw [he, finsum_mem_singleton]

-- Allow d = 0 at the center of the singleton path. The equations force it to be
-- positive whenever there is a second path vertex or a leaf.
private structure Valid {n : ℕ} {ι : Type} [Fintype ι] (x : Labels n ι) : Prop where
  r_pos : ∀ v, 0 < x.2 v
  path_eq : ∀ i : Fin (n + 1), x.1 (.inl i) * x.2 (.inl i) =
    value x.2 i.val + value x.2 (i.val + 2)
  leaf_eq : ∀ j : ι, x.1 (.inr j) * x.2 (.inr j) = x.2 (center n ι)
  primitive : ∀ g : ℕ, (∀ v, g ∣ x.2 v) → g = 1

private theorem Valid.center_pos {n : ℕ} {ι : Type} [Fintype ι] {x : Labels n ι}
    (hx : Valid x) (h : 0 < n ∨ Nonempty ι) : 0 < x.1 (center n ι) := by
  have he := hx.path_eq (Fin.last n)
  change x.1 (center n ι) * x.2 (center n ι) = value x.2 n + value x.2 (n + 2) at he
  apply Nat.pos_of_mul_pos_right
  rw [he, value_leaves]
  rcases h with hn | ⟨⟨j⟩⟩
  · have hv := value_path x.2 (⟨n - 1, by omega⟩ : Fin (n + 1))
    change value x.2 (n - 1 + 1) = _ at hv
    rw [show n - 1 + 1 = n by omega] at hv
    exact Nat.add_pos_left (hv ▸ hx.r_pos _) _
  · refine Nat.add_pos_right _ (Finset.sum_pos' (fun _ _ => Nat.zero_le _) ?_)
    exact ⟨j, mem_univ _, hx.r_pos _⟩

private theorem Valid.d_pos {n : ℕ} {ι : Type} [Fintype ι] {x : Labels n ι}
    (hx : Valid x) (v : Vertex n ι) (hv : v ≠ center n ι) : 0 < x.1 v := by
  suffices h : 0 < x.1 v * x.2 v from Nat.pos_of_mul_pos_right h
  cases v with
  | inr j => exact hx.leaf_eq j ▸ hx.r_pos _
  | inl i =>
    have hi : i.val < n := by
      by_contra! h
      apply hv
      exact congrArg Sum.inl (Fin.ext (by simp; omega))
    rw [hx.path_eq i, show i.val + 2 = (⟨i.val + 1, by omega⟩ : Fin (n + 1)).val + 1 by rfl,
      value_path]
    exact Nat.add_pos_right _ (hx.r_pos _)

private theorem valid_iff {n s : ℕ} (h : 0 < n ∨ 0 < s) (x : Labels n (Fin s)) :
    Valid x ↔ IsArithmeticalStructure (coconutTree (n + 1) s) x.1 x.2 := by
  constructor
  · intro hx
    refine ⟨fun v => ?_, hx.r_pos, ?_, hx.primitive⟩
    · by_cases hv : v = center n (Fin s)
      · subst v
        exact hx.center_pos (h.imp_right fun hs => ⟨⟨0, hs⟩⟩)
      · exact hx.d_pos _ hv
    · rintro (i | j)
      · rw [path_neighborSum]; exact hx.path_eq _
      · rw [leaf_neighborSum]; exact hx.leaf_eq _
  · intro hx
    refine ⟨hx.2.1, ?_, ?_, hx.2.2.2⟩
    · intro i
      rw [← path_neighborSum]; exact hx.2.2.1 _
    · intro j
      exact (hx.2.2.1 (.inr j)).trans (leaf_neighborSum x.2 j)

/-! ## Partition by the leaves with label one -/

private def Structures (n : ℕ) (ι : Type) [Fintype ι] := {x : Labels n ι // Valid x}

private def Reduced (n : ℕ) (ι : Type) [Fintype ι] :=
  {x : Labels n ι // Valid x ∧ ∀ j, x.1 (.inr j) ≠ 1}

private def unitLeaves {n s : ℕ} (x : Structures n (Fin s)) : Finset (Fin s) :=
  univ.filter fun j => x.val.1 (.inr j) = 1

private abbrev Rest {s : ℕ} (u : Finset (Fin s)) := {j : Fin s // j ∉ u}

private def fill {s : ℕ} (u : Finset (Fin s)) (a : Rest u → ℕ) (c : ℕ) (j : Fin s) : ℕ :=
  if h : j ∈ u then c else a ⟨j, h⟩

private theorem fill_sum {s : ℕ} (u : Finset (Fin s)) (a : Rest u → ℕ) (c : ℕ) :
    ∑ j, fill u a c j = u.card * c + ∑ j, a j := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ u)]
  have ha (j : u) : fill u a c j = c := by simp [fill, j.property]
  have hb (j : Rest u) : fill u a c j = a j := by simp [fill, j.property]
  simp [ha, hb]

private def leafExtend {n s : ℕ} (u : Finset (Fin s)) (x : Labels n (Rest u)) :
    Labels n (Fin s) :=
  (Sum.elim (fun i => x.1 (.inl i) + if i = Fin.last n then u.card else 0)
    (fill u (fun j => x.1 (.inr j)) 1),
    Sum.elim (fun i => x.2 (.inl i)) (fill u (fun j => x.2 (.inr j)) (x.2 (center n _))))

private theorem value_leafExtend {n s k : ℕ} (u : Finset (Fin s)) (x : Labels n (Rest u)) :
    value (leafExtend u x).2 k =
      value x.2 k + if k = n + 2 then u.card * x.2 (center n _) else 0 := by
  by_cases h : k = n + 2
  · subst k
    simp [value_leaves, leafExtend, fill_sum, add_comm]
  · simp [value, leafExtend, h]

private theorem valid_leafExtend {n s : ℕ} (u : Finset (Fin s)) (x : Labels n (Rest u)) :
    Valid (leafExtend u x) ↔ Valid x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | j)
      · exact h.r_pos (.inl i)
      · simpa [leafExtend, fill, j.property] using h.r_pos (.inr j.val)
    · intro i
      have he := h.path_eq i
      rw [value_leafExtend, value_leafExtend] at he
      have hi : i.val ≠ n + 2 := by omega
      have ht : i.val + 2 = n + 2 ↔ i = Fin.last n := by simp [Fin.ext_iff]
      simp only [leafExtend, Sum.elim_inl, hi, ite_false, add_zero, ht] at he
      split_ifs at he with hc
      · subst i
        rw [Nat.add_mul] at he
        change _ + u.card * x.2 (center n _) = _ at he
        omega
      · simpa using he
    · intro j
      simpa [leafExtend, fill, j.property] using h.leaf_eq j.val
    · intro g hg
      apply h.primitive g
      rintro (i | j)
      · exact hg (.inl i)
      · by_cases hj : j ∈ u
        · simpa [leafExtend, fill, hj] using hg (center n _)
        · simpa [leafExtend, fill, hj] using hg (.inr ⟨j, hj⟩)
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (i | j)
      · exact h.r_pos (.inl i)
      · by_cases hj : j ∈ u
        · simpa [leafExtend, fill, hj] using h.r_pos (center n _)
        · simpa [leafExtend, fill, hj] using h.r_pos (.inr ⟨j, hj⟩)
    · intro i
      rw [value_leafExtend, value_leafExtend]
      have hi : i.val ≠ n + 2 := by omega
      have ht : i.val + 2 = n + 2 ↔ i = Fin.last n := by simp [Fin.ext_iff]
      have he := h.path_eq i
      simp only [leafExtend, Sum.elim_inl, hi, ite_false, add_zero, ht]
      split_ifs with hc
      · subst i
        rw [Nat.add_mul, he, Nat.add_assoc]
      · simpa using he
    · intro j
      by_cases hj : j ∈ u
      · simp [leafExtend, fill, hj]
      · simpa [leafExtend, fill, hj] using h.leaf_eq ⟨j, hj⟩
    · intro g hg
      apply h.primitive g
      rintro (i | j)
      · exact hg (.inl i)
      · simpa [leafExtend, fill, j.property] using hg (.inr j.val)

private def addUnitLeaves {n s : ℕ} (u : Finset (Fin s)) (x : Reduced n (Rest u)) :
    {y : Structures n (Fin s) // unitLeaves y = u} := by
  refine ⟨⟨leafExtend u x.val, (valid_leafExtend u _).2 x.property.1⟩, ?_⟩
  ext j
  rw [show j ∈ unitLeaves ⟨leafExtend u x.val, (valid_leafExtend u _).2 x.property.1⟩ ↔
    (leafExtend u x.val).1 (.inr j) = 1 by simp [unitLeaves]]
  simp only [leafExtend, Sum.elim_inr]
  by_cases h : j ∈ u
  · simp [fill, h]
  · simp [fill, h, x.property.2 ⟨j, h⟩]

private noncomputable def leafFiberEquiv {n s : ℕ} (u : Finset (Fin s)) :
    Reduced n (Rest u) ≃ {y : Structures n (Fin s) // unitLeaves y = u} := by
  apply Equiv.ofBijective (addUnitLeaves u)
  constructor
  · intro x y h
    have hd (v : Vertex n (Fin s)) : (leafExtend u x.val).1 v = (leafExtend u y.val).1 v :=
      congrArg (fun z : {y : Structures n (Fin s) // unitLeaves y = u} => z.val.val.1 v) h
    have hr (v : Vertex n (Fin s)) : (leafExtend u x.val).2 v = (leafExtend u y.val).2 v :=
      congrArg (fun z : {y : Structures n (Fin s) // unitLeaves y = u} => z.val.val.2 v) h
    apply Subtype.ext
    refine Prod.ext (funext ?_) (funext ?_)
    · rintro (i | j)
      · exact Nat.add_right_cancel (hd (.inl i))
      · simpa [leafExtend, fill, j.property] using hd (.inr j.val)
    · rintro (i | j)
      · exact hr (.inl i)
      · simpa [leafExtend, fill, j.property] using hr (.inr j.val)
  · rintro ⟨⟨y, hy⟩, hu⟩
    have hunit (j : Fin s) : j ∈ u ↔ y.1 (.inr j) = 1 := by
      rw [← hu]; simp [unitLeaves]
    have hcopy (j : u) : y.2 (.inr j.val) = y.2 (center n _) := by
      simpa [(hunit j.val).1 j.property] using hy.leaf_eq j.val
    let x : Labels n (Rest u) :=
      (Sum.elim (fun i => y.1 (.inl i) - if i = Fin.last n then u.card else 0)
        (fun j => y.1 (.inr j.val)),
        Sum.elim (fun i => y.2 (.inl i)) (fun j => y.2 (.inr j.val)))
    have hle : u.card ≤ y.1 (center n _) := by
      have hf : fill u (fun j => y.2 (.inr j.val)) (y.2 (center n _)) =
          (fun j => y.2 (.inr j)) := by
        funext j
        by_cases hj : j ∈ u
        · simpa [fill, hj] using (hcopy ⟨j, hj⟩).symm
        · simp [fill, hj]
      have he := hy.path_eq (Fin.last n)
      rw [Fin.val_last, value_leaves, ← hf, fill_sum] at he
      change y.1 (center n _) * y.2 (center n _) = _ at he
      exact (Nat.mul_le_mul_right_iff (hy.r_pos (center n _))).mp (by omega)
    have he : leafExtend u x = y := by
      refine Prod.ext (funext ?_) (funext ?_)
      · rintro (i | j)
        · by_cases hi : i = Fin.last n
          · subst i; simp [leafExtend, x, Nat.sub_add_cancel hle]
          · simp [leafExtend, x, hi]
        · by_cases hj : j ∈ u
          · simp [leafExtend, x, fill, hj, (hunit j).1 hj]
          · simp [leafExtend, x, fill, hj]
      · rintro (i | j)
        · rfl
        · by_cases hj : j ∈ u
          · simpa [leafExtend, x, fill, hj] using (hcopy ⟨j, hj⟩).symm
          · simp [leafExtend, x, fill, hj]
    refine ⟨⟨x, (valid_leafExtend u x).mp (he ▸ hy), ?_⟩, Subtype.ext (Subtype.ext he)⟩
    exact fun j h => j.property ((hunit j.val).2 h)

private theorem reindex_value {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : Vertex n κ → ℕ) (k : ℕ) :
    value (r ∘ Sum.map id e) k = value r k := by
  by_cases h : k = n + 2
  · subst k
    rw [value_leaves, value_leaves]
    exact e.sum_comp (fun j => r (.inr j))
  · simp [value, h]

private def reindexLabels {n : ℕ} {ι κ : Type} (e : ι ≃ κ) (x : Labels n κ) : Labels n ι :=
  (x.1 ∘ Sum.map id e, x.2 ∘ Sum.map id e)

private theorem valid_reindex {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) {x : Labels n κ} (h : Valid x) : Valid (reindexLabels e x) where
  r_pos _ := h.r_pos _
  path_eq i := by
    change x.1 (.inl i) * x.2 (.inl i) =
      value (x.2 ∘ Sum.map id e) i.val + value (x.2 ∘ Sum.map id e) (i.val + 2)
    rw [reindex_value, reindex_value]
    exact h.path_eq i
  leaf_eq j := h.leaf_eq (e j)
  primitive g hg := by
    apply h.primitive g
    rintro (i | j)
    · exact hg (.inl i)
    · simpa [reindexLabels] using hg (.inr (e.symm j))

private def reindexReduced {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Reduced n ι ≃ Reduced n κ where
  toFun x := ⟨reindexLabels e.symm x.val, valid_reindex e.symm x.property.1,
    fun j => x.property.2 (e.symm j)⟩
  invFun y := ⟨reindexLabels e y.val, valid_reindex e y.property.1, fun j => y.property.2 (e j)⟩
  left_inv x := Subtype.ext (Prod.ext (funext fun v => by cases v <;> simp [reindexLabels])
    (funext fun v => by cases v <;> simp [reindexLabels]))
  right_inv y := Subtype.ext (Prod.ext (funext fun v => by cases v <;> simp [reindexLabels])
    (funext fun v => by cases v <;> simp [reindexLabels]))

private theorem leaf_partition (n s : ℕ) (hfinite : ∀ t, Finite (Reduced n (Fin t))) :
    Nat.card (Structures n (Fin s)) = ∑ j ∈ range (s + 1),
      s.choose j * Nat.card (Reduced n (Fin (s - j))) := by
  classical
  let T (u : Finset (Fin s)) := Reduced n (Rest u)
  let reindex (u : Finset (Fin s)) : T u ≃ Reduced n (Fin (s - u.card)) :=
    reindexReduced (Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl]))
  have (u : Finset (Fin s)) : Finite (T u) := Finite.of_injective _ (reindex u).injective
  have e : Structures n (Fin s) ≃ Σ u : Finset (Fin s), T u :=
    (Equiv.sigmaFiberEquiv unitLeaves).symm.trans
      (Equiv.sigmaCongrRight fun u => (leafFiberEquiv u).symm)
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun u => Nat.card_congr (reindex u)]
  rw [← powerset_univ]
  simpa [nsmul_eq_mul] using
    sum_powerset_apply_card (fun k => Nat.card (Reduced n (Fin (s - k))))
      (x := (univ : Finset (Fin s)))

/-! ## Insertion and contraction on the path -/

private def skip {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → Fin (n + 2) :=
  i.castSucc.succAbove

private theorem skip_left {n : ℕ} {i j : Fin (n + 1)} (h : j < i) : skip i j = j.castSucc :=
  Fin.succAbove_castSucc_of_lt _ _ h

private theorem skip_right {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) : skip i j = j.succ :=
  Fin.succAbove_castSucc_of_le _ _ h

private theorem skip_last {n : ℕ} (i : Fin (n + 1)) : skip i (Fin.last n) = Fin.last (n + 1) :=
  (skip_right i.le_last).trans (Fin.succ_last n)

private def bump {n : ℕ} (i j : Fin (n + 1)) : ℕ :=
  if j.val + 1 = i.val ∨ j = i then 1 else 0

-- Subdivision depends only on the path labels. Use the existing operation on those
-- labels and carry the leaves along unchanged, regardless of their index type.
private def pathExtend {n : ℕ} {ι : Type} (i : Fin (n + 1)) (x : Labels n ι) :
    Labels (n + 1) ι :=
  let path : Labels n (Fin 0) :=
    (Sum.elim (fun j => x.1 (.inl j)) Fin.elim0, Sum.elim (fun j => x.2 (.inl j)) Fin.elim0)
  let y := coconutSubdivide i path
  (Sum.elim (fun j => y.1 (.inl j)) (fun j => x.1 (.inr j)),
    Sum.elim (fun j => y.2 (.inl j)) (fun j => x.2 (.inr j)))

private theorem extend_d_skip {n : ℕ} {ι : Type}
    (i j : Fin (n + 1)) (x : Labels n ι) :
    (pathExtend i x).1 (.inl (skip i j)) = x.1 (.inl j) + bump i j := by
  by_cases hj : j < i
  · rw [skip_left hj]
    have hne : j ≠ i := ne_of_lt hj
    by_cases h : j.val + 1 = i.val
    · simp [pathExtend, coconutSubdivide, bump, h, show j.val ≤ n by omega]
    · simp [pathExtend, coconutSubdivide, bump, h, hne, show j.val + 1 < i.val by omega,
        show j.val ≤ n by omega]
  · rw [skip_right (le_of_not_gt hj)]
    simp only [pathExtend, coconutSubdivide, Sum.elim_inl, Fin.val_succ, bump,
      show ¬j.val + 1 + 1 < i.val by omega, show j.val + 1 + 1 ≠ i.val by omega,
      show j.val + 1 ≠ i.val by omega, ite_false, false_or, Nat.add_sub_cancel, j.isLt,
      dite_true, Nat.add_right_cancel_iff, ← Fin.ext_iff]
    split_ifs <;> simp

private theorem extend_r_skip {n : ℕ} {ι : Type}
    (i j : Fin (n + 1)) (x : Labels n ι) :
    (pathExtend i x).2 (.inl (skip i j)) = x.2 (.inl j) := by
  by_cases hj : j < i
  · rw [skip_left hj]
    simp [pathExtend, coconutSubdivide, show j.val < i.val from hj, show j.val ≤ n by omega]
  · rw [skip_right (le_of_not_gt hj)]
    simp [pathExtend, coconutSubdivide, show ¬j.val + 1 < i.val by omega,
      show j.val + 1 ≠ i.val by omega, show j.val ≤ n by omega]

private theorem extend_d_insert {n : ℕ} {ι : Type}
    (i : Fin (n + 1)) (x : Labels n ι) : (pathExtend i x).1 (.inl i.castSucc) = 1 := by
  simp [pathExtend, coconutSubdivide]

private theorem extend_r_insert {n : ℕ} {ι : Type} [Fintype ι]
    (i : Fin (n + 1)) (x : Labels n ι) :
    (pathExtend i x).2 (.inl i.castSucc) = value x.2 i.val + value x.2 (i.val + 1) := by
  rw [value_path]
  by_cases h : i.val = 0
  · obtain rfl : i = 0 := Fin.ext h
    simp [pathExtend, coconutSubdivide, value_zero]
  · have hi := i.isLt
    simp [pathExtend, coconutSubdivide, value, h, hi, show i.val - 1 < n + 1 by omega,
      show i.val ≤ n + 1 by omega, Nat.pos_of_ne_zero h]

private theorem extend_value_left {n : ℕ} {ι : Type} [Fintype ι]
    (i : Fin (n + 1)) (x : Labels n ι) {k : ℕ} (h : k ≤ i.val) :
    value (pathExtend i x).2 k = value x.2 k := by
  by_cases hz : k = 0
  · simp [hz, value_zero]
  let j : Fin (n + 1) := ⟨k - 1, by omega⟩
  have hj : j.val + 1 = k := by dsimp [j]; omega
  have hj' : j < i := by change k - 1 < i.val; omega
  have he := extend_r_skip i j x
  rw [skip_left hj'] at he
  calc
    value (pathExtend i x).2 k = (pathExtend i x).2 (.inl j.castSucc) :=
      hj ▸ value_path _ j.castSucc
    _ = x.2 (.inl j) := he
    _ = value x.2 k := hj ▸ (value_path _ j).symm

private theorem extend_value_right {n : ℕ} {ι : Type} [Fintype ι]
    (i : Fin (n + 1)) (x : Labels n ι) {k : ℕ} (h : i.val + 1 < k) (hk : k ≤ n + 3) :
    value (pathExtend i x).2 k = value x.2 (k - 1) := by
  by_cases ht : k = n + 3
  · subst k
    rw [show n + 3 = n + 1 + 2 by omega, show n + 1 + 2 - 1 = n + 2 by omega,
      value_leaves, value_leaves]
    rfl
  let j : Fin (n + 1) := ⟨k - 2, by omega⟩
  have hj : j.val + 1 = k - 1 := by dsimp [j]; omega
  have hj' : j.succ.val + 1 = k := by simp [j]; omega
  have hij : i ≤ j := by change i.val ≤ k - 2; omega
  calc
    value (pathExtend i x).2 k = (pathExtend i x).2 (.inl j.succ) := hj' ▸ value_path _ _
    _ = x.2 (.inl j) := skip_right hij ▸ extend_r_skip i j x
    _ = value x.2 (k - 1) := hj ▸ (value_path _ j).symm

private theorem extend_value_insert {n : ℕ} {ι : Type} [Fintype ι]
    (i : Fin (n + 1)) (x : Labels n ι) :
    value (pathExtend i x).2 (i.val + 1) = value x.2 i.val + value x.2 (i.val + 1) := by
  rw [← Fin.val_castSucc (i := i), value_path, Fin.val_castSucc, extend_r_insert]

private theorem extend_path_equation {n : ℕ} {ι : Type} [Fintype ι]
    (i j : Fin (n + 1)) (x : Labels n ι) :
    let y := pathExtend i x
    let k := skip i j
    y.1 (.inl k) * y.2 (.inl k) = value y.2 k.val + value y.2 (k.val + 2) ↔
      x.1 (.inl j) * x.2 (.inl j) = value x.2 j.val + value x.2 (j.val + 2) := by
  dsimp only
  rw [extend_d_skip, extend_r_skip]
  by_cases hj : j < i
  · rw [skip_left hj, Fin.val_castSucc, extend_value_left _ _ hj.le]
    have hne : j ≠ i := ne_of_lt hj
    by_cases h : j.val + 1 = i.val
    · rw [show j.val + 2 = i.val + 1 by omega, extend_value_insert, ← h,
        value_path, bump, ite_eq_left (Or.inl h), Nat.add_mul, one_mul]
      omega
    · rw [extend_value_left _ _ (by omega), bump, ite_eq_right (by simp [h, hne]),
        Nat.add_zero]
  · have hj' : i ≤ j := le_of_not_gt hj
    rw [skip_right hj', Fin.val_succ, extend_value_right _ _ (by omega : i.val + 1 < j.val + 1 + 2)
      (by omega), show j.val + 1 + 2 - 1 = j.val + 2 by omega]
    have hne : j.val + 1 ≠ i.val := by omega
    by_cases h : j = i
    · subst j
      rw [extend_value_insert, value_path, bump, ite_eq_left (Or.inr rfl), Nat.add_mul, one_mul]
      omega
    · rw [extend_value_right _ _ (by have := Fin.val_ne_of_ne h; omega) (by omega),
        Nat.add_sub_cancel, bump, ite_eq_right (by simp [h, hne]), Nat.add_zero]

private theorem valid_pathExtend {n : ℕ} {ι : Type} [Fintype ι]
    (i : Fin (n + 1)) (x : Labels n ι) : Valid (pathExtend i x) ↔ Valid x := by
  constructor
  · intro h
    refine ⟨?_, fun j => (extend_path_equation i j x).mp (h.path_eq _), ?_, ?_⟩
    · rintro (j | l)
      · rw [← extend_r_skip i j x]; exact h.r_pos _
      · exact h.r_pos (.inr l)
    · intro l
      have he := h.leaf_eq l
      change x.1 (.inr l) * x.2 (.inr l) = (pathExtend i x).2 (.inl (Fin.last (n + 1))) at he
      rw [← skip_last i, extend_r_skip] at he
      exact he
    · intro g hg
      apply h.primitive g
      rintro (j | l)
      · refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
        · rw [extend_r_insert, value_path]
          apply dvd_add ?_ (hg (.inl i))
          by_cases hz : i.val = 0
          · simp [hz, value_zero]
          · have he : (⟨i.val - 1, by omega⟩ : Fin (n + 1)).val + 1 = i.val := by simp; omega
            rw [← he, value_path]
            exact hg _
        · exact (extend_r_skip i k x).symm ▸ hg (.inl k)
      · exact hg (.inr l)
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (j | l)
      · refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
        · rw [extend_r_insert, value_path]
          exact Nat.add_pos_right _ (h.r_pos _)
        · change 0 < (pathExtend i x).2 (.inl (skip i k))
          rw [extend_r_skip]; exact h.r_pos _
      · exact h.r_pos (.inr l)
    · refine Fin.succAboveCases i.castSucc ?_ fun k =>
        (extend_path_equation i k x).mpr (h.path_eq k)
      simp only [Fin.val_castSucc, extend_d_insert, one_mul, extend_r_insert]
      rw [extend_value_left _ _ le_rfl, extend_value_right _ _ (by omega : i.val + 1 < i.val + 2)
        (by omega), show i.val + 2 - 1 = i.val + 1 by omega]
    · intro l
      rw [show (pathExtend i x).2 (center (n + 1) ι) = x.2 (center n ι) by
        change (pathExtend i x).2 (.inl (Fin.last (n + 1))) = _
        rw [← skip_last i, extend_r_skip]]
      exact h.leaf_eq l
    · intro g hg
      apply h.primitive g
      rintro (j | l)
      · exact extend_r_skip i j x ▸ hg (.inl (skip i j))
      · exact hg (.inr l)

-- `Stage n ι k` allows a noncentral path vertex to have `d = 1` only at indices below `k`.
private def Stage (n : ℕ) (ι : Type) [Fintype ι] (k : ℕ) :=
  {x : Labels n ι // Valid x ∧ (∀ j, x.1 (.inr j) ≠ 1) ∧
    ∀ j : Fin (n + 1), k ≤ j.val → j.val < n → x.1 (.inl j) ≠ 1}

private theorem Stage.path_pos {n k : ℕ} {ι : Type} [Fintype ι] (x : Stage (n + 1) ι k)
    (j : Fin (n + 2)) : 0 < x.val.1 (.inl j) := by
  by_cases h : j = Fin.last (n + 1)
  · subst j
    exact x.property.1.center_pos (Or.inl (by omega))
  · exact x.property.1.d_pos _ (fun he => h (Sum.inl.inj he))

private noncomputable def stageExtend {n : ℕ} {ι : Type} [Fintype ι] (i : Fin (n + 1))
    (x : Stage n ι (i.val + 1)) :
    {y : Stage (n + 1) ι (i.val + 1) // y.val.1 (.inl i.castSucc) = 1} := by
  refine ⟨⟨pathExtend i x.val, (valid_pathExtend i _).2 x.property.1, x.property.2.1, ?_⟩,
    extend_d_insert _ _⟩
  intro j hj hj'
  rcases Fin.eq_self_or_eq_succAbove i.castSucc j with rfl | ⟨k, rfl⟩
  · simp at hj
  change i.val + 1 ≤ (skip i k).val at hj
  change (skip i k).val < n + 1 at hj'
  change (pathExtend i x.val).1 (.inl (skip i k)) ≠ 1
  have hik : i ≤ k := by
    by_contra! h
    rw [skip_left h, Fin.val_castSucc] at hj
    omega
  rw [skip_right hik, Fin.val_succ] at hj hj'
  rw [extend_d_skip, bump]
  by_cases h : k = i
  · rw [ite_eq_left (Or.inr h)]
    have hp := x.property.1.d_pos (.inl k) (by
      intro he
      have hval := congrArg Fin.val (Sum.inl.inj he)
      simp at hval
      omega)
    omega
  · rw [ite_eq_right (by have := hik; simp [show k.val + 1 ≠ i.val by omega, h]), Nat.add_zero]
    have hne := Fin.val_ne_of_ne h
    exact x.property.2.2 k (by omega) (by omega)

private noncomputable def pathFiberEquiv {n : ℕ} {ι : Type} [Fintype ι] (i : Fin (n + 1)) :
    Stage n ι (i.val + 1) ≃ {y : Stage (n + 1) ι (i.val + 1) // y.val.1 (.inl i.castSucc) = 1} := by
  apply Equiv.ofBijective (stageExtend i)
  constructor
  · intro x y h
    have he : pathExtend i x.val = pathExtend i y.val :=
      congrArg (fun z : {y : Stage (n + 1) ι (i.val + 1) // y.val.1 (.inl i.castSucc) = 1} =>
        z.val.val) h
    apply Subtype.ext
    refine Prod.ext (funext ?_) (funext ?_)
    · rintro (j | l)
      · have hd := congrArg (fun z : Labels (n + 1) ι => z.1 (.inl (skip i j))) he
        rw [extend_d_skip, extend_d_skip] at hd
        omega
      · exact congrArg (fun z : Labels (n + 1) ι => z.1 (.inr l)) he
    · rintro (j | l)
      · rw [← extend_r_skip i j x.val, ← extend_r_skip i j y.val, he]
      · exact congrArg (fun z : Labels (n + 1) ι => z.2 (.inr l)) he
  · rintro ⟨y, hy⟩
    let x : Labels n ι :=
      (Sum.elim (fun j => y.val.1 (.inl (skip i j)) - bump i j) (fun l => y.val.1 (.inr l)),
        Sum.elim (fun j => y.val.2 (.inl (skip i j))) (fun l => y.val.2 (.inr l)))
    have hr_extend : (pathExtend i x).2 = y.val.2 := by
      funext v
      rcases v with j | l
      · refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
        · have he := y.property.1.path_eq i.castSucc
          rw [hy, one_mul, Fin.val_castSucc] at he
          rw [extend_r_insert, he]
          congr 1
          · by_cases hz : i.val = 0
            · simp [hz, value_zero]
            let a : Fin (n + 1) := ⟨i.val - 1, by omega⟩
            have ha : a.val + 1 = i.val := by dsimp [a]; omega
            have hai : a < i := by change i.val - 1 < i.val; omega
            calc
              value x.2 i.val = x.2 (.inl a) := ha ▸ value_path _ _
              _ = y.val.2 (.inl a.castSucc) := by
                change y.val.2 (.inl (skip i a)) = _
                rw [skip_left hai]
              _ = value y.val.2 i.val := by
                have hc : a.castSucc.val + 1 = i.val := ha
                exact ((congrArg (value y.val.2) hc).symm.trans (value_path _ _)).symm
          · rw [value_path]
            calc
              x.2 (.inl i) = y.val.2 (.inl i.succ) := by
                change y.val.2 (.inl (skip i i)) = _; rw [skip_right le_rfl]
              _ = value y.val.2 (i.val + 2) := (value_path _ i.succ).symm
        · exact extend_r_skip i k x
      · rfl
    have hd_extend : (pathExtend i x).1 = y.val.1 := by
      funext v
      rcases v with j | l
      · refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
        · rw [extend_d_insert, hy]
        · change (pathExtend i x).1 (.inl (skip i k)) = _
          rw [extend_d_skip]
          apply Nat.sub_add_cancel
          have hp := y.path_pos (skip i k)
          change bump i k ≤ y.val.1 (.inl (skip i k))
          unfold bump
          split <;> omega
      · rfl
    have he := Prod.ext hd_extend hr_extend
    refine ⟨⟨x, (valid_pathExtend i x).mp (he ▸ y.property.1), y.property.2.1, ?_⟩,
      Subtype.ext (Subtype.ext he)⟩
    intro k hk hk'
    have hik : i ≤ k := by omega
    have hkne : k ≠ i := by intro h; subst k; omega
    change y.val.1 (.inl (skip i k)) - bump i k ≠ 1
    rw [skip_right hik, bump, ite_eq_right (by simp [show k.val + 1 ≠ i.val by omega, hkne]),
      Nat.sub_zero]
    exact y.property.2.2 k.succ (by simp; omega) (by simp; omega)

private noncomputable def stageStep {n : ℕ} {ι : Type} [Fintype ι] (i : Fin (n + 1)) :
    Stage (n + 1) ι (i.val + 1) ≃ Stage (n + 1) ι i.val ⊕ Stage n ι (i.val + 1) := by
  classical
  apply (Equiv.sumCompl (fun y : Stage (n + 1) ι (i.val + 1) =>
    y.val.1 (.inl i.castSucc) ≠ 1)).symm.trans
  apply Equiv.sumCongr
  · refine ⟨fun y => ⟨y.val.val, y.val.property.1, y.val.property.2.1, ?_⟩,
      fun y => ⟨⟨y.val, y.property.1, y.property.2.1,
        fun j hj => y.property.2.2 j (by omega)⟩, y.property.2.2 i.castSucc le_rfl i.isLt⟩,
      fun _ => rfl, fun _ => rfl⟩
    intro j hj hj'
    by_cases h : j = i.castSucc
    · subst j; exact y.property
    · have he := Fin.val_ne_of_ne h
      exact y.val.property.2.2 j (by simp at he; omega) hj'
  · exact (Equiv.subtypeEquivRight (fun _ => not_not)).trans (pathFiberEquiv i).symm

/-! ## Finiteness of the labeling sets -/

private theorem sum_adj {α : Type} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (r : α → ℕ) (v : α) :
    (∑ᶠ w ∈ {w | G.Adj v w}, r w) = ∑ w, if G.Adj v w then r w else 0 := by
  rw [finsum_mem_eq_finite_toFinset_sum r (Set.toFinite _), ← sum_filter]
  congr 1
  ext w
  simp

-- Multiplying the two systems by the other system's positive labels and summing
-- gives equal weighted diagonal sums because adjacency is symmetric.
private theorem graph_diagonal_eq {α : Type} [Finite α] {G : SimpleGraph α}
    {d e r t : α → ℕ} (hr : IsArithmeticalStructure G d r)
    (ht : IsArithmeticalStructure G e t) (hde : d ≤ e) : d = e := by
  classical
  let _ := Fintype.ofFinite α
  have hsum (d r t : α → ℕ) (h : IsArithmeticalStructure G d r) :
      ∑ i, d i * (r i * t i) = ∑ i, ∑ j, if G.Adj i j then r j * t i else 0 := by
    refine sum_congr rfl fun i _ => ?_
    rw [← Nat.mul_assoc, h.2.2.1 i, sum_adj, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split <;> simp_all
  have he : ∑ i, d i * (r i * t i) = ∑ i, e i * (r i * t i) := by
    simp_rw [Nat.mul_comm (r _) (t _)]
    rw [hsum e t r ht]
    simp_rw [Nat.mul_comm (t _) (r _)]
    rw [hsum d r t hr, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [G.adj_comm]
  funext i
  apply le_antisymm (hde i)
  by_contra! h
  have hlt := sum_lt_sum (s := univ) (f := fun j => d j * (r j * t j))
    (g := fun j => e j * (r j * t j)) (fun j _ => Nat.mul_le_mul_right _ (hde j))
    ⟨i, mem_univ _, (Nat.mul_lt_mul_right (Nat.mul_pos (hr.2.1 i) (ht.2.1 i))).mpr h⟩
  omega

private theorem r_eq_of_d_eq {n : ℕ} {ι : Type} [Fintype ι] {x y : Labels n ι}
    (hx : Valid x) (hy : Valid y) (hd : x.1 = y.1) : x.2 = y.2 := by
  let a := x.2 (.inl 0)
  let b := y.2 (.inl 0)
  have hpath (k : ℕ) (hk : k ≤ n + 1) : b * value x.2 k = a * value y.2 k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases h0 : k = 0
      · simp [h0, value_zero]
      by_cases h1 : k = 1
      · subst k
        change b * value x.2 ((0 : Fin (n + 1)).val + 1) =
          a * value y.2 ((0 : Fin (n + 1)).val + 1)
        rw [value_path, value_path]
        exact Nat.mul_comm b a
      let i : Fin (n + 1) := ⟨k - 2, by omega⟩
      have hi : i.val + 2 = k := by dsimp [i]; omega
      have hi₀ := ih i.val (by omega) (by omega)
      have hi₁ := ih (i.val + 1) (by omega) (by omega)
      rw [value_path, value_path] at hi₁
      have he : b * (value x.2 i.val + value x.2 (i.val + 2)) =
          a * (value y.2 i.val + value y.2 (i.val + 2)) := calc
        _ = x.1 (.inl i) * (b * x.2 (.inl i)) := by rw [← hx.path_eq]; ac_rfl
        _ = y.1 (.inl i) * (a * y.2 (.inl i)) := by rw [← hd, hi₁]
        _ = _ := by rw [← hy.path_eq]; ac_rfl
      rw [Nat.mul_add, Nat.mul_add, hi, hi₀] at he
      omega
  have hcross (v : Vertex n ι) : b * x.2 v = a * y.2 v := by
    cases v with
    | inl j => simpa only [value_path] using hpath (j.val + 1) (by omega)
    | inr j =>
      have hc : b * x.2 (center n ι) = a * y.2 (center n ι) := by
        simpa only [value_path] using hpath ((Fin.last n).val + 1) (by simp)
      have he : x.1 (.inr j) * (b * x.2 (.inr j)) = x.1 (.inr j) * (a * y.2 (.inr j)) := calc
        _ = b * x.2 (center n ι) := by rw [← hx.leaf_eq]; ac_rfl
        _ = a * y.2 (center n ι) := hc
        _ = _ := by rw [← hy.leaf_eq, ← hd]; ac_rfl
      exact Nat.eq_of_mul_eq_mul_left (hx.d_pos _ (by simp [center])) he
  have gcd_r (z : Labels n ι) (hz : Valid z) : univ.gcd z.2 = 1 :=
    hz.primitive _ (fun v => Finset.gcd_dvd (mem_univ v))
  have hab : b = a := by
    have he := congrArg (fun f : Vertex n ι → ℕ => univ.gcd f) (funext hcross)
    change (univ.gcd fun v => b * x.2 v) = (univ.gcd fun v => a * y.2 v) at he
    rw [Finset.gcd_mul_left, Finset.gcd_mul_left, gcd_r x hx, gcd_r y hy] at he
    simpa using he
  funext v
  apply Nat.eq_of_mul_eq_mul_left (hx.r_pos (.inl 0))
  change a * x.2 v = a * y.2 v
  have hc := hcross v
  rw [hab] at hc
  exact hc

private theorem isolated_labels {x : Labels 0 (Fin 0)} (hx : Valid x) : x = (0, 1) := by
  have hzero : x.1 (.inl 0) = 0 := by
    have he := hx.path_eq (0 : Fin 1)
    change x.1 (.inl 0) * x.2 (.inl 0) = value x.2 0 + value x.2 2 at he
    have hz : value x.2 2 = 0 := (value_leaves x.2).trans (by simp)
    rw [value_zero, hz] at he
    exact (Nat.mul_eq_zero.mp he).resolve_right (hx.r_pos (.inl 0)).ne'
  have hone : x.2 (.inl 0) = 1 := by
    apply hx.primitive
    rintro (i | j)
    · rw [Fin.eq_zero i]
    · exact j.elim0
  refine Prod.ext (funext ?_) (funext ?_)
  · rintro (i | j)
    · rw [Fin.eq_zero i]; exact hzero
    · exact j.elim0
  · rintro (i | j)
    · rw [Fin.eq_zero i]; exact hone
    · exact j.elim0

-- The possible `d`-vectors form an antichain in a finite product of copies of `ℕ`.
private theorem finite_structures (n s : ℕ) : Finite (Structures n (Fin s)) := by
  classical
  by_cases h : 0 < n ∨ 0 < s
  · let D : Set (Vertex n (Fin s) → ℕ) := Set.range (fun x : Structures n (Fin s) => x.val.1)
    have he : IsAntichain (· ≤ ·) D := by
      rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hxy hle
      exact hxy (graph_diagonal_eq ((valid_iff h _).mp x.property) ((valid_iff h _).mp y.property)
        hle)
    let : Finite D := (WellQuasiOrderedLE.finite_of_isAntichain he).to_subtype
    refine Finite.of_injective (fun x : Structures n (Fin s) => (⟨x.val.1, ⟨x, rfl⟩⟩ : D)) ?_
    intro x y hxy
    have hd : x.val.1 = y.val.1 := congrArg Subtype.val hxy
    exact Subtype.ext (Prod.ext hd (r_eq_of_d_eq x.property y.property hd))
  · have hn : n = 0 := by omega
    have hs : s = 0 := by omega
    subst n s
    let : Subsingleton (Structures 0 (Fin 0)) := ⟨fun x y => Subtype.ext
      ((isolated_labels x.property).trans (isolated_labels y.property).symm)⟩
    infer_instance

private theorem finite_reduced (n s : ℕ) : Finite (Reduced n (Fin s)) :=
  let _ : Finite (Structures n (Fin s)) := finite_structures n s
  Finite.of_injective (β := Structures n (Fin s))
    (fun x : Reduced n (Fin s) => ⟨x.val, x.property.1⟩)
    (fun _ _ h => Subtype.ext (congrArg (fun z : Structures n (Fin s) => z.val) h))

private theorem finite_stage (n s k : ℕ) : Finite (Stage n (Fin s) k) :=
  let _ : Finite (Structures n (Fin s)) := finite_structures n s
  Finite.of_injective (β := Structures n (Fin s))
    (fun x : Stage n (Fin s) k => ⟨x.val, x.property.1⟩)
    (fun _ _ h => Subtype.ext (congrArg (fun z : Structures n (Fin s) => z.val) h))

/-! ## Solve the counting recurrence -/

private noncomputable def stageFull (n s k : ℕ) (hk : n ≤ k) :
    Stage n (Fin s) k ≃ Reduced n (Fin s) :=
  Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, fun _ h₁ h₂ => by omega⟩⟩

-- A difference of binomial coefficients, including the initial condition at k = 0.
private def weight (n k q : ℕ) : ℤ :=
  if k = 0 then if q = n then 1 else 0
  else ((k - 1 + (n - q)).choose (n - q) : ℤ) - (k - 1 + (n - q)).choose (n + 1)

private theorem weight_self {n k : ℕ} (hk : k ≤ n + 1) : weight n k n = 1 := by
  by_cases h : k = 0
  · simp [weight, h]
  · simp [weight, h, Nat.choose_eq_zero_of_lt (show k - 1 < n + 1 by omega)]

private theorem weight_step {n k q : ℕ} (hk : k ≤ n) (hq : q ≤ n) :
    weight (n + 1) (k + 1) q = weight (n + 1) k q + weight n (k + 1) q := by
  have hr : n + 1 - q = n - q + 1 := by omega
  cases k with
  | zero =>
    simp [weight, show q ≠ n + 1 by omega,
      Nat.choose_eq_zero_of_lt (show n + 1 - q < n + 2 by omega),
      Nat.choose_eq_zero_of_lt (show n - q < n + 1 by omega)]
  | succ k =>
    simp only [weight, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [hr, show k + 1 + (n - q + 1) = k + (n - q + 1) + 1 by omega,
      show k + (n - q + 1) = k + 1 + (n - q) by omega,
      Nat.choose_succ_succ', Nat.choose_succ_succ' _ (n + 1)]
    push_cast
    omega

-- At the end of the path there is no further position to contract.
private theorem weight_stable {n q : ℕ} (hq : q ≤ n) : weight n (n + 1) q = weight n n q := by
  by_cases h : q = n
  · subst q
    rw [weight_self (by omega), weight_self (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, m + 1 - q = r + 1 := ⟨m - q, by omega⟩
  rw [weight, weight, ite_eq_right (by omega), ite_eq_right (by omega), hr,
    Nat.add_sub_cancel, Nat.add_sub_cancel]
  rw [show m + 1 + (r + 1) = m + (r + 1) + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_succ_succ' _ (m + 1),
    Nat.choose_symm_of_eq_add (a := r) (b := m + 1) (by omega : m + (r + 1) = r + (m + 1))]
  push_cast
  omega

private theorem ballot_eq_choose_diff {n r : ℕ} (hr : r ≤ n) :
    (ballotNumber n r : ℤ) = ((n + r).choose n : ℤ) - (n + r).choose (n + 1) := by
  let a := (n + r).choose n
  let b := (n + r).choose (n + 1)
  have hab : b * (n + 1) = a * r := by
    simpa [a, b] using Nat.choose_succ_right_eq (n + r) n
  have hle : b ≤ a := (Nat.mul_le_mul_right_iff (Nat.succ_pos n)).mp
    (hab ▸ (Nat.mul_le_mul_left a (show r ≤ n + 1 by omega)))
  have he : (a - b) * (n + 1) = (n + 1 - r) * a := by
    rw [Nat.sub_mul, Nat.sub_mul, hab, Nat.mul_comm a, Nat.mul_comm a r]
  change (ballotNumber n r : ℤ) = (a : ℤ) - b
  rw [ballotNumber]
  change (((n + 1 - r) * a / (n + 1) : ℕ) : ℤ) = (a : ℤ) - b
  rw [← he, Nat.mul_div_cancel _ (Nat.succ_pos n), Nat.cast_sub hle]

private theorem weight_ballot {n q : ℕ} (hq : q ≤ n) :
    weight n n q = ballotNumber n (n - q) := by
  cases n with
  | zero => simp [show q = 0 by omega, weight, ballotNumber_zero_right]
  | succ n =>
    let r := n + 1 - q
    have he := ballot_eq_choose_diff (n := n + 1) (r := r) (by omega)
    change weight (n + 1) (n + 1) q = (ballotNumber (n + 1) r : ℤ)
    rw [he]
    simp only [weight, Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false]
    change ((n + r).choose r : ℤ) - (n + r).choose (n + 1 + 1) = _
    rw [show n + 1 + r = n + r + 1 by omega, Nat.choose_succ_succ', Nat.choose_succ_succ' _ (n + 1),
      Nat.choose_symm_of_eq_add (a := r) (b := n) (by omega : n + r = r + n)]
    push_cast
    omega

private theorem stage_count (n s k : ℕ) (hk : k ≤ n + 1) :
    (Nat.card (Stage n (Fin s) k) : ℤ) = ∑ q ∈ range (n + 1),
      weight n k q * Nat.card (Stage q (Fin s) 0) := by
  let S (q : ℕ) := (Nat.card (Stage q (Fin s) 0) : ℤ)
  change _ = ∑ q ∈ range (n + 1), weight n k q * S q
  have hzero (n : ℕ) : S n = ∑ q ∈ range (n + 1), weight n 0 q * S q := by
    rw [sum_range_succ, weight_self (by omega), one_mul]
    rw [sum_eq_zero (fun q hq => by simp [weight, ne_of_lt (mem_range.mp hq)]), zero_add]
  have full (n : ℕ) : Nat.card (Stage n (Fin s) (n + 1)) = Nat.card (Stage n (Fin s) n) :=
    Nat.card_congr ((stageFull n s _ (by omega)).trans (stageFull n s _ le_rfl).symm)
  induction n generalizing k with
  | zero =>
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl
    · exact hzero 0
    · rw [full, sum_range_one, weight_self (by omega), one_mul]
  | succ n ih =>
    have hwithin (k : ℕ) (hk : k ≤ n + 1) :
        (Nat.card (Stage (n + 1) (Fin s) k) : ℤ) = ∑ q ∈ range (n + 1 + 1),
          weight (n + 1) k q * S q := by
      induction k with
      | zero => exact hzero (n + 1)
      | succ k hkprev =>
        let i : Fin (n + 1) := ⟨k, by omega⟩
        have e := Nat.card_congr (stageStep (ι := Fin s) i)
        change Nat.card (Stage (n + 1) (Fin s) (k + 1)) =
          Nat.card (Stage (n + 1) (Fin s) k ⊕ Stage n (Fin s) (k + 1)) at e
        let _ := finite_stage (n + 1) s k
        let _ := finite_stage n s (k + 1)
        rw [Nat.card_sum] at e
        rw [e, Nat.cast_add, hkprev (by omega), ih (k + 1) hk]
        rw [sum_range_succ (f := fun q => weight (n + 1) k q * S q),
          sum_range_succ (f := fun q => weight (n + 1) (k + 1) q * S q),
          weight_self (by omega), weight_self (by omega), one_mul,
          add_right_comm, ← sum_add_distrib]
        congr 1
        refine sum_congr rfl fun q hq => ?_
        rw [weight_step (by omega) (by have := mem_range.mp hq; omega), add_mul]
    by_cases h : k ≤ n + 1
    · exact hwithin k h
    · obtain rfl : k = n + 1 + 1 := by omega
      rw [full, hwithin _ le_rfl]
      refine sum_congr rfl fun q hq => ?_
      rw [weight_stable (by have := mem_range.mp hq; omega)]

private theorem reduced_count (n s : ℕ) :
    Nat.card (Reduced n (Fin s)) = ∑ q ∈ range (n + 1),
      ballotNumber n (n - q) * Nat.card (Stage q (Fin s) 0) := by
  rw [← Nat.card_congr (stageFull n s n le_rfl)]
  apply Int.ofNat_inj.mp
  rw [stage_count n s n (by omega)]
  push_cast
  exact sum_congr rfl fun q hq => by rw [weight_ballot (by have := mem_range.mp hq; omega)]

/-! ## Path cases and the coconut count term -/

private theorem isolated_valid : Valid ((0, 1) : Labels 0 (Fin 0)) := by
  refine ⟨fun _ => Nat.one_pos, ?_, fun j => j.elim0, ?_⟩
  · intro i
    rw [Fin.eq_zero i]
    simp [value_zero, value_leaves]
  · exact fun g h => Nat.dvd_one.mp (h (.inl 0))

private theorem no_smooth_path (n : ℕ) (hn : 0 < n) (x : Stage n (Fin 0) 0) : False := by
  have hgrow (k : ℕ) (hk : k ≤ n) : value x.val.2 k < value x.val.2 (k + 1) := by
    induction k with
    | zero =>
      change value x.val.2 0 < value x.val.2 ((0 : Fin (n + 1)).val + 1)
      rw [value_zero, value_path]
      exact x.property.1.r_pos _
    | succ k ih =>
      let i : Fin (n + 1) := ⟨k, by omega⟩
      have hp := x.property.1.d_pos (.inl i) (by
        intro h
        have he := congrArg Fin.val (Sum.inl.inj h)
        change k = n at he
        omega)
      have hne := x.property.2.2 i (Nat.zero_le _) (by change k < n; omega)
      have htwo : 2 ≤ x.val.1 (.inl i) := by omega
      have he := x.property.1.path_eq i
      have hr := value_path x.val.2 i
      have hb := Nat.mul_le_mul_right (x.val.2 (.inl i)) htwo
      change _ = value x.val.2 k + value x.val.2 (k + 2) at he
      change value x.val.2 (k + 1) = _ at hr
      have hprev := ih (by omega)
      change value x.val.2 (k + 1) < value x.val.2 (k + 2)
      omega
  have h := hgrow n le_rfl
  have he := x.property.1.path_eq (Fin.last n)
  have hp := x.property.1.center_pos (Or.inl hn)
  have hb := Nat.mul_le_mul_right (x.val.2 (center n _)) (show 1 ≤ x.val.1 (center n _) from hp)
  have hc := value_path x.val.2 (Fin.last n)
  have hz : value x.val.2 (n + 2) = 0 := (value_leaves _).trans (by simp)
  simp only [Fin.val_last, hz, Nat.add_zero] at he
  change value x.val.2 (n + 1) = x.val.2 (center n _) at hc
  change x.val.1 (center n _) * x.val.2 (center n _) = _ at he
  rw [one_mul] at hb
  omega

private theorem isolated_stage_count : Nat.card (Stage 0 (Fin 0) 0) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  have x : Stage 0 (Fin 0) 0 := ⟨(0, 1), isolated_valid, fun j => j.elim0,
    fun _ _ h => (Nat.not_lt_zero _ h).elim⟩
  exact ⟨⟨fun y z => Subtype.ext ((isolated_labels y.property.1).trans
    (isolated_labels z.property.1).symm)⟩, ⟨x⟩⟩

private theorem path_count (n : ℕ) : Nat.card (Reduced n (Fin 0)) = catalan n := by
  rw [reduced_count]
  rw [Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, ballotNumber_self, isolated_stage_count, mul_one]
  · intro q _ hq
    have : IsEmpty (Stage q (Fin 0) 0) := ⟨no_smooth_path q (by omega)⟩
    rw [Nat.card_of_isEmpty, mul_zero]
  · simp

private def path_equiv_no_leaves (n : ℕ) : Structures n (Fin 0) ≃ Reduced n (Fin 0) :=
  Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨h, fun j => j.elim0⟩, And.left⟩

private theorem arith_reindex {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)) {d r : W → ℕ}
    (h : IsArithmeticalStructure H d r) : IsArithmeticalStructure G (d ∘ e) (r ∘ e) := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  refine ⟨fun v => h.1 _, fun v => h.2.1 _, fun v => ?_, fun g hg => ?_⟩
  · change d (e v) * r (e v) = _
    rw [h.2.2.1, sum_adj, sum_adj]
    simp_rw [he]
    exact (e.sum_comp (fun w => if H.Adj (e v) w then r w else 0)).symm
  · exact h.2.2.2 g (fun w => by simpa using hg (e.symm w))

private def appendEquiv (n : ℕ) : Vertex n (Fin 1) ≃ Vertex (n + 1) (Fin 0) :=
  finSumFinEquiv.trans (Equiv.sumEmpty (Fin (n + 2)) (Fin 0)).symm

private theorem append_inl (n : ℕ) (i : Fin (n + 1)) :
    appendEquiv n (.inl i) = .inl i.castSucc := by
  apply (Equiv.sumEmpty (Fin (n + 2)) (Fin 0)).injective
  simp [appendEquiv, finSumFinEquiv_apply_left]
  rfl

private theorem append_inr (n : ℕ) (i : Fin 1) :
    appendEquiv n (.inr i) = .inl (Fin.last (n + 1)) := by
  apply (Equiv.sumEmpty (Fin (n + 2)) (Fin 0)).injective
  simp [appendEquiv, finSumFinEquiv_apply_right, Fin.ext_iff, Fin.eq_zero i]

private theorem append_adj (n : ℕ) (v w : Vertex n (Fin 1)) :
    (coconutTree (n + 1) 1).Adj v w ↔
      (coconutTree (n + 1 + 1) 0).Adj (appendEquiv n v) (appendEquiv n w) := by
  rcases v with i | j <;> rcases w with i' | j'
  · simp [append_inl, coconutTree_adj_inl_inl]
  · simp [append_inl, append_inr, coconutTree_adj_inl_inl, coconutTree_adj_inl_inr]
    omega
  · rw [(coconutTree (n + 1) 1).adj_comm (.inr j) (.inl i'),
      (coconutTree (n + 1 + 1) 0).adj_comm (appendEquiv n (.inr j)) (appendEquiv n (.inl i'))]
    simp [append_inl, append_inr, coconutTree_adj_inl_inl, coconutTree_adj_inl_inr]
    omega
  · simp [append_inr, coconutTree_not_adj_inr_inr]

private def appendPath (n : ℕ) : Structures n (Fin 1) ≃ Structures (n + 1) (Fin 0) where
  toFun x := ⟨(x.val.1 ∘ (appendEquiv n).symm, x.val.2 ∘ (appendEquiv n).symm),
    (valid_iff (Or.inl (by omega)) _).mpr (arith_reindex (appendEquiv n).symm
      (fun v w => by
        simpa using (append_adj n ((appendEquiv n).symm v) ((appendEquiv n).symm w)).symm)
      ((valid_iff (Or.inr (by omega)) _).mp x.property))⟩
  invFun y := ⟨(y.val.1 ∘ appendEquiv n, y.val.2 ∘ appendEquiv n),
    (valid_iff (Or.inr (by omega)) _).mpr (arith_reindex (appendEquiv n) (append_adj n)
      ((valid_iff (Or.inl (by omega)) _).mp y.property))⟩
  left_inv x := Subtype.ext (Prod.ext (funext fun _ => by simp) (funext fun _ => by simp))
  right_inv y := Subtype.ext (Prod.ext (funext fun _ => by simp) (funext fun _ => by simp))

private theorem one_leaf_count (n : ℕ) :
    Nat.card (Reduced n (Fin 1)) = catalan (n + 1) - catalan n := by
  have hp := leaf_partition n 1 (finite_reduced n)
  rw [Nat.card_congr (appendPath n), Nat.card_congr (path_equiv_no_leaves (n + 1)),
    path_count] at hp
  rw [sum_range_succ, sum_range_one] at hp
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.sub_zero, one_mul] at hp
  change catalan (n + 1) = Nat.card (Reduced n (Fin 1)) + Nat.card (Reduced n (Fin 0)) at hp
  rw [path_count] at hp
  omega

private def smoothEquiv (n s : ℕ) (hs : 0 < s) : Stage n (Fin s) 0 ≃
    {x : Labels n (Fin s) // IsSmoothCoconut (n + 1) s x.1 x.2} :=
  Equiv.subtypeEquivRight fun x => by
    rw [IsSmoothCoconut]
    constructor
    · rintro ⟨hv, hl, hp⟩
      have h := (valid_iff (Or.inr hs) _).mp hv
      refine ⟨h, fun i hi => ?_, fun j => ?_⟩
      · have hne := hp i (Nat.zero_le _) (by omega)
        have hp' := h.1 (.inl i)
        omega
      · have hp' := h.1 (.inr j)
        have hj := hl j
        omega
    · rintro ⟨h, hp, hl⟩
      exact ⟨(valid_iff (Or.inr hs) _).mpr h, fun j => by have := hl j; omega,
        fun i _ hi => by have := hp i (by omega); omega⟩

private theorem reduced_count_term (n s : ℕ) :
    Nat.card (Reduced n (Fin s)) = coconutCountTerm (n + 1 + s) s := by
  rcases s with _ | s
  · simp [coconutCountTerm_zero, path_count]
  rcases s with _ | s
  · rw [one_leaf_count, coconutCountTerm, ite_eq_right (by decide), ite_eq_left rfl]
    congr 1
  let s' := s + 2
  change Nat.card (Reduced n (Fin s')) = coconutCountTerm (n + 1 + s') s'
  have hs : 0 < s' := by omega
  rw [coconutCountTerm, ite_eq_right (by omega), ite_eq_right (by omega), reduced_count]
  let N (k : ℕ) := Set.ncard {x : (Fin k ⊕ Fin s' → ℕ) × (Fin k ⊕ Fin s' → ℕ) |
    IsSmoothCoconut k s' x.1 x.2}
  change ∑ q ∈ range (n + 1), ballotNumber n (n - q) * Nat.card (Stage q (Fin s') 0) =
    ∑ i ∈ Icc (s' + 1) (n + 1 + s'),
      ballotNumber (n + 1 + s' - s' - 1) (n + 1 + s' - i) * N (i - s')
  have hN (q : ℕ) : Nat.card (Stage q (Fin s') 0) = N (q + 1) := by
    let T : Set (Labels q (Fin s')) := {x | IsSmoothCoconut (q + 1) s' x.1 x.2}
    let e : Stage q (Fin s') 0 ≃ T := smoothEquiv q s' hs
    exact (Nat.card_congr e).trans (Nat.card_coe_set_eq T)
  simp_rw [hN]
  refine Finset.sum_bij (fun q _ => q + 1 + s') ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_range] at hq
    rw [mem_Icc]
    omega
  · intro q hq q' hq' he
    change q + 1 + s' = q' + 1 + s' at he
    omega
  · intro i hi
    rw [mem_Icc] at hi
    refine ⟨i - s' - 1, mem_range.mpr (by omega), by omega⟩
  · intro q hq
    rw [mem_range] at hq
    rw [show n + 1 + s' - s' - 1 = n by omega, show n + 1 + s' - (q + 1 + s') = n - q by omega,
      show q + 1 + s' - s' = q + 1 by omega]

end ncard_arithmeticalStructure_coconutTree

open Finset ncard_arithmeticalStructure_coconutTree in
/-- **Number of arithmetical structures on coconut trees.** For $p \ge 1$ and $s \ge 2$, the number
of arithmetical structures on the coconut tree $CT(p, s)$ is
$$\sum_{j=0}^{s} \binom{s}{j} A(p + s - j, s - j),$$
where $A(x, y)$ is the coconut count term.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Theorem 1
(`integers-2025-A82-thm-1`). -/
public theorem ncard_arithmeticalStructure_coconutTree {p s : ℕ} (hp : 1 ≤ p)
    (hs : 2 ≤ s) :
    Set.ncard {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) |
      IsArithmeticalStructure (coconutTree p s) x.1 x.2}
      = ∑ j ∈ Finset.range (s + 1), s.choose j * coconutCountTerm (p + s - j) (s - j) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let A : Set (Labels n (Fin s)) := {x | IsArithmeticalStructure (coconutTree (n + 1) s) x.1 x.2}
  let e : A ≃ Structures n (Fin s) := Equiv.subtypeEquivRight fun x =>
    (valid_iff (Or.inr (show 0 < s by omega)) x).symm
  change A.ncard = _
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, leaf_partition n s (finite_reduced n)]
  refine sum_congr rfl fun j hj => ?_
  rw [reduced_count_term]
  rw [mem_range] at hj
  rw [show n + 1 + (s - j) = n + 1 + s - j by omega]

end MetaMathlibExt
