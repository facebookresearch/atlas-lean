/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleZeta.Series

/-!
# Reversing multiple-zeta summation conventions

Multiple-zeta values are commonly written using either strictly increasing
summation variables, with the final exponent at least two, or strictly
decreasing summation variables, with the first exponent at least two. This
module defines the increasing presentation and proves that reversing both the
exponent index and the summation tuple identifies it with `strictValue`.

## Main definitions

* `Index.reverse` reverses the exponent index.
* `Index.IsIncreasingAdmissible` expresses admissibility in the increasing convention.
* `StrictIncreasingTuple` is a strictly increasing tuple of positive naturals.
* `increasingSummand` and `increasingValue` give the increasing presentation.
* `increasingEquivDecreasing` reverses an increasing tuple.

## Main results

* `Index.isIncreasingAdmissible_iff_reverse_isAdmissible` transports admissibility.
* `increasingSummand_eq_strictSummand_reverse` identifies individual summands.
* `increasingValue_eq_strictValue_reverse` identifies the two series.

## References

* [K.-W. Chen et al., *Some Symmetry and Duality Theorems on Multiple
  Zeta(-star) Values*](https://arxiv.org/abs/2304.08722)
* [N. Tamang and P. Sarkar, *An algebraic proof of the duality of multiple
  zeta-star values of height one*](https://arxiv.org/abs/2307.09867)
* [Z. Li, Z. Wang, and L. Zhang, *A proof of a weighted sum conjecture for
  finite multiple zeta values of level two*](https://arxiv.org/abs/2608.10675)
* [H. Bachmann and Risan, *Formal finite multiple zeta
  values*](https://arxiv.org/abs/2608.15480)
-/

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

/-- **Reversed index.** The reverse of an index $(k_0, \dots, k_{d-1})$ is the index
$(k_{d-1}, \dots, k_0)$ with the same entries in the opposite order. -/
def Index.reverse (index : Index) : Index :=
  match index with
  | ⟨n, composition⟩ => ⟨n, composition.reverse⟩

@[simp]
theorem Index.reverse_entries (index : Index) :
    index.reverse.entries = index.entries.reverse := by
  rcases index with ⟨n, composition⟩
  simp [Index.entries, Index.reverse, Composition.reverse_blocks]

@[simp]
theorem Index.reverse_weight (index : Index) :
    index.reverse.weight = index.weight := by
  rcases index with ⟨n, composition⟩
  rfl

@[simp]
theorem Index.reverse_depth (index : Index) :
    index.reverse.depth = index.depth := by
  rcases index with ⟨n, composition⟩
  change composition.reverse.blocks.length = composition.blocks.length
  simp

@[simp]
theorem Index.reverse_reverse (index : Index) :
    index.reverse.reverse = index := by
  rcases index with ⟨n, composition⟩
  simp only [Index.reverse]
  rw [Composition.reverse_reverse]

/-- **Strictly increasing tuples.** For a natural number $d$, a strictly increasing tuple of
length $d$ is a tuple $(m_0, \dots, m_{d-1})$ of positive natural numbers with
$m_0 < m_1 < \cdots < m_{d-1}$. These are the summation variables of the increasing
multiple-zeta convention. -/
abbrev StrictIncreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // StrictMono m}

/-- **Admissibility in the increasing convention.** An index $(k_0, \dots, k_{d-1})$ is
admissible in the increasing convention when its list of entries read in reverse order,
$(k_{d-1}, \dots, k_0)$, is admissible: it is nonempty, its first element $k_{d-1}$ is at least
two, and its other elements are positive. Since the entries of an index are positive, this says
that the index is nonempty and its last entry is at least two.

This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
def Index.IsIncreasingAdmissible (index : Index) : Prop :=
  MetaMathlibExt.MultipleZeta.IsAdmissible index.entries.reverse

/-- **Increasing admissibility is admissibility of the reverse.** An index is admissible in the
increasing convention (nonempty with last entry at least two) if and only if its reverse is
admissible (nonempty with first entry at least two). -/
theorem Index.isIncreasingAdmissible_iff_reverse_isAdmissible (index : Index) :
    index.IsIncreasingAdmissible ↔ index.reverse.IsAdmissible := by
  rw [Index.isAdmissible_iff, Index.reverse_entries]
  rfl

private theorem composition_blocksFun_reverse {n : ℕ}
    (composition : Composition n)
    (i : Fin composition.reverse.blocks.length) :
    Composition.blocksFun composition.reverse i =
      Composition.blocksFun composition
        (Fin.rev (Fin.castOrderIso (by simp) i)) := by
  simp only [Composition.blocksFun, Composition.reverse_blocks,
    List.get_eq_getElem, List.getElem_reverse, Fin.val_rev, Nat.sub_sub]
  apply getElem_congr rfl
  change composition.blocks.length - (1 + i.val) =
    composition.blocks.length - (i.val + 1)
  omega

/-- **Entries of the reversed index.** Let $k = (k_0, \dots, k_{d-1})$ be an index of depth $d$;
its reverse also has depth $d$. For every $i < d$, the $i$-th entry of the reverse of $k$ is
$k_{d-1-i}$. -/
theorem Index.reverse_entry (index : Index)
    (i : Fin index.reverse.depth) :
    index.reverse.entry i =
      index.entry (Fin.rev (Fin.castOrderIso index.reverse_depth i)) := by
  rcases index with ⟨n, composition⟩
  apply PNat.eq
  exact composition_blocksFun_reverse composition i

/-- **Summand of the increasing multiple-zeta series.** Let $k = (k_0, \dots, k_{d-1})$ be an
index of depth $d$. To a strictly increasing tuple $m = (m_0, \dots, m_{d-1})$ of positive
natural numbers it attaches the real number
$$\Bigl(\prod_{i=0}^{d-1} m_i^{k_i}\Bigr)^{-1}.$$

This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
noncomputable def increasingSummand (index : Index)
    (m : StrictIncreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- **Multiple zeta value in the increasing convention.** Let $k = (k_0, \dots, k_{d-1})$ be an
index of depth $d$ that is admissible in the increasing convention. Its value in the increasing
convention is the real number
$$\sum_{0 < m_0 < \cdots < m_{d-1}} \prod_{i=0}^{d-1} m_i^{-k_i},$$
the unconditional sum over all strictly increasing tuples of positive natural numbers (taken to
be $0$ if the family is not summable).

This is the convention in arXiv:2304.08722 and arXiv:2608.10675. -/
@[nolint unusedArguments]
noncomputable def increasingValue (index : Index)
    (_h : index.IsIncreasingAdmissible) : ℝ :=
  ∑' m : StrictIncreasingTuple index.depth, increasingSummand index m

/-- **Reversal of strictly increasing tuples.** Let $k$ be an index of depth $d$; its reverse
also has depth $d$. Sending a strictly increasing tuple $(m_0, \dots, m_{d-1})$ of positive
natural numbers to the reversed tuple $(m_{d-1}, \dots, m_0)$ is a bijection from the strictly
increasing tuples of length $d$ onto the strictly decreasing tuples of length $d$, whose inverse
again reverses the order of the coordinates. -/
def increasingEquivDecreasing (index : Index) :
    StrictIncreasingTuple index.depth ≃
      StrictDecreasingTuple index.reverse.depth where
  toFun m :=
    ⟨fun i => m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth i <
            Fin.castOrderIso index.reverse_depth j := by
        simpa using hij
      exact m.2 (Fin.rev_lt_rev.mpr hcast)⟩
  invFun m :=
    ⟨fun i => m.1 (Fin.castOrderIso index.reverse_depth.symm (Fin.rev i)), by
      intro i j hij
      have hcast :
          Fin.castOrderIso index.reverse_depth.symm (Fin.rev j) <
            Fin.castOrderIso index.reverse_depth.symm (Fin.rev i) := by
        simpa using Fin.rev_lt_rev.mpr hij
      exact m.2 hcast⟩
  left_inv m := by
    ext i
    simp
  right_inv m := by
    ext i
    simp

@[simp]
theorem increasingEquivDecreasing_apply (index : Index)
    (m : StrictIncreasingTuple index.depth)
    (i : Fin index.reverse.depth) :
    (increasingEquivDecreasing index m).1 i =
      m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)) :=
  rfl

/-- **Reversal preserves each summand.** Let $k = (k_0, \dots, k_{d-1})$ be an index of depth
$d$ and let $m = (m_0, \dots, m_{d-1})$ be a strictly increasing tuple of positive natural
numbers. Then the summand of the increasing multiple-zeta series of $k$ at $m$ equals the
summand of the strict multiple-zeta series of the reversed index $(k_{d-1}, \dots, k_0)$ at the
strictly decreasing tuple $(m_{d-1}, \dots, m_0)$. -/
theorem increasingSummand_eq_strictSummand_reverse (index : Index)
    (m : StrictIncreasingTuple index.depth) :
    increasingSummand index m =
      strictSummand index.reverse (increasingEquivDecreasing index m) := by
  unfold increasingSummand strictSummand
  let e : Fin index.reverse.depth ≃ Fin index.depth :=
    (Fin.castOrderIso index.reverse_depth).toEquiv.trans Fin.revPerm
  have hprod :
      (∏ i : Fin index.depth, ((m.1 i : ℝ) ^ (index.entry i : ℕ))) =
        ∏ j : Fin index.reverse.depth,
          ((m.1 (e j) : ℝ) ^ (index.reverse.entry j : ℕ)) := by
    symm
    apply Fintype.prod_equiv e
    intro j
    simp [e, Index.reverse_entry]
  rw [hprod]
  rfl

/-- **Increasing values agree with strict values of the reverse.** Let
$k = (k_0, \dots, k_{d-1})$ be an index of depth $d$ that is admissible in the increasing
convention, so that its reverse $(k_{d-1}, \dots, k_0)$ is admissible. Then the value of $k$ in
the increasing convention equals the strict multiple zeta value of the reverse of $k$:
$$\sum_{0 < m_0 < \cdots < m_{d-1}} \prod_{i=0}^{d-1} m_i^{-k_i}
= \sum_{n_0 > \cdots > n_{d-1} > 0} \prod_{i=0}^{d-1} n_i^{-k_{d-1-i}},$$
where both sides are unconditional sums of real numbers (taken to be $0$ for a non-summable
family). -/
theorem increasingValue_eq_strictValue_reverse (index : Index)
    (h : index.IsIncreasingAdmissible) :
    increasingValue index h =
      strictValue index.reverse
        (Or.inl (index.isIncreasingAdmissible_iff_reverse_isAdmissible.mp h)) := by
  unfold increasingValue strictValue
  rw [show (fun m : StrictIncreasingTuple index.depth =>
      increasingSummand index m) =
      fun m => strictSummand index.reverse
        (increasingEquivDecreasing index m) by
    funext m
    exact increasingSummand_eq_strictSummand_reverse index m]
  exact Equiv.tsum_eq (increasingEquivDecreasing index)
    (strictSummand index.reverse)

end MetaMathlibExt.MultipleZeta
