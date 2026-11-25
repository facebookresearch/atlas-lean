/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import MathlibExt.NumberTheory.MultipleZeta.Index

/-!
# Multiple-zeta and multiple-zeta-star series

This file defines multiple-zeta summands and values using strictly decreasing positive summation
variables, and multiple-zeta-star summands and values using weakly decreasing positive summation
variables. The star convention follows arXiv:2307.09867 and arXiv:2309.07569.
-/

@[expose] public section

namespace MetaMathlibExt.MultipleZeta

/-- **Empty multiple-zeta index.** The empty multiple-zeta index, which has no entries and weight
zero.

Source: arXiv:2307.09867, empty-index convention. -/
def Index.empty : Index :=
  ⟨0, ⟨[], by simp, by simp⟩⟩

@[simp]
theorem Index.empty_entries : Index.empty.entries = [] :=
  rfl

@[simp]
theorem Index.empty_weight : Index.empty.weight = 0 :=
  rfl

@[simp]
theorem Index.empty_depth : Index.empty.depth = 0 :=
  rfl

/-- **Entry of a multiple-zeta index.** For a multiple-zeta index $k = (k_0, \dots, k_{d-1})$ of
depth $d$ and $0 \le i < d$, the entry of $k$ at $i$ is the positive natural number $k_i$. -/
def Index.entry : (index : Index) → Fin index.depth → PNat
  | ⟨_, composition⟩ => fun i =>
    ⟨composition.blocksFun i, composition.blocks_pos (composition.blocksFun_mem_blocks i)⟩

@[simp]
theorem Index.entry_coe (index : Index) (i : Fin index.depth) :
    (index.entry i : ℕ) = index.2.blocksFun i :=
  rfl

/-- **Strictly decreasing tuples.** For a natural number $r$, a strictly decreasing $r$-tuple is a
tuple $(m_0, \dots, m_{r-1})$ of positive integers with $m_0 > m_1 > \dots > m_{r-1}$.

Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
abbrev StrictDecreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // StrictAnti m}

/-- **Empty strictly decreasing tuple.** The unique strictly decreasing tuple of positive natural
numbers of length zero, namely the empty tuple. -/
def StrictDecreasingTuple.empty : StrictDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem StrictDecreasingTuple.eq_empty (m : StrictDecreasingTuple 0) :
    m = StrictDecreasingTuple.empty := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- **Multiple zeta summand.** Let $\mathbf{k} = (k_0, \dots, k_{r-1})$ be an index of depth $r$
and let $(m_0, \dots, m_{r-1})$ be a strictly decreasing $r$-tuple of positive integers. The
summand attached to $\mathbf{k}$ and this tuple is the real number
$\left(\prod_{i=0}^{r-1} m_i^{k_i}\right)^{-1}$.

Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
noncomputable def strictSummand (index : Index)
    (m : StrictDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

@[simp]
theorem strictSummand_empty (m : StrictDecreasingTuple Index.empty.depth) :
    strictSummand Index.empty m = 1 := by
  unfold strictSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

/-- **Admissible or empty index.** A multiple-zeta index is admissible or empty when it is
admissible (nonempty with first entry at least two) or has depth zero, that is, has no entries.

The strict multiple-zeta value and the multiple-zeta-star value are defined on these indices. -/
def Index.IsAdmissibleOrEmpty (index : Index) : Prop :=
  index.IsAdmissible ∨ index.depth = 0

/-- **Multiple zeta value.** Let $\mathbf{k} = (k_0, \dots, k_{r-1})$ be an index of depth $r$
that is admissible ($r \ge 1$ and $k_0 \ge 2$) or empty. Its multiple zeta value is the real
number
$$\zeta(\mathbf{k}) = \sum_{m_0 > m_1 > \dots > m_{r-1} \ge 1} \prod_{i=0}^{r-1} m_i^{-k_i}$$
where the sum runs over all strictly decreasing $r$-tuples $(m_0, \dots, m_{r-1})$ of positive
integers. The sum is unconditional, with value $0$ by convention when the family is not
summable.

Source: arXiv:2307.09867, lines 60–63, and arXiv:2309.07569, lines 76–80. -/
@[nolint unusedArguments]
noncomputable def strictValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : StrictDecreasingTuple index.depth, strictSummand index m

@[simp]
theorem strictValue_empty (h : Index.empty.IsAdmissibleOrEmpty) :
    strictValue Index.empty h = 1 := by
  let m : StrictDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using StrictDecreasingTuple.empty
  unfold strictValue
  rw [tsum_eq_single m]
  · exact strictSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

/-- **Weakly decreasing tuples.** For a natural number $r$, a weakly decreasing $r$-tuple is a
tuple $(m_0, \dots, m_{r-1})$ of positive integers with $m_0 \ge m_1 \ge \dots \ge m_{r-1}$.

Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
abbrev WeaklyDecreasingTuple (depth : ℕ) :=
  {m : Fin depth → PNat // Antitone m}

/-- **Empty weakly decreasing tuple.** The unique weakly decreasing tuple of positive natural
numbers of length zero, namely the empty tuple. -/
def WeaklyDecreasingTuple.empty : WeaklyDecreasingTuple 0 :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem WeaklyDecreasingTuple.eq_empty (m : WeaklyDecreasingTuple 0) :
    m = WeaklyDecreasingTuple.empty := by
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

/-- **Strictly decreasing tuples as weakly decreasing tuples.** For a natural number $r$, every
strictly decreasing $r$-tuple $(m_0, \dots, m_{r-1})$ of positive integers is weakly decreasing;
this map sends it to the same tuple, regarded as a weakly decreasing $r$-tuple. -/
def StrictDecreasingTuple.toWeaklyDecreasing {depth : ℕ}
    (m : StrictDecreasingTuple depth) : WeaklyDecreasingTuple depth :=
  ⟨m.1, m.2.antitone⟩

/-- **Multiple-zeta-star summand.** For a multiple-zeta index $k = (k_0, \dots, k_{d-1})$ of
depth $d$ and a weakly decreasing tuple $m = (m_0, \dots, m_{d-1})$ of positive natural numbers,
the star summand of $k$ at $m$ is the real number $\left(\prod_{i<d} m_i^{k_i}\right)^{-1}$.

Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
noncomputable def starSummand (index : Index)
    (m : WeaklyDecreasingTuple index.depth) : ℝ :=
  (∏ i : Fin index.depth, ((m.1 i : ℕ) : ℝ) ^ (index.entry i : ℕ))⁻¹

/-- **Star and strict summands agree on strictly decreasing tuples.** For a multiple-zeta index
$k$ of depth $d$ and a strictly decreasing tuple $m$ of $d$ positive natural numbers, the star
summand of $k$ at $m$, with $m$ regarded as a weakly decreasing tuple, equals the strict summand
of $k$ at $m$. -/
@[simp]
theorem starSummand_toWeaklyDecreasing
    (index : Index) (m : StrictDecreasingTuple index.depth) :
    starSummand index m.toWeaklyDecreasing = strictSummand index m :=
  rfl

@[simp]
theorem starSummand_empty (m : WeaklyDecreasingTuple Index.empty.depth) :
    starSummand Index.empty m = 1 := by
  unfold starSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

/-- **Multiple zeta-star value.** Let $\mathbf{k} = (k_0, \dots, k_{r-1})$ be an index of depth
$r$ that is admissible ($r \ge 1$ and $k_0 \ge 2$) or empty. Its multiple zeta-star value is the
real number
$$\zeta^\star(\mathbf{k}) = \sum_{m_0 \ge \dots \ge m_{r-1} \ge 1} \prod_{i=0}^{r-1} m_i^{-k_i}$$
where the sum runs over all weakly decreasing $r$-tuples $(m_0, \dots, m_{r-1})$ of positive
integers. The sum is unconditional, with value $0$ by convention when the family is not
summable.

Source: arXiv:2307.09867, lines 61–65, and arXiv:2309.07569v2, lines 84–87. -/
@[nolint unusedArguments]
noncomputable def starValue (index : Index) (_h : index.IsAdmissibleOrEmpty) : ℝ :=
  ∑' m : WeaklyDecreasingTuple index.depth, starSummand index m

/-- **Multiple-zeta-star value of the empty index.** The multiple-zeta-star value of the empty
index is $1$.

Source: arXiv:2307.09867, lines 166–167. -/
@[simp]
theorem starValue_empty (h : Index.empty.IsAdmissibleOrEmpty) :
    starValue Index.empty h = 1 := by
  let m : WeaklyDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using WeaklyDecreasingTuple.empty
  unfold starValue
  rw [tsum_eq_single m]
  · exact starSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

/-- **Repeated index.** For a natural number $k$ and a positive natural number $e$, the index
$\{e\}^k = (e, \dots, e)$ consisting of $k$ entries all equal to $e$, so of weight $ke$.

For $e = 2$ its multiple-zeta-star value is $\zeta^\star(\{2\}^k)$.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Section 1 (notation `ζ*({2}^k)` and `ζ({2}^k)`). -/
def Index.replicate (k : ℕ) (e : PNat) : Index :=
  ⟨k * e, ⟨List.replicate k (e : ℕ), fun h => by
      rw [List.eq_of_mem_replicate h]
      exact e.pos, by simp⟩⟩

@[simp]
theorem Index.replicate_entries (k : ℕ) (e : PNat) :
    (Index.replicate k e).entries = List.replicate k (e : ℕ) :=
  rfl

@[simp]
theorem Index.replicate_weight (k : ℕ) (e : PNat) :
    (Index.replicate k e).weight = k * e :=
  rfl

@[simp]
theorem Index.replicate_depth (k : ℕ) (e : PNat) : (Index.replicate k e).depth = k := by
  simp [Index.replicate, Index.depth, Composition.length]

@[simp]
theorem Index.replicate_entry (k : ℕ) (e : PNat) (i : Fin (Index.replicate k e).depth) :
    (Index.replicate k e).entry i = e := by
  apply PNat.eq
  simp only [Index.entry, Index.replicate, Composition.blocksFun, PNat.mk_coe]
  exact List.eq_of_mem_replicate (List.get_mem _ _)

/-- **Repeated indices with entry at least two are admissible or empty.** For every natural
number $k$ and every positive natural number $e \ge 2$, the index $\{e\}^k$ consisting of $k$
entries all equal to $e$ is admissible or empty.

Source: Iovleff, INTEGERS 26 (2026), Article A114,
Section 1 (`ζ*({2}^k)`). -/
theorem Index.replicate_isAdmissibleOrEmpty (k : ℕ) {e : PNat} (he : 2 ≤ (e : ℕ)) :
    (Index.replicate k e).IsAdmissibleOrEmpty := by
  cases k with
  | zero => exact Or.inr (Index.replicate_depth 0 e)
  | succ k =>
      left
      simpa [Index.replicate, Index.IsAdmissible, List.replicate_succ] using he

end MetaMathlibExt.MultipleZeta
