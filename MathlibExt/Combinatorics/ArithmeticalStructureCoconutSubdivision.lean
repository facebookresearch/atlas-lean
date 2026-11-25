/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree

/-!
# Subdivision of arithmetical structures on coconut trees

Inserting a path vertex by coconut subdivision preserves arithmetical structures.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Subdivision at a path vertex of a coconut tree.** Let the coconut tree $CT(p, s)$ have path
vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$, let $d$ and $r$ be labelings of
its vertices by natural numbers, and let $1 \le k \le p$. Subdividing $(d, r)$ at position $k$
gives the labelings $(d', r')$ of $CT(p + 1, s)$ obtained by inserting a new path vertex $w$
just before $v_k$, so that the path becomes $v_1, \dots, v_{k-1}, w, v_k, \dots, v_p$, with
$d'(w) = 1$ and $r'(w) = r(v_{k-1}) + r(v_k)$, where $r(v_0) = 0$ (so $r'(w) = r(v_1)$ when
$k = 1$). The path neighbours of $w$, namely $v_{k-1}$ (when $k \ge 2$) and $v_k$, get
$d' = d + 1$; every other vertex keeps its value of $d$, and every vertex other than $w$ keeps
its value of $r$.

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

/-- **Example of subdividing a coconut tree.** List a labeling of a coconut tree as its values on
the path vertices $v_1, v_2, \dots$, then $\mid$, then its values on the leaves. Subdividing the
labelings $d = (2, 2, 2, 2 \mid 2, 2, 4)$ and $r = (1, 2, 3, 4 \mid 2, 2, 1)$ of $CT(4, 3)$ at
position $2$ gives the labelings $d' = (3, 1, 3, 2, 2 \mid 2, 2, 4)$ and
$r' = (1, 3, 2, 3, 4 \mid 2, 2, 1)$ of $CT(5, 3)$. These are the labelings of Example 3.2, whose
smoothing at $v_2$ is $(d, r)$, so here subdivision undoes that smoothing.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9 and
Example 3.2 (arXiv numbering). -/
public theorem coconutSubdivide_example :
    coconutSubdivide (p := 4) (s := 3) 1
        (Sum.elim ![2, 2, 2, 2] ![2, 2, 4], Sum.elim ![1, 2, 3, 4] ![2, 2, 1]) =
      (Sum.elim ![3, 1, 3, 2, 2] ![2, 2, 4], Sum.elim ![1, 3, 2, 3, 4] ![2, 2, 1]) := by
  decide

end

namespace IsArithmeticalStructure.coconutSubdivide

open scoped BigOperators

-- The path occupies levels 1 through p, with all the leaves at level p + 1.
private def level (p s k : ℕ) : Set (Fin p ⊕ Fin s) :=
  {v | Sum.elim (fun j : Fin p => j.val + 1) (fun _ : Fin s => p + 1) v = k}

private noncomputable def levelSum {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) (k : ℕ) : ℕ :=
  ∑ᶠ w ∈ level p s k, r w

private theorem levelSum_zero {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) :
    levelSum r 0 = 0 := by
  have h : level p s 0 = ∅ := by
    ext (j | j) <;> simp [level]
  rw [levelSum, h, finsum_mem_empty]

private theorem levelSum_path {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) (j : Fin p) :
    levelSum r (j.val + 1) = r (.inl j) := by
  have h : level p s (j.val + 1) = {Sum.inl j} := by
    ext (k | k)
    · simp [level, Fin.ext_iff]
    · simp [level, Nat.ne_of_gt j.isLt]
  rw [levelSum, h, finsum_mem_singleton]

private theorem levelSum_leaves {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) :
    levelSum r (p + 1) = ∑ l, r (.inr l) := by
  have h : level p s (p + 1) = Set.range Sum.inr := by
    ext (j | j)
    · simp [level, Nat.ne_of_lt j.isLt]
    · simp [level]
  rw [levelSum, h, finsum_mem_range Sum.inr_injective, finsum_eq_sum_of_fintype]

private theorem path_neighborSum {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) (j : Fin p) :
    (∑ᶠ w ∈ {w | (coconutTree p s).Adj (.inl j) w}, r w) =
      levelSum r j.val + levelSum r (j.val + 2) := by
  have h : {w | (coconutTree p s).Adj (.inl j) w} =
      level p s j.val ∪ level p s (j.val + 2) := by
    ext (k | k)
    · simp [level, coconutTree_adj_inl_inl]
      omega
    · simp [level, coconutTree_adj_inl_inr]
      omega
  have hdisj : Disjoint (level p s j.val) (level p s (j.val + 2)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    simp only [level, Set.mem_ofPred_eq] at hw hw'
    omega
  rw [h, levelSum, levelSum]
  exact finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)

private theorem leaf_neighborSum {p s : ℕ} (r : Fin (p + 1) ⊕ Fin s → ℕ) (l : Fin s) :
    (∑ᶠ w ∈ {w | (coconutTree (p + 1) s).Adj (.inr l) w}, r w) =
      r (.inl (Fin.last p)) := by
  have h : {w | (coconutTree (p + 1) s).Adj (.inr l) w} = {Sum.inl (Fin.last p)} := by
    ext (j | j)
    · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
      simp [Fin.ext_iff]
    · simp [coconutTree_not_adj_inr_inr]
  rw [h, finsum_mem_singleton]

variable {p s : ℕ} {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)} {i : Fin p}

private theorem r_left (j : Fin p) (hj : j.val < i.val) :
    (MetaMathlibExt.coconutSubdivide i x).2 (.inl j.castSucc) = x.2 (.inl j) := by
  simp [MetaMathlibExt.coconutSubdivide, hj, j.isLt]

private theorem r_right (j : Fin p) (hj : i.val ≤ j.val) :
    (MetaMathlibExt.coconutSubdivide i x).2 (.inl j.succ) = x.2 (.inl j) := by
  simp [MetaMathlibExt.coconutSubdivide, show ¬j.val + 1 < i.val by omega,
    show j.val + 1 ≠ i.val by omega, j.isLt]

private theorem d_left (j : Fin p) (hj : j.val < i.val) :
    (MetaMathlibExt.coconutSubdivide i x).1 (.inl j.castSucc) =
      x.1 (.inl j) + if j.val + 1 = i.val then 1 else 0 := by
  by_cases h : j.val + 1 = i.val
  · simp [MetaMathlibExt.coconutSubdivide, h, j.isLt]
  · simp [MetaMathlibExt.coconutSubdivide, h, show j.val + 1 < i.val by omega, j.isLt]

private theorem d_right (j : Fin p) (hj : i.val ≤ j.val) :
    (MetaMathlibExt.coconutSubdivide i x).1 (.inl j.succ) =
      x.1 (.inl j) + if j.val = i.val then 1 else 0 := by
  simp [MetaMathlibExt.coconutSubdivide, show ¬j.val + 1 + 1 < i.val by omega,
    show j.val + 1 + 1 ≠ i.val by omega, show j.val + 1 ≠ i.val by omega, j.isLt]
  split_ifs <;> simp

private theorem d_insert :
    (MetaMathlibExt.coconutSubdivide i x).1 (.inl i.castSucc) = 1 := by
  simp [MetaMathlibExt.coconutSubdivide]

private theorem levels_left {k : ℕ} (hk : k ≤ i.val) :
    levelSum (MetaMathlibExt.coconutSubdivide i x).2 k = levelSum x.2 k := by
  by_cases h : k = 0
  · simp [h, levelSum_zero]
  let j : Fin p := ⟨k - 1, by omega⟩
  have hj : j.val + 1 = k := by dsimp [j]; omega
  rw [← hj, ← Fin.val_castSucc (i := j), levelSum_path, Fin.val_castSucc, levelSum_path]
  exact r_left j (show k - 1 < i.val by omega)

private theorem levels_right {k : ℕ} (hk : i.val + 1 < k) (hk' : k ≤ p + 2) :
    levelSum (MetaMathlibExt.coconutSubdivide i x).2 k = levelSum x.2 (k - 1) := by
  by_cases h : k = p + 2
  · rw [h, show p + 2 - 1 = p + 1 by omega, levelSum_leaves, levelSum_leaves]
    rfl
  let j : Fin p := ⟨k - 2, by omega⟩
  have hj : j.val + 1 = k - 1 := by dsimp [j]; omega
  have hj' : j.succ.val + 1 = k := by simp [j]; omega
  calc
    _ = (MetaMathlibExt.coconutSubdivide i x).2 (.inl j.succ) := hj' ▸ levelSum_path _ _
    _ = x.2 (.inl j) := r_right j (show i.val ≤ k - 2 by omega)
    _ = _ := hj ▸ (levelSum_path _ j).symm

private theorem levels_insert :
    levelSum (MetaMathlibExt.coconutSubdivide i x).2 (i.val + 1) =
      levelSum x.2 i.val + levelSum x.2 (i.val + 1) := by
  rw [← Fin.val_castSucc (i := i), levelSum_path, Fin.val_castSucc, levelSum_path]
  simp only [MetaMathlibExt.coconutSubdivide, Sum.elim_inl, Fin.val_castSucc,
    lt_self_iff_false, i.isLt, dite_true, ite_true, ite_false]
  congr 1
  by_cases h : i.val = 0
  · simp [h, levelSum_zero]
  · let j : Fin p := ⟨i.val - 1, by omega⟩
    have hj : j.val + 1 = i.val := by dsimp [j]; omega
    simp only [h, ite_false, dite_eq_left (show i.val - 1 < p by omega)]
    calc
      _ = x.2 (.inl j) := rfl
      _ = levelSum x.2 (j.val + 1) := (levelSum_path x.2 j).symm
      _ = _ := congrArg (levelSum x.2) hj

end IsArithmeticalStructure.coconutSubdivide

open IsArithmeticalStructure.coconutSubdivide in
/-- **Subdivision preserves arithmetical structures on coconut trees.** If $(d, r)$ is an
arithmetical structure on the coconut tree $CT(p, s)$, whose path vertices are $v_1, \dots, v_p$,
then for every $1 \le k \le p$, subdividing $(d, r)$ at position $k$ (inserting a new path vertex
just before $v_k$) gives an arithmetical structure on $CT(p + 1, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.11
(`integers-2025-A82-prop-3`). -/
public theorem IsArithmeticalStructure.coconutSubdivide {p s : ℕ}
    {x : (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p s) x.1 x.2) (i : Fin p) :
    IsArithmeticalStructure (coconutTree (p + 1) s) (coconutSubdivide i x).1
      (coconutSubdivide i x).2 := by
  let y := MetaMathlibExt.coconutSubdivide i x
  have hpath_eq (j : Fin p) :
      x.1 (.inl j) * x.2 (.inl j) = levelSum x.2 j.val + levelSum x.2 (j.val + 2) :=
    (hx.2.2.1 (.inl j)).trans (path_neighborSum x.2 j)
  have hpath (j : Fin (p + 1)) :
      (0 < y.1 (.inl j)) ∧ (0 < y.2 (.inl j)) ∧
        y.1 (.inl j) * y.2 (.inl j) = levelSum y.2 j.val + levelSum y.2 (j.val + 2) := by
    refine Fin.succAboveCases i.castSucc ?_ ?_ j
    · -- The inserted vertex has label 1 and its second label is the sum of its neighbours.
      have hr : y.2 (.inl i.castSucc) = levelSum x.2 i.val + levelSum x.2 (i.val + 1) :=
        (levelSum_path y.2 i.castSucc).symm.trans levels_insert
      rw [show y.1 (.inl i.castSucc) = 1 from d_insert, hr, one_mul, Fin.val_castSucc,
        levels_left le_rfl, levels_right (by omega) (by omega : i.val + 2 ≤ p + 2),
        show i.val + 2 - 1 = i.val + 1 by omega, levelSum_path]
      exact ⟨one_pos, Nat.add_pos_right _ (hx.2.1 _), rfl⟩
    · intro k
      by_cases hk : k < i
      · -- A vertex to the left keeps its index.
        rw [Fin.succAbove_castSucc_of_lt _ _ hk, d_left k hk, r_left k hk, Fin.val_castSucc,
          levels_left (Nat.le_of_lt hk)]
        refine ⟨Nat.add_pos_left (hx.1 _) _, hx.2.1 _, ?_⟩
        by_cases h : k.val + 1 = i.val
        · rw [ite_eq_left h, Nat.add_mul, one_mul, hpath_eq,
            show k.val + 2 = i.val + 1 by omega, levels_insert, ← h, levelSum_path]
          omega
        · rw [ite_eq_right h, Nat.add_zero, hpath_eq, levels_left (by omega)]
      · -- A vertex to the right shifts by one.
        have hk' : i ≤ k := le_of_not_gt hk
        rw [Fin.succAbove_castSucc_of_le _ _ hk', d_right k hk', r_right k hk', Fin.val_succ,
          levels_right (by omega : i.val + 1 < k.val + 1 + 2) (by omega),
          show k.val + 1 + 2 - 1 = k.val + 2 by omega]
        refine ⟨Nat.add_pos_left (hx.1 _) _, hx.2.1 _, ?_⟩
        by_cases h : k.val = i.val
        · rw [ite_eq_left h, Nat.add_mul, one_mul, hpath_eq,
            show k.val + 1 = i.val + 1 by omega, levels_insert, ← h, levelSum_path]
          omega
        · rw [ite_eq_right h, Nat.add_zero, hpath_eq, levels_right (by omega) (by omega),
            Nat.add_sub_cancel]
  have hleaf (l : Fin s) :
      y.1 (.inr l) * y.2 (.inr l) = ∑ᶠ w ∈ {w | (coconutTree (p + 1) s).Adj (.inr l) w},
        y.2 w := by
    cases p with
    | zero => exact i.elim0
    | succ q =>
      rw [leaf_neighborSum, ← Fin.succ_last,
        r_right (Fin.last q) (Nat.le_of_lt_succ i.isLt)]
      exact (hx.2.2.1 (.inr l)).trans (leaf_neighborSum x.2 l)
  change IsArithmeticalStructure (coconutTree (p + 1) s) y.1 y.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (j | l)
    · exact (hpath j).1
    · exact hx.1 (.inr l)
  · rintro (j | l)
    · exact (hpath j).2.1
    · exact hx.2.1 (.inr l)
  · rintro (j | l)
    · exact (hpath j).2.2.trans (path_neighborSum y.2 j).symm
    · exact hleaf l
  · -- Every original second label still occurs after subdivision.
    intro g hg
    apply hx.2.2.2 g
    rintro (j | l)
    · by_cases hj : j.val < i.val
      · exact r_left j hj ▸ hg (.inl j.castSucc)
      · exact r_right j (Nat.le_of_not_gt hj) ▸ hg (.inl j.succ)
    · exact hg (.inr l)

end MetaMathlibExt
