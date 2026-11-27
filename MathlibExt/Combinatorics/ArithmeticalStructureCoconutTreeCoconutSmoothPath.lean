/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.SuccPred
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree

/-!
# Path smoothing on coconut trees

Smoothing at a path vertex deletes the vertex and lowers `d` at its path neighbours.
The main result is that smoothing at a non-central path vertex with `d`-label `1`
preserves arithmetical structures.

Statements from Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith,
*Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82
(preprint arXiv:2406.11183, whose text supplies the definitions).

The coconut tree `CT(p, s)` has vertex type `Fin p ⊕ Fin s`: the path vertex
`v_{i+1}` is `.inl i` and the leaf `v_{ℓ_{j+1}}` is `.inr j`; the central vertex
`v_p` is `.inl ⟨p - 1, _⟩`. A structure `(d, r)` is a pair of labelings of the
vertices. Counts `|Arith(G)|` and `|SArith(G)|` are `Set.ncard` of the sets of
pairs `(d, r)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Smoothing at a path vertex of a coconut tree.** Let the coconut tree $CT(p + 1, s)$ have
path vertices $v_1, \dots, v_{p+1}$, central vertex $v_{p+1}$ and leaves $\ell_1, \dots, \ell_s$,
let $d$ and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le p + 1$.
Smoothing $(d, r)$ at $v_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$v_k$ and renumbering the remaining path vertices $v_1, \dots, v_{k-1}, v_{k+1}, \dots, v_{p+1}$
in order as $v_1, \dots, v_p$. Every remaining vertex keeps its value of $r$ and its value of $d$,
except that $d$ drops by $1$ (truncated at $0$) at the path neighbours $v_{k-1}$ and $v_{k+1}$
of $v_k$, where they exist.

The paper applies it only at a non-central vertex ($k \le p$) with $d(v_k) = 1$: for $k \ge 2$
this is the degree-2 smoothing of Definition 3.1 and for $k = 1$ the smoothing at $v_1$ of
Definition 3.4.

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

end

namespace IsArithmeticalStructure.coconutSmoothPath

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

private theorem leaf_neighborSum {p s : ℕ} (hp : 0 < p) (r : Fin p ⊕ Fin s → ℕ)
    (l : Fin s) :
    (∑ᶠ w ∈ {w | (coconutTree p s).Adj (.inr l) w}, r w) =
      r (.inl ⟨p - 1, by omega⟩) := by
  have h : {w | (coconutTree p s).Adj (.inr l) w} = {Sum.inl ⟨p - 1, by omega⟩} := by
    ext (j | j)
    · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
      simp only [Set.mem_singleton_iff, Sum.inl.injEq, Fin.ext_iff]
      omega
    · simp [coconutTree_not_adj_inr_inr]
  rw [h, finsum_mem_singleton]

private theorem succAbove_val_lt {p : ℕ} {i : Fin (p + 1)} {j : Fin p}
    (h : j.val < i.val) : (i.succAbove j).val = j.val := by
  have hlt : j.castSucc < i := by simpa [Fin.lt_def, Fin.val_castSucc] using h
  rw [Fin.succAbove_of_castSucc_lt _ _ hlt, Fin.val_castSucc]

private theorem succAbove_val_le {p : ℕ} {i : Fin (p + 1)} {j : Fin p}
    (h : i.val ≤ j.val) : (i.succAbove j).val = j.val + 1 := by
  have hle : i ≤ j.castSucc := by simpa [Fin.le_def, Fin.val_castSucc] using h
  rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.val_succ]

private theorem r_smooth_path {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {j : Fin p} :
    (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) = x.2 (.inl (i.succAbove j)) := rfl

private theorem r_smooth_leaf {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {l : Fin s} :
    (MetaMathlibExt.coconutSmoothPath i x).2 (.inr l) = x.2 (.inr l) := rfl

private theorem d_smooth_leaf {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {l : Fin s} :
    (MetaMathlibExt.coconutSmoothPath i x).1 (.inr l) = x.1 (.inr l) := rfl

private theorem d_smooth_path_adj {p s : ℕ}
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {j : Fin p} (h : j.val + 1 = i.val ∨ j.val = i.val) :
    (MetaMathlibExt.coconutSmoothPath i x).1 (.inl j) = x.1 (.inl (i.succAbove j)) - 1 := by
  simp [MetaMathlibExt.coconutSmoothPath, h]

private theorem d_smooth_path_not {p s : ℕ}
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {j : Fin p} (h : ¬(j.val + 1 = i.val ∨ j.val = i.val)) :
    (MetaMathlibExt.coconutSmoothPath i x).1 (.inl j) = x.1 (.inl (i.succAbove j)) := by
  simp [MetaMathlibExt.coconutSmoothPath, h]

private theorem levels_left {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} (hi : i.val < p) {k : ℕ} (hk : k ≤ i.val) :
    levelSum (MetaMathlibExt.coconutSmoothPath i x).2 k = levelSum x.2 k := by
  by_cases hz : k = 0
  · simp [hz, levelSum_zero]
  · have hkp : k - 1 < p := by omega
    have hkp1 : k - 1 < p + 1 := by omega
    let j : Fin p := ⟨k - 1, hkp⟩
    let jold : Fin (p + 1) := ⟨k - 1, hkp1⟩
    have hj : j.val + 1 = k := by simp [j]; omega
    have hjold : jold.val + 1 = k := by simp [jold]; omega
    have hlt : j.val < i.val := by simp [j]; omega
    have hsucc : i.succAbove j = jold := by
      apply Fin.ext
      rw [succAbove_val_lt hlt]
    calc levelSum (MetaMathlibExt.coconutSmoothPath i x).2 k
        = (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) := hj ▸ levelSum_path _ _
      _ = x.2 (.inl (i.succAbove j)) := r_smooth_path
      _ = x.2 (.inl jold) := by rw [hsucc]
      _ = levelSum x.2 k := (hjold ▸ (levelSum_path _ _).symm)

private theorem levels_right {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} {k : ℕ} (hk : i.val < k) (hk' : k ≤ p + 1) :
    levelSum (MetaMathlibExt.coconutSmoothPath i x).2 k = levelSum x.2 (k + 1) := by
  by_cases hleaf : k = p + 1
  · subst hleaf
    rw [levelSum_leaves, levelSum_leaves]
    apply Finset.sum_congr rfl
    intro l _
    rfl
  · have hkp : k - 1 < p := by omega
    have hkp1 : k < p + 1 := by omega
    let j : Fin p := ⟨k - 1, hkp⟩
    let jold : Fin (p + 1) := ⟨k, hkp1⟩
    have hj : j.val + 1 = k := by simp [j]; omega
    have hjold : jold.val + 1 = k + 1 := by simp [jold]
    have hle : i.val ≤ j.val := by simp [j]; omega
    have hsucc : i.succAbove j = jold := by
      apply Fin.ext
      rw [succAbove_val_le hle]
      simp [j, jold]
      omega
    calc levelSum (MetaMathlibExt.coconutSmoothPath i x).2 k
        = (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) := hj ▸ levelSum_path _ _
      _ = x.2 (.inl (i.succAbove j)) := r_smooth_path
      _ = x.2 (.inl jold) := by rw [hsucc]
      _ = levelSum x.2 (k + 1) := (hjold ▸ (levelSum_path _ _).symm)

private theorem levelSum_path_pos {p s : ℕ} {r : Fin p ⊕ Fin s → ℕ}
    (hr : ∀ v, 0 < r v) (j : Fin p) : 0 < levelSum r (j.val + 1) := by
  rw [levelSum_path]
  exact hr _

private theorem levelSum_leaves_pos {p s : ℕ} (hs : 1 ≤ s) {r : Fin p ⊕ Fin s → ℕ}
    (hr : ∀ v, 0 < r v) : 0 < levelSum r (p + 1) := by
  rw [levelSum_leaves]
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨⟨0, by omega⟩, Finset.mem_univ _, hr _⟩

private theorem old_path_eq {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) (j : Fin (p + 1)) :
    x.1 (.inl j) * x.2 (.inl j) = levelSum x.2 j.val + levelSum x.2 (j.val + 2) :=
  (hx.2.2.1 (.inl j)).trans (path_neighborSum x.2 j)

private theorem smooth_center_eq {p s : ℕ}
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    {i : Fin (p + 1)} (hi : i.val < p) (hp : 0 < p) :
    (MetaMathlibExt.coconutSmoothPath i x).2 (.inl ⟨p - 1, by omega⟩) =
      x.2 (.inl ⟨p, by omega⟩) := by
  rw [r_smooth_path]
  have h : i.succAbove ⟨p - 1, by omega⟩ = (⟨p, by omega⟩ : Fin (p + 1)) := by
    apply Fin.ext
    rw [succAbove_val_le (by omega : i.val ≤ p - 1)]
    simp
    omega
  rw [h]

private theorem d_ge_two_pred {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) {i : Fin (p + 1)}
    (hi : i.val < p) (hd : x.1 (.inl i) = 1) {k : Fin (p + 1)} (hk : k.val + 1 = i.val) :
    2 ≤ x.1 (.inl k) := by
  have heq := old_path_eq hx k
  have hrk : x.2 (.inl k) = levelSum x.2 i.val := by
    have h : k.val + 1 = i.val := hk
    calc x.2 (.inl k) = levelSum x.2 (k.val + 1) := (levelSum_path _ _).symm
      _ = levelSum x.2 i.val := by rw [h]
  have hi_eq := old_path_eq hx i
  rw [hd, one_mul] at hi_eq
  have hri : levelSum x.2 (i.val + 1) = x.2 (.inl i) := levelSum_path _ _
  have hmid : k.val + 2 = i.val + 1 := by omega
  have hpos : 0 < levelSum x.2 (i.val + 2) := by
    have hlt : i.val + 1 < p + 1 := by omega
    have h := levelSum_path_pos hx.2.1 (⟨i.val + 1, hlt⟩ : Fin (p + 1))
    simpa using h
  rw [hmid, hri] at heq
  have hgt : x.2 (.inl k) < x.1 (.inl k) * x.2 (.inl k) := by omega
  by_contra hcon
  have hd1 : x.1 (.inl k) ≤ 1 := by omega
  have hle := Nat.mul_le_mul_right (x.2 (.inl k)) hd1
  rw [one_mul] at hle
  omega

private theorem d_ge_two_succ {p s : ℕ} (hs : 1 ≤ s)
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) {i : Fin (p + 1)}
    (hi : i.val < p) (hd : x.1 (.inl i) = 1) {k : Fin (p + 1)} (hk : k.val = i.val + 1) :
    2 ≤ x.1 (.inl k) := by
  have heq := old_path_eq hx k
  have hrk : x.2 (.inl k) = levelSum x.2 (i.val + 2) := by
    calc x.2 (.inl k) = levelSum x.2 (k.val + 1) := (levelSum_path _ _).symm
      _ = levelSum x.2 (i.val + 2) := by rw [hk]
  have hi_eq := old_path_eq hx i
  rw [hd, one_mul] at hi_eq
  have hri : levelSum x.2 (i.val + 1) = x.2 (.inl i) := levelSum_path _ _
  have hpos : 0 < levelSum x.2 (i.val + 3) ∨ 0 < levelSum x.2 i.val := by
    by_cases hiv : i.val = 0
    · left
      by_cases hleaf : i.val + 3 = p + 2
      · rw [hleaf]
        exact levelSum_leaves_pos (p := p + 1) hs hx.2.1
      · have hlt : i.val + 2 < p + 1 := by omega
        have h := levelSum_path_pos hx.2.1 (⟨i.val + 2, hlt⟩ : Fin (p + 1))
        have heq3 : i.val + 2 + 1 = i.val + 3 := by omega
        rw [heq3] at h
        exact h
    · right
      have hlt : i.val - 1 < p + 1 := by omega
      have h := levelSum_path_pos hx.2.1 (⟨i.val - 1, hlt⟩ : Fin (p + 1))
      have heq0 : i.val - 1 + 1 = i.val := by omega
      rw [heq0] at h
      exact h
  have hkv2 : k.val + 2 = i.val + 3 := by omega
  rw [hkv2, hk, hri] at heq
  have hgt : x.2 (.inl k) < x.1 (.inl k) * x.2 (.inl k) := by
    rcases hpos with h | h <;> omega
  by_contra hcon
  have hd1 : x.1 (.inl k) ≤ 1 := by omega
  have hle := Nat.mul_le_mul_right (x.2 (.inl k)) hd1
  rw [one_mul] at hle
  omega

private theorem r_at_i {p s : ℕ} {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) {i : Fin (p + 1)}
    (hd : x.1 (.inl i) = 1) :
    x.2 (.inl i) = levelSum x.2 i.val + levelSum x.2 (i.val + 2) := by
  have h := old_path_eq hx i
  rw [hd, one_mul] at h
  exact h

end IsArithmeticalStructure.coconutSmoothPath

open IsArithmeticalStructure.coconutSmoothPath in
/-- **Path smoothing preserves arithmetical structures on coconut trees.** Let $s \ge 1$ and let
$(d, r)$ be an arithmetical structure on the coconut tree $CT(p + 1, s)$, whose path vertices are
$v_1, \dots, v_{p+1}$ with central vertex $v_{p+1}$. If $d(v_k) = 1$ for some non-central path
vertex $v_k$ (that is, $1 \le k \le p$), then smoothing $(d, r)$ at $v_k$ gives an arithmetical
structure on $CT(p, s)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.3
(`integers-2025-A82-prop-1`) and Proposition 3.6 for `i = 1` (`integers-2025-A82-prop-2`). -/
public theorem IsArithmeticalStructure.coconutSmoothPath {p s : ℕ} (hs : 1 ≤ s)
    {x : (Fin (p + 1) ⊕ Fin s → ℕ) × (Fin (p + 1) ⊕ Fin s → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree (p + 1) s) x.1 x.2) (i : Fin (p + 1))
    (hi : i.val < p) (hd : x.1 (.inl i) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothPath i x).1
      (coconutSmoothPath i x).2 := by
  have hp : 0 < p := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (j | l)
    · by_cases hadj : j.val + 1 = i.val ∨ j.val = i.val
      · rw [d_smooth_path_adj hadj]
        rcases hadj with hpre | hsucc
        · have hlt : j.val < i.val := by omega
          have hkv : (i.succAbove j).val + 1 = i.val := by
            rw [succAbove_val_lt hlt]; omega
          have h2 := d_ge_two_pred hx hi hd hkv
          omega
        · have hle : i.val ≤ j.val := by omega
          have hkv : (i.succAbove j).val = i.val + 1 := by
            rw [succAbove_val_le hle]; omega
          have h2 := d_ge_two_succ hs hx hi hd hkv
          omega
      · rw [d_smooth_path_not hadj]
        exact hx.1 _
    · rw [d_smooth_leaf]
      exact hx.1 _
  · rintro (j | l)
    · rw [r_smooth_path]
      exact hx.2.1 _
    · rw [r_smooth_leaf]
      exact hx.2.1 _
  · rintro (j | l)
    · rw [path_neighborSum]
      by_cases hpre : j.val + 1 = i.val
      · have hlt : j.val < i.val := by omega
        have hkv_val : (i.succAbove j).val = j.val := succAbove_val_lt hlt
        have hkv : (i.succAbove j).val + 1 = i.val := by omega
        have h2 := d_ge_two_pred hx hi hd hkv
        rw [d_smooth_path_adj (Or.inl hpre), r_smooth_path, Nat.sub_mul, one_mul]
        have heq := old_path_eq hx (i.succAbove j)
        rw [hkv_val] at heq
        have hjv2 : j.val + 2 = i.val + 1 := by omega
        rw [hjv2] at heq
        have hri : levelSum x.2 (i.val + 1) = x.2 (.inl i) := levelSum_path _ _
        rw [hri] at heq
        have hi_eq := r_at_i hx hd
        have hrk : x.2 (.inl (i.succAbove j)) = levelSum x.2 i.val := by
          have h : (i.succAbove j).val + 1 = i.val := hkv
          calc x.2 (.inl (i.succAbove j))
              = levelSum x.2 ((i.succAbove j).val + 1) := (levelSum_path _ _).symm
            _ = levelSum x.2 i.val := by rw [h]
        have hL1 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 j.val = levelSum x.2 j.val :=
          levels_left hi (by omega)
        have hL2 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 (j.val + 2) =
            levelSum x.2 (i.val + 2) := by
          rw [hjv2]
          exact levels_right (x := x) (show i.val < i.val + 1 by omega)
            (show i.val + 1 ≤ p + 1 by omega)
        omega
      · by_cases hsucc : j.val = i.val
        · have hle : i.val ≤ j.val := by omega
          have hkv_val : (i.succAbove j).val = j.val + 1 := succAbove_val_le hle
          have hkv : (i.succAbove j).val = i.val + 1 := by omega
          have h2 := d_ge_two_succ hs hx hi hd hkv
          rw [d_smooth_path_adj (Or.inr hsucc), r_smooth_path, Nat.sub_mul, one_mul]
          have heq := old_path_eq hx (i.succAbove j)
          have hkv2 : (i.succAbove j).val + 2 = i.val + 3 := by omega
          rw [hkv2, hkv] at heq
          have hri : levelSum x.2 (i.val + 1) = x.2 (.inl i) := levelSum_path _ _
          rw [hri] at heq
          have hi_eq := r_at_i hx hd
          have hrk : x.2 (.inl (i.succAbove j)) = levelSum x.2 (i.val + 2) := by
            calc x.2 (.inl (i.succAbove j))
                = levelSum x.2 ((i.succAbove j).val + 1) := (levelSum_path _ _).symm
              _ = levelSum x.2 (i.val + 2) := by rw [hkv]
          have hL1 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 j.val =
              levelSum x.2 i.val := by
            rw [hsucc]
            exact levels_left hi le_rfl
          have hL2 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 (j.val + 2) =
              levelSum x.2 (i.val + 3) := by
            rw [hsucc]
            exact levels_right (x := x) (show i.val < i.val + 2 by omega)
              (show i.val + 2 ≤ p + 1 by omega)
          omega
        · have hadj : ¬(j.val + 1 = i.val ∨ j.val = i.val) := by
            simp [hpre, hsucc]
          rw [d_smooth_path_not hadj, r_smooth_path]
          by_cases hlt : j.val < i.val
          · have hkv : (i.succAbove j).val = j.val := succAbove_val_lt hlt
            have heq := old_path_eq hx (i.succAbove j)
            rw [hkv] at heq
            have hL1 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 j.val =
                levelSum x.2 j.val :=
              levels_left hi (by omega)
            have hL2 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 (j.val + 2) =
                levelSum x.2 (j.val + 2) :=
              levels_left hi (by omega)
            omega
          · have hle : i.val ≤ j.val := by omega
            have hkv : (i.succAbove j).val = j.val + 1 := succAbove_val_le hle
            have heq := old_path_eq hx (i.succAbove j)
            rw [hkv] at heq
            have hlt' : i.val < j.val := by omega
            have hL1 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 j.val =
                levelSum x.2 (j.val + 1) :=
              levels_right hlt' (by omega)
            have hL2 : levelSum (MetaMathlibExt.coconutSmoothPath i x).2 (j.val + 2) =
                levelSum x.2 (j.val + 2 + 1) :=
              levels_right (by omega) (by omega)
            have hjv : j.val + 1 + 2 = j.val + 2 + 1 := by omega
            rw [hjv] at heq
            omega
    · rw [leaf_neighborSum hp, d_smooth_leaf, r_smooth_leaf]
      have hold := hx.2.2.1 (.inr l)
      have hp1 : 0 < p + 1 := by omega
      rw [leaf_neighborSum (p := p + 1) hp1] at hold
      have hcenter := smooth_center_eq (x := x) hi hp
      rw [hcenter]
      have hcen : (⟨p + 1 - 1, by omega⟩ : Fin (p + 1)) = ⟨p, by omega⟩ := by
        apply Fin.ext
        simp
      rw [hcen] at hold
      exact hold
  · intro g hg
    apply hx.2.2.2 g
    rintro (k | l)
    · refine i.succAboveCases ?_ ?_ k
      · have hr := r_at_i hx hd
        rw [hr]
        apply dvd_add
        · by_cases hiv : i.val = 0
          · rw [hiv, levelSum_zero]
            exact dvd_zero _
          · have hlt : i.val - 1 < p := by omega
            let j : Fin p := ⟨i.val - 1, hlt⟩
            have hjval : j.val = i.val - 1 := rfl
            have hltj : j.val < i.val := by omega
            have hsucc : (i.succAbove j).val + 1 = i.val := by
              rw [succAbove_val_lt hltj]
              omega
            have heq : levelSum x.2 i.val = (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) := by
              rw [← hsucc, levelSum_path, ← r_smooth_path]
            rw [heq]
            exact hg _
        · let j : Fin p := ⟨i.val, hi⟩
          have hle : i.val ≤ j.val := by simp [j]
          have hsucc : (i.succAbove j).val + 1 = i.val + 2 := by
            rw [succAbove_val_le hle]
          have heq : levelSum x.2 (i.val + 2) =
              (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) := by
            rw [← hsucc, levelSum_path, ← r_smooth_path]
          rw [heq]
          exact hg _
      · intro j
        have h : x.2 (.inl (i.succAbove j)) = (MetaMathlibExt.coconutSmoothPath i x).2 (.inl j) :=
          r_smooth_path.symm
        rw [h]
        exact hg _
    · exact hg (.inr l)

end MetaMathlibExt
