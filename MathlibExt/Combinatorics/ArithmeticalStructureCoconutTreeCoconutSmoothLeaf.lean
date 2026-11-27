/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.SuccPred
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTree
import all MathlibExt.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath

/-!
# Leaf smoothing on coconut trees

Smoothing a leaf with `d`-label `1` preserves an arithmetical structure when at least two
vertices remain. The deleted leaf has the same `r`-label as the centre, so only the centre's
`d`-label decreases and the common divisors of the `r`-labels are unchanged.

## References

* Alexander Diaz-Lopez, Brian Ha, Pamela E. Harris, Jonathan Rogers, Theo Koss, and Dorian
  Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82,
  pp. 1–23, Definition 5 and Proposition 2, Case 2 (Section 3.1). These are Definition 3.4
  and Proposition 3.6 in arXiv:2406.11183.
* Kassie Archer, Abigail C. Bishop, Alexander Diaz-Lopez, Luis D. García Puente, Darren
  Glass, and Joel Louwsma, *Arithmetical structures on bidents*, Discrete Mathematics 343
  (2020), Article 111850, Section 2.2.1. The coconut-tree paper credits this smoothing method
  on bidents.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Smoothing at a leaf of a coconut tree.** Let the coconut tree $CT(p, s + 1)$ have path
vertices $v_1, \dots, v_p$, central vertex $v_p$ and leaves $\ell_1, \dots, \ell_{s+1}$, let $d$
and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le s + 1$. Smoothing
$(d, r)$ at the leaf $\ell_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$\ell_k$ and renumbering the remaining leaves $\ell_1, \dots, \ell_{k-1}, \ell_{k+1}, \dots,
\ell_{s+1}$ in order as $\ell_1, \dots, \ell_s$. Every remaining vertex keeps its value of $r$
and its value of $d$, except that $d$ drops by $1$ (truncated at $0$) at the central vertex $v_p$
when $p \ge 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.4
(arXiv numbering). -/
public def coconutSmoothLeaf {p s : ℕ} (l : Fin (s + 1))
    (x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)) :
    (Fin p ⊕ Fin s → ℕ) × (Fin p ⊕ Fin s → ℕ) :=
  (Sum.elim (fun j => if j.val + 1 = p then x.1 (.inl j) - 1 else x.1 (.inl j))
      (fun m => x.1 (.inr (l.succAbove m))),
    Sum.elim (fun j => x.2 (.inl j)) (fun m => x.2 (.inr (l.succAbove m))))

end

open IsArithmeticalStructure.coconutSmoothPath in
/-- **Smoothing a leaf preserves arithmetical structures.** Let $p$ and $s$ be natural numbers
with $p + s \ge 2$, let $(d, r)$ be an arithmetical structure on the coconut tree
$CT(p, s + 1)$, and let $\ell$ be a leaf with $d(\ell) = 1$. Then the labelings $(d', r')$
obtained by smoothing $(d, r)$ at $\ell$ form an arithmetical structure on $CT(p, s)$.

The hypothesis $p + s \ge 2$ excludes the single-edge tree $CT(1, 1)$: there $d = r = (1, 1)$,
and smoothing the leaf gives $d' = 0$ at the remaining vertex, which is not an arithmetical
structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 3.6
(`integers-2025-A82-prop-2`). -/
public theorem IsArithmeticalStructure.coconutSmoothLeaf {p s : ℕ} (hps : 2 ≤ p + s)
    {x : (Fin p ⊕ Fin (s + 1) → ℕ) × (Fin p ⊕ Fin (s + 1) → ℕ)}
    (hx : IsArithmeticalStructure (coconutTree p (s + 1)) x.1 x.2) (l : Fin (s + 1))
    (hd : x.1 (.inr l) = 1) :
    IsArithmeticalStructure (coconutTree p s) (coconutSmoothLeaf l x).1
      (coconutSmoothLeaf l x).2 := by
  by_cases hp0 : p = 0
  · subst p
    have h : {w | (coconutTree 0 (s + 1)).Adj (.inr l) w} = ∅ := by
      ext (j | j)
      · exact Fin.elim0 j
      · simp [coconutTree_not_adj_inr_inr]
    have heq := hx.2.2.1 (.inr l)
    rw [hd, one_mul, h, finsum_mem_empty] at heq
    exact ((hx.2.1 (.inr l)).ne' heq).elim
  have hp := Nat.pos_of_ne_zero hp0
  let c : Fin p := ⟨p - 1, by omega⟩
  have hc : c.val + 1 = p := by simp [c]; omega
  have hrl : x.2 (.inr l) = x.2 (.inl c) := by
    simpa only [hd, one_mul, leaf_neighborSum hp] using hx.2.2.1 (.inr l)
  let t := MetaMathlibExt.coconutSmoothLeaf l x
  have hr : ∀ v, 0 < t.2 v := by
    rintro (j | j)
    · exact hx.2.1 (.inl j)
    · exact hx.2.1 (.inr (l.succAbove j))
  have hcenter (j : Fin p) : j.val + 1 = p ↔ j = c :=
    ⟨fun h => Fin.ext (by omega), fun h => h ▸ hc⟩
  have hdl (j : Fin p) :
      t.1 (.inl j) = if j = c then x.1 (.inl j) - 1 else x.1 (.inl j) := by
    simp [t, MetaMathlibExt.coconutSmoothLeaf, hcenter]
  -- Only the final level (the leaves) changes; the missing summand is the centre's label.
  have hlevels (k : ℕ) (hk : k ≤ p) : levelSum t.2 k = levelSum x.2 k := by
    cases k with
    | zero => rw [levelSum_zero, levelSum_zero]
    | succ k =>
      let j : Fin p := ⟨k, by omega⟩
      change levelSum t.2 (j.val + 1) = levelSum x.2 (j.val + 1)
      rw [levelSum_path, levelSum_path]
      rfl
  have hleaves : levelSum x.2 (p + 1) = x.2 (.inl c) + levelSum t.2 (p + 1) := by
    rw [levelSum_leaves, levelSum_leaves, Fin.sum_univ_succAbove _ l, hrl]
    rfl
  have hold (j : Fin p) :
      x.1 (.inl j) * x.2 (.inl j) = levelSum x.2 j.val + levelSum x.2 (j.val + 2) :=
    (hx.2.2.1 (.inl j)).trans (path_neighborSum x.2 j)
  have hc2 : c.val + 2 = p + 1 := by omega
  have hceq := hold c
  rw [hc2, hleaves] at hceq
  -- A remaining leaf, or the preceding path vertex, contributes a positive summand.
  have hremaining : 0 < levelSum x.2 c.val + levelSum t.2 (p + 1) := by
    by_cases hs : 1 ≤ s
    · exact Nat.add_pos_right _ (levelSum_leaves_pos hs hr)
    · have hcp : 0 < c.val := by omega
      let j : Fin p := ⟨c.val - 1, by omega⟩
      have hj : j.val + 1 = c.val := by dsimp [j]; omega
      rw [← hj]
      exact Nat.add_pos_left (levelSum_path_pos hx.2.1 j) _
  have hdc : 1 < x.1 (.inl c) := by
    have hmul : 1 * x.2 (.inl c) < x.1 (.inl c) * x.2 (.inl c) := by
      rw [one_mul, hceq]
      omega
    exact Nat.lt_of_mul_lt_mul_right hmul
  change IsArithmeticalStructure (coconutTree p s) t.1 t.2
  refine ⟨?_, hr, ?_, ?_⟩
  · rintro (j | j)
    · rw [hdl]
      by_cases hj : j = c
      · subst j
        rw [ite_eq_left rfl]
        omega
      · rw [ite_eq_right hj]
        exact hx.1 _
    · exact hx.1 (.inr (l.succAbove j))
  · rintro (j | j)
    · rw [path_neighborSum, hdl, hlevels _ j.isLt.le]
      change _ * x.2 (.inl j) = _
      by_cases hj : j = c
      · subst j
        rw [ite_eq_left rfl, Nat.sub_mul, one_mul, hc2, hceq]
        omega
      · have hjp : j.val + 2 ≤ p := by
          have hn := fun he => hj ((hcenter j).mp he)
          have := j.isLt
          omega
        rw [ite_eq_right hj, hlevels _ hjp]
        exact hold j
    · rw [leaf_neighborSum hp]
      exact (hx.2.2.1 (.inr (l.succAbove j))).trans (leaf_neighborSum hp x.2 _)
  · intro g hg
    apply hx.2.2.2 g
    rintro (j | j)
    · exact hg (.inl j)
    · refine l.succAboveCases ?_ (fun i => hg (.inr i)) j
      rw [hrl]
      exact hg (.inl c)

end MetaMathlibExt
