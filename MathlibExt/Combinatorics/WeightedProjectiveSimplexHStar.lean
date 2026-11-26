/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # The explicit $h^*$-formula and its first reflexive stabilization -/

namespace MetaMathlibExt

/-- **The $h^*$ formula of a weight vector.** For a list $q = (q_1, \dots, q_n)$ of natural
numbers, put $|q| = q_1 + \dots + q_n$ and define the weight statistic
$w(q,b) = b - \sum_{i=1}^n \lfloor q_i b / (1 + |q|) \rfloor$. The $h^*$ formula of $q$ is the
integer polynomial $\sum_{b=0}^{|q|} z^{w(q,b)}$.

It is named a formula, not defined to be $h^*$; Theorem 5 relates it to the independently
defined Ehrhart-series condition.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
@[expose] public noncomputable def hStarFormula (q : List ℕ) : Polynomial ℤ :=
  ∑ b ∈ Finset.range (q.sum + 1), Polynomial.X ^ weightStatistic q b

private theorem foldl_lcm_ne_zero_iff (p : List ℕ) (d : ℕ) :
    p.foldl Nat.lcm d ≠ 0 ↔ d ≠ 0 ∧ ∀ a ∈ p, 0 < a := by
  induction p generalizing d with
  | nil => simp
  | cons a p ih =>
    simp only [List.foldl_cons, ih, ne_eq, Nat.lcm_eq_zero_iff, not_or, List.forall_mem_cons,
      Nat.pos_iff_ne_zero, and_assoc]

-- At the final index, the floor for a positive weight `a` is `a - 1`.
private theorem final_floor_add_one {a n : ℕ} (ha : 0 < a) (hle : a ≤ n) :
    a * n / (1 + n) + 1 = a := by
  rw [Nat.add_comm 1 n]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hkn : k ≤ n := by omega
  have hdiv : (k + 1) * n / (n + 1) = k :=
    Nat.div_eq_of_lt_le
      (by simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] using
        Nat.add_le_add_left hkn (k * n))
      (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) (Nat.succ_pos k))
  rw [hdiv]

private theorem weightStatistic_sum (p : List ℕ) (hpos : ∀ a ∈ p, 0 < a) :
    weightStatistic p p.sum = p.length := by
  have hsum : (p.map fun a => a * p.sum / (1 + p.sum)).sum + p.length = p.sum := by
    calc
      _ = (p.map fun a => a * p.sum / (1 + p.sum) + 1).sum := by
        rw [List.sum_map_add, List.map_const', List.sum_const_nat, Nat.mul_one]
      _ = (p.map id).sum := by
        congr 1
        exact List.map_congr_left fun a ha =>
          final_floor_add_one (hpos a ha) (List.le_sum_of_mem ha)
      _ = p.sum := by rw [List.map_id]
  rw [weightStatistic]
  omega

/-- **The first reflexive stabilization adds one monomial to the $h^*$-formula.** Let
$q = (q_1, \dots, q_n)$ be a list of natural numbers whose reflexive stabilization number is
$1$, so that its first reflexive stabilization is $\operatorname{rs}(q) = (1, q_1, \dots, q_n)$.
For a list $p = (p_1, \dots, p_m)$ of natural numbers put $|p| = p_1 + \dots + p_m$, let
$\ell(p) = \lfloor (1 + |p|) / \operatorname{lcm}(p) \rfloor$ (taken to be $0$ when
$\operatorname{lcm}(p) = 0$), let
$w(p, b) = b - \sum_{i=1}^{m} \lfloor p_i b / (1 + |p|) \rfloor$ be its weight statistic, and let
$h_p(z) = \sum_{b=0}^{|p|} z^{w(p, b)} \in \mathbb{Z}[z]$ be its explicit $h^*$-formula. Suppose
that $\ell(\operatorname{rs}(q)) = 1$. Then $h_{\operatorname{rs}(q)}(z) = h_q(z) + z^{n+1}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public theorem stabilization_hStar_add_monomial (q : List ℕ)
    (hrsn : reflexiveStabilizationNumber q = 1)
    (hell : listEll (reflexiveStabilization q) = 1) :
    hStarFormula (reflexiveStabilization q) =
      hStarFormula q + Polynomial.X ^ (q.length + 1) := by
  have hrs : reflexiveStabilization q = 1 :: q := by
    rw [reflexiveStabilization, hrsn, List.replicate_one, List.singleton_append]
  have hsum : (reflexiveStabilization q).sum = q.sum + 1 := by
    rw [hrs, List.sum_cons, Nat.add_comm]
  -- A zero weight would make the lcm, and hence `listEll`, zero.
  have hlcm : weightLcm (reflexiveStabilization q) ≠ 0 := by
    intro hz
    simp only [listEll, hz, Nat.div_zero, zero_ne_one] at hell
  have hpos := ((foldl_lcm_ne_zero_iff (reflexiveStabilization q) 1).1 hlcm).2
  have hlast : weightStatistic (reflexiveStabilization q) (q.sum + 1) = q.length + 1 := by
    rw [← hsum, weightStatistic_sum _ hpos, hrs, List.length_cons]
  -- Split off the new endpoint and compare the summands on the old range.
  unfold hStarFormula
  rw [hsum, Finset.sum_range_succ, hlast]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [stabilization_weightStatistic_eq q hrsn hell b (Nat.lt_succ_iff.1 (Finset.mem_range.1 hb))]

end MetaMathlibExt
