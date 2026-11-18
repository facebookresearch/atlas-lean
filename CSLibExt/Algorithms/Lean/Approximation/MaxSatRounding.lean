/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Complex.ExponentialBounds
public import CSLibExt.Logics.Propositional.CNF.Semantics

/-!
# The Goemans–Williamson 3/4-approximation for MAX SAT

M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum
satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666.

Clauses are the repository's CNF clauses `Cslib.Logic.PL.CNFClause` (lists of literals
`(variable, polarity)`). Setting each variable `x_i` true independently with probability `p_i`,
a clause is falsified exactly when all its literals are false, so for a clause whose literals
use distinct variables its satisfaction probability is
`1 - ∏_{i ∈ P} (1 - p_i) ∏_{i ∈ N} p_i` (§2). This file works with that closed form,
`clauseSatProb`, and does not formalize the probability space.

A list may repeat a variable. For such a clause the closed form is not the satisfaction
probability, and `lpClauseBound` counts the repeated literal twice where the paper's LP sums over
sets: for `x₀ ∨ x₀` with `p₀ = 1/2` the closed form is `3/4` while the probability is `1/2`. The
theorems below are true inequalities about the closed form for every clause; their reading as the
paper's probabilistic statements (Lemma 3.1, Theorem 4.1, a `3/4`-approximation in expectation)
holds for clauses whose literals use distinct variables, which is the paper's setting.

In the list below, "probability" and "expected weight" mean the closed forms; they are the
true probabilities and expectations for clauses with distinct variables.

* `clauseSatProb_half` : Johnson's assignment `p_i = 1/2` satisfies a `k`-literal clause with
  probability `1 - 2^{-k}` (§2).
* `roundingFactor_mul_le_clauseSatProb` : their Lemma 3.1; for every feasible solution
  `(y, z)` of the linear relaxation (LP), randomized rounding `p_i = y_i` satisfies a clause
  with `k` literals with probability at least `β_k z_j`, `β_k = 1 - (1 - 1/k)^k`.
* `three_quarters_le_max_expectedWeight` : their Theorem 4.1; the better of the two
  assignments has expected weight at least `(3/4) ∑_j w_j z_j`.
* `three_quarters_le_max_expectedWeight_of_optimal` : with `(y, z)` optimal for (LP), the
  better expected weight is at least `3/4` of the weight satisfied by any truth assignment.
-/

@[expose] public section

namespace CSLibExt.Algorithms.Approximation.MaxSat

open Cslib.Logic.PL Finset

/-- **Probability that a literal is true.** If variable `i` is true with probability `p i`,
the literal `(i, true)` is true with probability `p i` and `(i, false)` with probability
`1 - p i`. Evaluated at an LP solution `y`, it is the literal's contribution to the left-hand
side `∑_{i ∈ P} y_i + ∑_{i ∈ N} (1 - y_i)` of the clause constraint of (LP) (Goemans and
Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §3). -/
noncomputable def literalProb (p : ℕ → ℝ) (l : ℕ × Bool) : ℝ := if l.2 then p l.1 else 1 - p l.1

/-- **Satisfaction probability of a clause.** `1 - ∏_l (1 - P[l true])`, the probability that a
clause whose literals use distinct variables is satisfied when the variables are set
independently (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2). -/
noncomputable def clauseSatProb (p : ℕ → ℝ) (C : CNFClause) : ℝ :=
  1 - (C.map fun l => 1 - literalProb p l).prod

/-- **Left-hand side of the clause constraint of the MAX SAT relaxation.**
`∑_{i ∈ P_j} y_i + ∑_{i ∈ N_j} (1 - y_i)` (Goemans and Williamson, *SIAM J. Discrete Math.*
7(4) (1994), §3, constraint of (IP) and (LP)). -/
noncomputable def lpClauseBound (y : ℕ → ℝ) (C : CNFClause) : ℝ := (C.map (literalProb y)).sum

/-- **The randomized-rounding factor.** `β_k = 1 - (1 - 1/k)^k` (Goemans and Williamson,
*SIAM J. Discrete Math.* 7(4) (1994), Lemma 3.1). -/
noncomputable def roundingFactor (k : ℕ) : ℝ := 1 - (1 - 1 / (k : ℝ)) ^ k

private theorem prod_map_const (C : CNFClause) (c : ℝ) :
    (C.map fun _ => c).prod = c ^ C.length := by
  induction C with
  | nil => simp
  | cons a C ih => simp [pow_succ, mul_comm]

/-- **Johnson's random assignment.** With every variable true with probability `1/2`, the
closed-form satisfaction probability of a clause with `k` literals is `1 - 2^{-k}`; for a clause
whose literals use distinct variables this is the probability that Johnson's assignment
satisfies it (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2). -/
theorem clauseSatProb_half (C : CNFClause) :
    clauseSatProb (fun _ => 1 / 2) C = 1 - (1 / 2 : ℝ) ^ C.length := by
  unfold clauseSatProb literalProb
  have : (C.map fun l : ℕ × Bool => 1 - if l.2 then (1 / 2 : ℝ) else 1 - 1 / 2) =
      C.map fun _ => (1 / 2 : ℝ) := by
    refine List.map_congr_left fun l _ => ?_
    split_ifs <;> norm_num
  rw [this, prod_map_const]

/-- AM–GM in power form: `∏ z_i ≤ ((∑ z_i) / n)^n` for nonnegative `z : Fin n → ℝ`. -/
private theorem prod_le_mean_pow {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / n) ^ n := by
  have hsum_pos : (0 : ℝ) < ∑ _i : Fin n, (1 : ℝ) := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean (univ : Finset (Fin n)) (fun _ => (1 : ℝ)) z
    (fun _ _ => zero_le_one) hsum_pos (fun i _ => hz i)
  simp only [Real.rpow_one, one_mul] at h
  have hsum : ∑ _i ∈ (univ : Finset (Fin n)), (1 : ℝ) = (n : ℝ) := by simp
  rw [hsum] at h
  have hprod : 0 ≤ ∏ i, z i := prod_nonneg fun i _ => hz i
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hprod _) h n
  rwa [Real.rpow_inv_natCast_pow hprod (Nat.pos_iff_ne_zero.mp hn)] at hpow

/-- **Goemans–Williamson Lemma 3.1.** Let `0 ≤ y_i ≤ 1` on the variables of a clause `C` with
`k` literals, and `0 ≤ z ≤ min(1, ∑_{i ∈ P} y_i + ∑_{i ∈ N} (1 - y_i))`. Then the closed-form
satisfaction probability of `C` under `p_i = y_i` is at least `β_k z`, `β_k = 1 - (1 - 1/k)^k`.
For a clause whose literals use distinct variables, as in the paper, this says that randomized
rounding satisfies `C` with probability at least `β_k z` (Goemans and Williamson, *SIAM J.
Discrete Math.* 7(4) (1994), Lemma 3.1, proved as there by the arithmetic–geometric mean
inequality and concavity). The inequality itself holds for every clause. -/
theorem roundingFactor_mul_le_clauseSatProb {y : ℕ → ℝ} {C : CNFClause} {z : ℝ}
    (hy : ∀ l ∈ C, 0 ≤ y l.1 ∧ y l.1 ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hz : z ≤ lpClauseBound y C) :
    roundingFactor C.length * z ≤ clauseSatProb y C := by
  rcases Nat.eq_zero_or_pos C.length with hk | hk
  · rw [List.length_eq_zero_iff] at hk
    subst hk
    simp [roundingFactor, clauseSatProb]
  set k := C.length with hkdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  -- the literal values `a_l = 1 - P[l true]` lie in `[0, 1]`
  have hlit : ∀ l ∈ C, 0 ≤ literalProb y l ∧ literalProb y l ≤ 1 := by
    intro l hl
    obtain ⟨h0, h1⟩ := hy l hl
    unfold literalProb
    split_ifs <;> constructor <;> linarith
  let a : Fin k → ℝ := fun i => 1 - literalProb y C[i.1]
  have ha : ∀ i, 0 ≤ a i := fun i => by
    have := (hlit C[i.1] (List.getElem_mem _)).2
    simp only [a]; linarith
  have hprod : (C.map fun l => 1 - literalProb y l).prod = ∏ i, a i := by
    simp only [a]
    exact (Fin.prod_univ_fun_getElem C (fun l => 1 - literalProb y l)).symm
  have hsum : ∑ i, a i = k - lpClauseBound y C := by
    simp only [a, lpClauseBound]
    rw [sum_sub_distrib, Fin.sum_univ_fun_getElem C (literalProb y)]
    simp [hkdef]
  -- AM–GM
  have hamgm := prod_le_mean_pow hk a ha
  rw [hsum] at hamgm
  have hmean_nonneg : 0 ≤ (k - lpClauseBound y C) / k := by
    rw [← hsum]; exact div_nonneg (sum_nonneg fun i _ => ha i) hkR.le
  have hmean_le : (k - lpClauseBound y C) / k ≤ 1 - z / k := by
    rw [div_le_iff₀ hkR]
    have : (1 - z / k) * k = k - z := by field_simp
    linarith
  have hstep : ∏ i, a i ≤ (1 - z / k) ^ k :=
    hamgm.trans (pow_le_pow_left₀ hmean_nonneg hmean_le k)
  -- convexity of `t ↦ t ^ k` on `[0, ∞)`
  have hconv := (convexOn_pow k).2 (Set.mem_Ici.2 (zero_le_one : (0 : ℝ) ≤ 1))
    (Set.mem_Ici.2 (show (0 : ℝ) ≤ 1 - 1 / k by
      have : 1 / (k : ℝ) ≤ 1 := by
        rw [div_le_one hkR]; exact_mod_cast hk
      linarith))
    (show 0 ≤ 1 - z by linarith) hz0 (by ring)
  simp only [smul_eq_mul, one_pow, mul_one] at hconv
  have hpt : (1 - z) + z * (1 - 1 / (k : ℝ)) = 1 - z / k := by ring
  rw [hpt] at hconv
  unfold clauseSatProb roundingFactor
  rw [hprod]
  nlinarith

/-- **The per-clause inequality behind the 3/4 guarantee.** For every `k`,
`(1 - 2^{-k}) + β_k ≥ 3/2` (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994),
proof of Theorem 4.1: equality for `k = 1, 2`, and `7/8 + 1 - 1/e ≥ 3/2` for `k ≥ 3`, using
`(1 - 1/k)^k ≤ 1/e ≤ 3/8`). -/
theorem three_halves_le_johnson_add_roundingFactor {k : ℕ} (hk : 0 < k) :
    (3 / 2 : ℝ) ≤ (1 - (1 / 2 : ℝ) ^ k) + roundingFactor k := by
  unfold roundingFactor
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
  · norm_num
  · norm_num
  · have hkR : (3 : ℝ) ≤ k := by exact_mod_cast h3
    have hhalf : (1 / 2 : ℝ) ^ k ≤ 1 / 8 := by
      calc (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ 3 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) h3
        _ = 1 / 8 := by norm_num
    have hbase0 : 0 ≤ 1 - 1 / (k : ℝ) := by
      have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hexp : (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) := by
      have h1 : 1 - 1 / (k : ℝ) ≤ Real.exp (-(1 / k)) := by
        have := Real.add_one_le_exp (-(1 / (k : ℝ)))
        linarith
      calc (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-(1 / k)) ^ k := pow_le_pow_left₀ hbase0 h1 k
        _ = Real.exp (-1) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
    have he : Real.exp (-1) ≤ 3 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.exp_one_gt_d9
      linarith
    linarith

/-- **Goemans–Williamson Theorem 4.1, per clause.** For a clause `C`, `0 ≤ y ≤ 1` on its
variables, and `0 ≤ z ≤ min(1, ∑_{i ∈ P} y_i + ∑_{i ∈ N} (1 - y_i))`, the average of the
closed-form satisfaction probabilities under Johnson's assignment and under randomized rounding
is at least `(3/4) z`; for a clause with distinct variables these are the true probabilities
(Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), proof of Theorem 4.1). -/
theorem three_quarters_mul_le_average {y : ℕ → ℝ} {C : CNFClause} {z : ℝ}
    (hy : ∀ l ∈ C, 0 ≤ y l.1 ∧ y l.1 ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hz : z ≤ lpClauseBound y C) :
    (3 / 4 : ℝ) * z ≤ (clauseSatProb (fun _ => 1 / 2) C + clauseSatProb y C) / 2 := by
  have hr := roundingFactor_mul_le_clauseSatProb hy hz0 hz1 hz
  rw [clauseSatProb_half]
  rcases Nat.eq_zero_or_pos C.length with hk | hk
  · rw [List.length_eq_zero_iff] at hk
    subst hk
    have : z ≤ 0 := by simpa [lpClauseBound] using hz
    simp [clauseSatProb]
    linarith
  have hkey := three_halves_le_johnson_add_roundingFactor hk
  have hA : 0 ≤ 1 - (1 / 2 : ℝ) ^ C.length := by
    have : (1 / 2 : ℝ) ^ C.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  nlinarith

/-- **Feasible solutions of the MAX SAT linear relaxation.** For clauses `C j`, `j < m`,
`(y, z)` is feasible for (LP) when `0 ≤ y_i ≤ 1`, `0 ≤ z_j ≤ 1` and
`z_j ≤ ∑_{i ∈ P_j} y_i + ∑_{i ∈ N_j} (1 - y_i)` (Goemans and Williamson, *SIAM J. Discrete
Math.* 7(4) (1994), §3). -/
def LPFeasible {m : ℕ} (C : Fin m → CNFClause) (y : ℕ → ℝ) (z : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∀ j, 0 ≤ z j ∧ z j ≤ 1 ∧ z j ≤ lpClauseBound y (C j)

/-- **Expected weight of a randomized assignment.** `∑_j w_j · clauseSatProb p (C j)`. When every
clause uses distinct variables, this is the expected satisfied weight when variable `i` is true
independently with probability `p i` (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4)
(1994), §2); otherwise it is only the closed form. -/
noncomputable def expectedWeight {m : ℕ} (w : Fin m → ℝ) (C : Fin m → CNFClause)
    (p : ℕ → ℝ) : ℝ :=
  ∑ j, w j * clauseSatProb p (C j)

/-- **Goemans–Williamson Theorem 4.1.** For nonnegative weights and a feasible solution
`(y, z)` of (LP), let `Ŵ₁` be the expected weight under `p_i = 1/2` and `Ŵ₂` under
`p_i = y_i`. Then `max(Ŵ₁, Ŵ₂) ≥ (Ŵ₁ + Ŵ₂) / 2 ≥ (3/4) ∑_j w_j z_j` (Goemans and Williamson,
*SIAM J. Discrete Math.* 7(4) (1994), Theorem 4.1, stated there for an optimal `(y, z)`; the
proof uses only feasibility). `Ŵ₁`, `Ŵ₂` are the closed forms `expectedWeight`, which are
expected weights when every clause uses distinct variables. -/
theorem three_quarters_le_max_expectedWeight {m : ℕ} {w : Fin m → ℝ} {C : Fin m → CNFClause}
    {y : ℕ → ℝ} {z : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j) (hf : LPFeasible C y z) :
    (3 / 4 : ℝ) * ∑ j, w j * z j ≤
        (expectedWeight w C (fun _ => 1 / 2) + expectedWeight w C y) / 2 ∧
      (expectedWeight w C (fun _ => 1 / 2) + expectedWeight w C y) / 2 ≤
        max (expectedWeight w C (fun _ => 1 / 2)) (expectedWeight w C y) := by
  refine ⟨?_, by
    rcases le_total (expectedWeight w C (fun _ => 1 / 2)) (expectedWeight w C y) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith⟩
  unfold expectedWeight
  rw [mul_sum, ← sum_add_distrib, sum_div]
  refine sum_le_sum fun j _ => ?_
  obtain ⟨hz0, hz1, hz⟩ := hf.2 j
  have h := three_quarters_mul_le_average (fun l _ => hf.1 l.1) hz0 hz1 hz
  have := mul_le_mul_of_nonneg_left h (hw j)
  linarith

/-- **Weight satisfied by a truth assignment.** `∑_{j : C_j satisfied by a} w_j`. -/
noncomputable def satisfiedWeight {m : ℕ} (w : Fin m → ℝ) (C : Fin m → CNFClause)
    (a : ℕ → Bool) : ℝ := by
  classical
  exact ∑ j, if CNFClause.Satisfies a (C j) then w j else 0

/-- **Truth assignments are feasible for the relaxation.** The incidence vector `y_i = [a_i]`,
`z_j = [C_j satisfied]` of a truth assignment is feasible for (LP), with objective the satisfied
weight; hence the optimal value of (LP) is at least the MAX SAT optimum (Goemans and Williamson,
*SIAM J. Discrete Math.* 7(4) (1994), §3, `Z*_LP ≥ Z*_IP`). -/
theorem lpFeasible_of_assignment {m : ℕ} (w : Fin m → ℝ) (C : Fin m → CNFClause)
    (a : ℕ → Bool) : ∃ y z, LPFeasible C y z ∧ ∑ j, w j * z j = satisfiedWeight w C a := by
  classical
  refine ⟨fun i => if a i then 1 else 0,
    fun j => if CNFClause.Satisfies a (C j) then 1 else 0, ⟨fun i => ?_, fun j => ?_⟩, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · dsimp only
    have hnn : ∀ l ∈ C j, 0 ≤ literalProb (fun i => if a i then 1 else 0) l := by
      intro l _
      simp only [literalProb]
      split_ifs <;> norm_num
    have hsum_nn : 0 ≤ lpClauseBound (fun i => if a i then 1 else 0) (C j) := by
      unfold lpClauseBound
      exact List.sum_nonneg fun x hx => by
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
        exact hnn l hl
    refine ⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num, ?_⟩
    split_ifs with hs
    · obtain ⟨l, hl, hsat⟩ := (CNFClause.satisfies_def).1 hs
      have hl1 : literalProb (fun i => if a i then 1 else 0) l = 1 := by
        simp only [literalProb]
        cases hb : l.2 <;> simp_all
      unfold lpClauseBound
      have := List.single_le_sum (fun x hx => by
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hx
        exact hnn l' hl') _ (List.mem_map.2 ⟨l, hl, rfl⟩)
      rw [hl1] at this
      exact this
    · exact hsum_nn
  · unfold satisfiedWeight
    refine sum_congr rfl fun j _ => ?_
    dsimp only
    by_cases hs : CNFClause.Satisfies a (C j)
    · simp only [hs, ↓reduceIte, mul_one]
    · simp only [hs, ↓reduceIte, mul_zero]

/-- **The 3/4 guarantee against the MAX SAT optimum.** For nonnegative weights, if `(y, z)` is
an optimal solution of (LP), then for every truth assignment `a`,
`max(Ŵ₁, Ŵ₂) ≥ (3/4) · (weight satisfied by a)` for the closed forms `Ŵ₁`, `Ŵ₂`. For
instances whose clauses use distinct variables, the paper's setting, `Ŵ₁` and `Ŵ₂` are expected
weights, so the better of Johnson's assignment and randomized rounding is a
`3/4`-approximation in expectation (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4)
(1994), Theorem 4.1 with `Z*_LP ≥ Z*_IP`). For clauses repeating a variable that reading fails:
for the single clause `x₀ ∨ x₀`, `y₀ = 1/2`, `z = 1` is optimal and both closed forms are `3/4`,
while both roundings satisfy the clause with probability `1/2`. -/
theorem three_quarters_le_max_expectedWeight_of_optimal {m : ℕ} {w : Fin m → ℝ}
    {C : Fin m → CNFClause} {y : ℕ → ℝ} {z : Fin m → ℝ} (hw : ∀ j, 0 ≤ w j)
    (hf : LPFeasible C y z)
    (hopt : ∀ y' z', LPFeasible C y' z' → ∑ j, w j * z' j ≤ ∑ j, w j * z j) (a : ℕ → Bool) :
    (3 / 4 : ℝ) * satisfiedWeight w C a ≤
      max (expectedWeight w C (fun _ => 1 / 2)) (expectedWeight w C y) := by
  obtain ⟨y', z', hf', hval⟩ := lpFeasible_of_assignment w C a
  have h1 := hopt y' z' hf'
  rw [hval] at h1
  obtain ⟨h2, h3⟩ := three_quarters_le_max_expectedWeight hw hf
  linarith

end CSLibExt.Algorithms.Approximation.MaxSat
