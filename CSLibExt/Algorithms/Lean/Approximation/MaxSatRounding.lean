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
`(variable, polarity)`). As in the paper, where a clause is given by disjoint sets `P_j`, `N_j`
of variables, every clause must use distinct variables: `(C.map Prod.fst).Nodup`, no variable
occurring twice in either polarity. `clauseSatProb` and `expectedWeight` take this hypothesis as
an argument, and so does every statement below that reads them as a probability or an
expectation. They also take a proof that the rounding probabilities lie in `[0, 1]`
(`∀ i, 0 ≤ p i ∧ p i ≤ 1`): for other values the closed form is not a probability (with
`p₀ = 2` the clause `x₀` would be satisfied with "probability" `2`). The LP side
(`literalProb`, `lpClauseBound`, `LPFeasible`) stays defined for every real point.

Setting each variable `x_i` true independently with probability `p_i`, a clause is falsified
exactly when all its literals are false; with distinct variables these events are independent,
so the clause is satisfied with probability `1 - ∏_{i ∈ P} (1 - p_i) ∏_{i ∈ N} p_i` (§2). This
file works with that closed form, `clauseSatProb`, and proves that it is the satisfaction
probability (`clauseSatProb_eq_sum_assignments`, an explicit sum over the assignments of the
clause's variables). For a clause repeating a variable the closed form is not the probability:
for `x₀ ∨ x₀` with `p₀ = 1/2` it would be `3/4` while the probability is `1/2`; such clauses are
excluded. With distinct variables, `lpClauseBound` is the left-hand side of the paper's LP
constraint.

* `clauseSatProb_eq_sum_assignments` : for a clause with distinct variables, `clauseSatProb`
  is the probability that independent rounding satisfies it (§2).
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
Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §3). It is a probability when
`0 ≤ p i ≤ 1`; it is defined for every real `p` because the LP side evaluates it at arbitrary
points. -/
noncomputable def literalProb (p : ℕ → ℝ) (l : ℕ × Bool) : ℝ := if l.2 then p l.1 else 1 - p l.1

/-- **Satisfaction probability of a clause.** For probabilities `0 ≤ p i ≤ 1` and a clause `C`
whose literals use distinct variables, `1 - ∏_l (1 - P[l true])`, the probability that `C` is
satisfied when each variable `i` is set true independently with probability `p i` (Goemans and
Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2; proved in
`clauseSatProb_eq_sum_assignments`). The hypotheses restrict the closed form to its domain: for
`p i` outside `[0, 1]` or a clause repeating a variable it is not the satisfaction
probability. -/
noncomputable def clauseSatProb (p : ℕ → ℝ) (_hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (C : CNFClause)
    (_hC : (C.map Prod.fst).Nodup) : ℝ :=
  1 - (C.map fun l => 1 - literalProb p l).prod

/-- **Left-hand side of the clause constraint of the MAX SAT relaxation.**
`∑_{i ∈ P_j} y_i + ∑_{i ∈ N_j} (1 - y_i)` (Goemans and Williamson, *SIAM J. Discrete Math.*
7(4) (1994), §3, constraint of (IP) and (LP)), the sum over the literals of the clause; for a
clause with distinct variables this is the paper's sum over the sets `P_j` and `N_j`. -/
noncomputable def lpClauseBound (y : ℕ → ℝ) (C : CNFClause) : ℝ := (C.map (literalProb y)).sum

/-- **The randomized-rounding factor.** `β_k = 1 - (1 - 1/k)^k` (Goemans and Williamson,
*SIAM J. Discrete Math.* 7(4) (1994), Lemma 3.1). -/
noncomputable def roundingFactor (k : ℕ) : ℝ := 1 - (1 - 1 / (k : ℝ)) ^ k

open Classical in
/-- **The closed form is the satisfaction probability.** Let `C` be a clause whose literals use
distinct variables, with variable set `V = {l.1 : l ∈ C}`, and set each variable `i ∈ V` true
independently with probability `p i ∈ [0, 1]`, so that an assignment `a : V → Bool` has
probability
`∏_{i ∈ V} P[a i]`, `P[true] = p i`, `P[false] = 1 - p i`. Then `clauseSatProb p C` is the total
probability of the assignments that satisfy `C` (Goemans and Williamson, *SIAM J. Discrete
Math.* 7(4) (1994), §2): because the literals use distinct variables, exactly one assignment
falsifies `C`, the one making every literal false, and its probability is
`∏_l (1 - P[l true])`. -/
theorem clauseSatProb_eq_sum_assignments (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {C : CNFClause} (hC : (C.map Prod.fst).Nodup) :
    clauseSatProb p hp C hC = ∑ a : (C.map Prod.fst).toFinset → Bool,
      (∏ i, if a i then p i else 1 - p i) *
        if CNFClause.Satisfies
            (fun n => if h : n ∈ (C.map Prod.fst).toFinset then a ⟨n, h⟩ else false) C
        then 1 else 0 := by
  set V := (C.map Prod.fst).toFinset
  have hmemV : ∀ l ∈ C, l.1 ∈ V := fun l hl =>
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩)
  -- the literal of each variable, unique because the variables are distinct
  have hlit : ∀ i : V, ∃ l ∈ C, l.1 = i := fun i => by
    obtain ⟨l, hl, h⟩ := List.mem_map.mp (List.mem_toFinset.mp i.2)
    exact ⟨l, hl, h⟩
  choose lit hlitC hlit1 using hlit
  have huniq : ∀ l ∈ C, ∀ l' ∈ C, l.1 = l'.1 → l = l' := fun l hl l' hl' h =>
    List.inj_on_of_nodup_map hC hl hl' h
  have hlit_eq : ∀ l (hl : l ∈ C), lit ⟨l.1, hmemV l hl⟩ = l := fun l hl =>
    huniq _ (hlitC _) _ hl (hlit1 _)
  -- the only falsifying assignment
  set a₀ : V → Bool := fun i => !(lit i).2 with ha₀
  have hsat : ∀ a : V → Bool,
      CNFClause.Satisfies (fun n => if h : n ∈ V then a ⟨n, h⟩ else false) C ↔ a ≠ a₀ := by
    intro a
    rw [CNFClause.satisfies_def]
    constructor
    · rintro ⟨l, hl, hal⟩ rfl
      rw [dite_eq_left (hmemV l hl)] at hal
      simp [ha₀, hlit_eq l hl] at hal
    · intro hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      refine ⟨lit i, hlitC i, ?_⟩
      have hi' : (⟨(lit i).1, hmemV _ (hlitC i)⟩ : V) = i := Subtype.ext (hlit1 i)
      rw [dite_eq_left (hmemV _ (hlitC i)), hi']
      simpa [ha₀] using hi
  -- the probabilities of all assignments add up to `1`
  have htot : ∑ a : V → Bool, (∏ i, if a i then p i else 1 - p i) = 1 := by
    rw [← Fintype.prod_sum (fun (i : V) (b : Bool) => if b then p i else 1 - p i)]
    simp
  -- the probability of the falsifying assignment
  have hw₀ : (∏ i, if a₀ i then p i else 1 - p i) = (C.map fun l => 1 - literalProb p l).prod := by
    rw [← List.prod_toFinset _ (List.Nodup.of_map _ hC)]
    refine Finset.prod_bij (fun i _ => lit i) (fun i _ => List.mem_toFinset.mpr (hlitC i))
      (fun i _ j _ h => Subtype.ext ((hlit1 i).symm.trans ((congrArg Prod.fst h).trans (hlit1 j))))
      (fun l hl => ⟨⟨l.1, hmemV l (List.mem_toFinset.mp hl)⟩, Finset.mem_univ _,
        hlit_eq l (List.mem_toFinset.mp hl)⟩) (fun i _ => ?_)
    simp only [ha₀, literalProb, hlit1]
    cases (lit i).2 <;> simp
  calc clauseSatProb p hp C hC
      = ∑ a : V → Bool, ((∏ i, if a i then p i else 1 - p i) -
          if a = a₀ then ∏ i, if a i then p i else 1 - p i else 0) := by
        rw [Finset.sum_sub_distrib, htot, Finset.sum_ite_eq' Finset.univ a₀, ite_eq_left
          (Finset.mem_univ _), hw₀]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : a = a₀
        · rw [ite_eq_left h, ite_eq_right ((hsat a).not.mpr (not_not.mpr h))]
          ring
        · rw [ite_eq_right h, ite_eq_left ((hsat a).mpr h)]
          ring

private theorem prod_map_const (C : CNFClause) (c : ℝ) :
    (C.map fun _ => c).prod = c ^ C.length := by
  induction C with
  | nil => simp
  | cons a C ih => simp [pow_succ, mul_comm]

/-- **Johnson's probabilities are probabilities.** `p_i = 1/2` lies in `[0, 1]` for every
variable `i`. -/
theorem half_mem_Icc : ∀ _i : ℕ, (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 := fun _ => by norm_num

/-- **Johnson's random assignment.** With every variable true with probability `1/2`, a clause
with `k` literals on distinct variables is satisfied with probability `1 - 2^{-k}` (Goemans and
Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2). -/
theorem clauseSatProb_half (C : CNFClause) (hC : (C.map Prod.fst).Nodup) :
    clauseSatProb (fun _ => 1 / 2) half_mem_Icc C hC = 1 - (1 / 2 : ℝ) ^ C.length := by
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

/-- **Goemans–Williamson Lemma 3.1.** Let `C` be a clause with `k` literals on distinct
variables, `0 ≤ y_i ≤ 1` for every variable, and
`0 ≤ z ≤ min(1, ∑_{i ∈ P} y_i + ∑_{i ∈ N} (1 - y_i))`. Then randomized rounding `p_i = y_i`
satisfies `C` with probability at least `β_k z`, `β_k = 1 - (1 - 1/k)^k` (Goemans and
Williamson, *SIAM J. Discrete Math.* 7(4) (1994), Lemma 3.1, proved as there by the
arithmetic–geometric mean inequality and concavity). -/
theorem roundingFactor_mul_le_clauseSatProb {y : ℕ → ℝ} {C : CNFClause} {z : ℝ}
    (hC : (C.map Prod.fst).Nodup) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (hz : z ≤ lpClauseBound y C) :
    roundingFactor C.length * z ≤ clauseSatProb y hy C hC := by
  rcases Nat.eq_zero_or_pos C.length with hk | hk
  · rw [List.length_eq_zero_iff] at hk
    subst hk
    simp [roundingFactor, clauseSatProb]
  set k := C.length with hkdef
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  -- the literal values `a_l = 1 - P[l true]` lie in `[0, 1]`
  have hlit : ∀ l ∈ C, 0 ≤ literalProb y l ∧ literalProb y l ≤ 1 := by
    intro l hl
    obtain ⟨h0, h1⟩ := hy l.1
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

/-- **Goemans–Williamson Theorem 4.1, per clause.** For a clause `C` on distinct variables,
`0 ≤ y ≤ 1`, and `0 ≤ z ≤ min(1, ∑_{i ∈ P} y_i + ∑_{i ∈ N} (1 - y_i))`, the
average of the probabilities that Johnson's assignment and randomized rounding satisfy `C` is at
least `(3/4) z` (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), proof of
Theorem 4.1). -/
theorem three_quarters_mul_le_average {y : ℕ → ℝ} {C : CNFClause} {z : ℝ}
    (hC : (C.map Prod.fst).Nodup) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) (hz : z ≤ lpClauseBound y C) :
    (3 / 4 : ℝ) * z ≤
      (clauseSatProb (fun _ => 1 / 2) half_mem_Icc C hC + clauseSatProb y hy C hC) / 2 := by
  have hr := roundingFactor_mul_le_clauseSatProb hC hy hz0 hz1 hz
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

/-- **Expected weight of a randomized assignment.** For clauses `C j` on distinct variables
and probabilities `0 ≤ p i ≤ 1`, `∑_j w_j · clauseSatProb p (C j)`, the expected satisfied
weight when variable `i` is true independently with probability `p i`, by linearity of
expectation (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), §2). -/
noncomputable def expectedWeight {m : ℕ} (w : Fin m → ℝ) (C : Fin m → CNFClause)
    (hC : ∀ j, ((C j).map Prod.fst).Nodup) (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : ℝ :=
  ∑ j, w j * clauseSatProb p hp (C j) (hC j)

/-- **Goemans–Williamson Theorem 4.1.** For clauses on distinct variables, nonnegative weights
and a feasible solution `(y, z)` of (LP), let `Ŵ₁` be the expected satisfied weight under
`p_i = 1/2` and `Ŵ₂` under `p_i = y_i`. Then `max(Ŵ₁, Ŵ₂) ≥ (Ŵ₁ + Ŵ₂) / 2 ≥ (3/4) ∑_j w_j z_j`
(Goemans and Williamson, *SIAM J. Discrete Math.* 7(4) (1994), Theorem 4.1, stated there for an
optimal `(y, z)`; the proof uses only feasibility). -/
theorem three_quarters_le_max_expectedWeight {m : ℕ} {w : Fin m → ℝ} {C : Fin m → CNFClause}
    {y : ℕ → ℝ} {z : Fin m → ℝ} (hC : ∀ j, ((C j).map Prod.fst).Nodup) (hw : ∀ j, 0 ≤ w j)
    (hf : LPFeasible C y z) :
    (3 / 4 : ℝ) * ∑ j, w j * z j ≤
        (expectedWeight w C hC (fun _ => 1 / 2) half_mem_Icc + expectedWeight w C hC y hf.1) / 2 ∧
      (expectedWeight w C hC (fun _ => 1 / 2) half_mem_Icc + expectedWeight w C hC y hf.1) / 2 ≤
        max (expectedWeight w C hC (fun _ => 1 / 2) half_mem_Icc)
          (expectedWeight w C hC y hf.1) := by
  refine ⟨?_, by
    rcases le_total (expectedWeight w C hC (fun _ => 1 / 2) half_mem_Icc)
        (expectedWeight w C hC y hf.1) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith⟩
  unfold expectedWeight
  rw [mul_sum, ← sum_add_distrib, sum_div]
  refine sum_le_sum fun j _ => ?_
  obtain ⟨hz0, hz1, hz⟩ := hf.2 j
  have h := three_quarters_mul_le_average (hC j) hf.1 hz0 hz1 hz
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

/-- **The 3/4 guarantee against the MAX SAT optimum.** For clauses on distinct variables and
nonnegative weights, if `(y, z)` is an optimal solution of (LP), then for every truth assignment
`a`, `max(Ŵ₁, Ŵ₂) ≥ (3/4) · (weight satisfied by a)`, where `Ŵ₁` and `Ŵ₂` are the expected
satisfied weights of Johnson's assignment and of randomized rounding: the better of the two is
a `3/4`-approximation in expectation (Goemans and Williamson, *SIAM J. Discrete Math.* 7(4)
(1994), Theorem 4.1 with `Z*_LP ≥ Z*_IP`). Clauses that repeat a variable are excluded: for the
single clause `x₀ ∨ x₀`, the closed forms would be `3/4` while both roundings satisfy it with
probability `1/2`. -/
theorem three_quarters_le_max_expectedWeight_of_optimal {m : ℕ} {w : Fin m → ℝ}
    {C : Fin m → CNFClause} {y : ℕ → ℝ} {z : Fin m → ℝ} (hC : ∀ j, ((C j).map Prod.fst).Nodup)
    (hw : ∀ j, 0 ≤ w j) (hf : LPFeasible C y z)
    (hopt : ∀ y' z', LPFeasible C y' z' → ∑ j, w j * z' j ≤ ∑ j, w j * z j) (a : ℕ → Bool) :
    (3 / 4 : ℝ) * satisfiedWeight w C a ≤
      max (expectedWeight w C hC (fun _ => 1 / 2) half_mem_Icc) (expectedWeight w C hC y hf.1) := by
  obtain ⟨y', z', hf', hval⟩ := lpFeasible_of_assignment w C a
  have h1 := hopt y' z' hf'
  rw [hval] at h1
  obtain ⟨h2, h3⟩ := three_quarters_le_max_expectedWeight hC hw hf
  linarith

end CSLibExt.Algorithms.Approximation.MaxSat
