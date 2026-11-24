/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive

/-! # Examples of reflexive weighted projective space simplices -/

open MetaMathlibExt

-- The vertex `-q` of `Δ_(1,q)` is a lattice point, and doubling it gives a lattice point of `2Δ`.
example : IsLatticePoint (weightedSimplex ![3, 10, 15]) ![-3, -10, -15] := by
  apply subset_convexHull
  right
  funext i
  fin_cases i <;> simp

example : IsLatticePoint (polytopeDilate 2 (weightedSimplex ![1])) ![-2] := by
  refine ⟨fun _ => -1, subset_convexHull ℝ _ (Or.inr ?_), ?_⟩
  · funext i
    simp
  · funext i
    fin_cases i
    norm_num

example (P : Set (Fin 2 → ℝ)) : polytopeDilate 1 P = P := polytopeDilate_one P

-- For `n = 1` and `n = 2` the theorem gives the first reflexive stabilizations of `(3, 10, 15)`
-- and `(6, 20, 30)`.
private theorem reflexiveStabilization_three_ten_fifteen_test :
    reflexiveStabilization [3, 10, 15] = [1, 3, 10, 15] := by
  rw [← almostIDPWeights_eq_reflexiveStabilization 1 le_rfl]
  decide

example : reflexiveStabilization [6, 20, 30] = [1, 1, 1, 6, 20, 30] := by
  rw [← almostIDPWeights_eq_reflexiveStabilization 2 (by norm_num)]
  decide

-- The reflexive stabilization number of `(3, 10, 15)` is `1`, so `Δ_(1,(1,3,10,15))` is
-- reflexive and `Δ_(1,(3,10,15))` is not.
private theorem reflexiveStabilizationNumber_three_ten_fifteen_test :
    reflexiveStabilizationNumber [3, 10, 15] = 1 := by
  have h := congrArg List.length (almostIDPWeights_eq_reflexiveStabilization 1 le_rfl)
  simp only [List.length_ofFn, reflexiveStabilization, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil, Nat.mul_one] at h
  omega

private theorem isReflexive_one_three_ten_fifteen_test :
    IsReflexive (weightedSimplexList [1, 3, 10, 15]) := by
  have h1 := reflexiveStabilizationNumber_three_ten_fifteen_test
  have hne : {k : ℕ | IsReflexive
      (weightedSimplexList (List.replicate k 1 ++ [3, 10, 15]))}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [reflexiveStabilizationNumber, h, Nat.sInf_empty] at h1
    exact zero_ne_one h1
  have hmem := Nat.sInf_mem hne
  rw [← reflexiveStabilizationNumber, h1] at hmem
  exact hmem

example : ¬ IsReflexive (weightedSimplexList [3, 10, 15]) := by
  intro h
  have h0 : reflexiveStabilizationNumber [3, 10, 15] = 0 :=
    Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using h))
  rw [reflexiveStabilizationNumber_three_ten_fifteen_test] at h0
  exact one_ne_zero h0

-- The weighted free sum of `(1, 3, 10, 15)` with itself: the second copy is scaled by
-- `1 + (1 + 3 + 10 + 15) = 30`, so the weights `(1, 3, 10, 15, 30, 90, 300, 450)` give a reflexive
-- simplex.
example : IsReflexive (weightedSimplexList [1, 3, 10, 15, 30, 90, 300, 450]) :=
  weighted_free_sum_reflexive [1, 3, 10, 15] [1, 3, 10, 15] (by decide) (by decide)
    isReflexive_one_three_ten_fifteen_test isReflexive_one_three_ten_fifteen_test

-- The least common multiple of a weight list, with `lcm() = 1`, and the integer `ℓ`, which is `0`
-- when a weight is `0`.
example : weightLcm [2, 2, 3] = 6 := by
  decide

example : weightLcm [] = 1 := rfl

example : listEll [1, 3, 10, 15] = 1 := by
  decide

example : listEll [4, 0, 6] = 0 := by
  decide

-- For `q = (2, 2, 3)`, the weight statistic `w(q, b) = b - 2⌊2b/8⌋ - ⌊3b/8⌋` for `b = 0, …, 7`.
example : (List.range 8).map (weightStatistic [2, 2, 3]) = [0, 1, 2, 2, 1, 2, 2, 3] := by
  decide

-- For `q = (3, 10, 15)`, `rsn(q) = 1`, `rs(q) = (1, 3, 10, 15)` and `ℓ(rs(q)) = 30 / 30 = 1`, so
-- the first reflexive stabilization preserves the weight statistic up to `b = 3 + 10 + 15 = 28`.
example (b : ℕ) (hb : b ≤ 28) :
    weightStatistic [3, 10, 15] b = weightStatistic [1, 3, 10, 15] b := by
  have h := stabilization_weightStatistic_eq [3, 10, 15]
    reflexiveStabilizationNumber_three_ten_fifteen_test
    (by rw [reflexiveStabilization_three_ten_fifteen_test]; decide) b hb
  rwa [reflexiveStabilization_three_ten_fifteen_test] at h

-- The bound `b ≤ ∑ q` is needed: at `b = 29` the two weight statistics are `1` and `4`.
example : weightStatistic [3, 10, 15] 29 = 1 ∧ weightStatistic [1, 3, 10, 15] 29 = 4 := by
  decide

-- The hypothesis `1 ≤ n` is needed: for `n = 0` the weight vector is `(0, 0)`, which is too short
-- to be a stabilization of `(0, 0, 0)`.
example : List.ofFn (almostIDPWeights 0) = [0, 0] := by
  decide

example : List.ofFn (almostIDPWeights 0) ≠ reflexiveStabilization [3 * 0, 10 * 0, 15 * 0] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_ofFn, reflexiveStabilization, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] at this
  omega

-- The expansion `(r_1^{x_1}, …, r_d^{x_d})` lists `x_i` copies of each `r_i`, in order; a value
-- with multiplicity `0` does not occur.
example : expandSupport ![2, 5, 7] ![1, 0, 2] = [2, 7, 7] := by
  decide

-- Valid support data needs distinct support values and positive multiplicities.
private theorem validSupport_one_three_ten_fifteen_test :
    ValidSupport ![1, 3, 10, 15] ![1, 1, 1, 1] := by
  unfold ValidSupport
  decide

example : ¬ ValidSupport ![2, 2] ![1, 1] := by
  unfold ValidSupport
  decide

example : ¬ ValidSupport ![1, 3] ![1, 0] := by
  unfold ValidSupport
  decide

-- The complementary factors `s_i = lcm(r) / r_i` of `r = (1, 3, 10, 15)` are `(30, 10, 3, 2)`;
-- they are all `0` when some `r_i = 0`, since then `lcm(r) = 0`.
example : List.ofFn (setupS ![1, 3, 10, 15]) = [30, 10, 3, 2] := by
  decide

example : List.ofFn (setupS ![0, 3]) = [0, 0] := by
  decide

-- For the reflexive weights `(1, 3, 10, 15)` the theorem gives `gcd(1, 3, 10, 15) = 1` and
-- `lcm(30, 10, 3, 2) = lcm(1, 3, 10, 15) = 30`.
example : Finset.univ.gcd ![1, 3, 10, 15] = 1 ∧
    Finset.univ.lcm (setupS ![1, 3, 10, 15]) = weightLcm (List.ofFn ![1, 3, 10, 15]) := by
  have hexp : expandSupport ![1, 3, 10, 15] ![1, 1, 1, 1] = [1, 3, 10, 15] := by
    decide
  refine support_gcd_and_complementary_lcm ![1, 3, 10, 15] ![1, 1, 1, 1]
    validSupport_one_three_ten_fifteen_test ?_
  rw [hexp]
  exact isReflexive_one_three_ten_fifteen_test

-- For `r = (2, 4)` both conclusions fail: `gcd(2, 4) = 2`, and `lcm(4/2, 4/4) = 2 ≠ 4`. So the
-- theorem shows that the simplex of the weights `(2, 4)` is not reflexive.
example : Finset.univ.gcd ![2, 4] = 2 ∧ Finset.univ.lcm (setupS ![2, 4]) = 2 ∧
    weightLcm (List.ofFn ![2, 4]) = 4 := by
  decide

example : ¬ IsReflexive (weightedSimplexList [2, 4]) := by
  intro h
  have hexp : expandSupport ![2, 4] ![1, 1] = [2, 4] := by
    decide
  have hgcd := (support_gcd_and_complementary_lcm ![2, 4] ![1, 1]
    (by unfold ValidSupport; decide) (by rw [hexp]; exact h)).1
  exact absurd hgcd (by decide)

-- The hypothesis `0 < d` is needed: with `d = 0` the expansion is empty, the simplex of the empty
-- weight list is the whole space `ℝ⁰` and is reflexive, but the gcd of the empty family is `0`.
private theorem isReflexive_nil_test : IsReflexive (weightedSimplexList []) := by
  have hsub : ∀ p z : Fin ([] : List ℕ).length → ℝ, p = z := fun _ _ => funext fun i => i.elim0
  have huniv : ∀ S : Set (Fin ([] : List ℕ).length → ℝ), S.Nonempty → S = Set.univ :=
    fun S ⟨p, hp⟩ => Set.eq_univ_of_forall fun z => hsub p z ▸ hp
  have hP : weightedSimplexList [] = Set.univ :=
    huniv _ ⟨_, subset_convexHull ℝ _ (Or.inr rfl)⟩
  have hD : ∀ t, polytopeDilate t (weightedSimplexList []) = Set.univ := fun t =>
    huniv _ ⟨_, 0, hP ▸ Set.mem_univ 0, rfl⟩
  refine ⟨0, ?_, fun t _ x => ?_⟩
  · simp [IsLatticePoint, hP]
  · simp only [IsLatticePoint, hD, interior_univ, Set.mem_univ, true_and, true_iff]
    exact ⟨0, funext fun i => i.elim0⟩

example : IsReflexive (weightedSimplexList (expandSupport (![] : Fin 0 → ℕ) ![])) ∧
    Finset.univ.gcd (![] : Fin 0 → ℕ) = 0 :=
  ⟨isReflexive_nil_test, rfl⟩

-- A singleton lattice polytope has IDP in every positive dilate.
example (v : Fin 2 → ℤ) : HasIDP ({fun i => (v i : ℝ)} : Set (Fin 2 → ℝ)) := by
  intro m _ w hw
  obtain ⟨z, hz, heq⟩ := hw
  obtain rfl := Set.mem_singleton_iff.mp hz
  refine ⟨fun _ => v, fun _ => Set.mem_singleton _, fun i => ?_⟩
  have hi : (w i : ℝ) = m * (v i : ℝ) := congrFun heq i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact_mod_cast hi.symm

-- Three copies of 1 contribute 3 to the remainder sum modulo 2. The required equation
-- would be 4 = 2, even when the larger support value is listed first.
example : ¬ (IsReflexive (weightedSimplexList [2, 1, 1, 1]) ∧
    HasIDP (weightedSimplexList [2, 1, 1, 1])) := by
  rintro ⟨href, hidp⟩
  have hexp : expandSupport ![2, 1] ![1, 3] = [2, 1, 1, 1] := by decide
  have h := idp_reflexive_implies_support_necessary ![2, 1] ![1, 3]
    (by unfold ValidSupport; decide) (hexp ▸ href) (hexp ▸ hidp) 0
  exact absurd h (by decide)
