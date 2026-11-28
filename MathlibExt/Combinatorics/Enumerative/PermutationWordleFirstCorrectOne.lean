/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination

/-!
# Three-guess permutation Wordle solves with a fixed point

For $n \ge 4$, if the strategy uses cyclic shift on every set of fewer than $n$ incorrect
positions, the number of permutations solved in exactly three guesses with a correct entry
in the first guess can be computed by summing the three-guess derangement count over proper
supports. This works for any component on $n$ positions, since a first-guess match stays locked.

## References

* Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
  (2026), Article 26.1.7, pp. 1–16, Lemma 9 and Theorem 10. The proof uses the support
  reduction of Theorem 10 and the formalization of Lemma 9 in
  `MathlibExt.Combinatorics.Enumerative.PermutationWordleDerangements`
  (`MetaMathlibExt.card_derangements_solvedIn_three_cyclicShift`).
* Samuel Kutin and Lawren Smithline, *Permutation Wordle*, arXiv:2408.00903v3 (2026),
  Lemma 3.4. Hiveley cites their characterization by excedances; the proof here uses the
  three-guess derangement count directly.
-/

namespace MetaMathlibExt

open Finset

private noncomputable def fixedSupportEquiv {n : ℕ} (I : Finset (Fin n))
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ m ≤ I.card, S m = cyclicShiftStrategy m) :
    {δ : Equiv.Perm (Fin I.card) // (∀ i, δ i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy δ 3} ≃
      {π : Equiv.Perm (Fin n) // π.support = I ∧ PermWordleSolvedIn S π 3} := by
  classical
  let e := (I.orderIsoOfFin rfl).toEquiv
  have hsupport (δ : Equiv.Perm (Fin I.card)) :
      (δ.extendDomain e).support = I ↔ ∀ i, δ i ≠ i := by
    rw [Equiv.Perm.support_extend_domain]
    constructor
    · intro h i
      have hi : (e i).val ∈ δ.support.map e.asEmbedding := h.symm ▸ (e i).property
      obtain ⟨j, hj, hji⟩ := mem_map.mp hi
      have : j = i := e.injective (Subtype.ext hji)
      exact Equiv.Perm.mem_support.mp (this ▸ hj)
    · intro h
      have hfull : δ.support = univ := eq_univ_of_forall fun i => Equiv.Perm.mem_support.mpr (h i)
      rw [hfull]
      exact I.map_orderEmbOfFin_univ rfl
  let extend (δ : {δ : Equiv.Perm (Fin I.card) //
      (∀ i, δ i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy δ 3}) :
      {π : Equiv.Perm (Fin n) // π.support = I ∧ PermWordleSolvedIn S π 3} :=
    ⟨δ.val.extendDomain e, (hsupport _).mpr δ.property.1,
      (permWordleSolvedIn_extendDomain_iff I S cyclicShiftStrategy hS _ _).mpr δ.property.2⟩
  refine Equiv.ofBijective extend ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have hi := Equiv.congr_fun (congrArg Subtype.val h) (e i).val
    change a.val.extendDomain e (e i).val = b.val.extendDomain e (e i).val at hi
    rw [Equiv.Perm.extendDomain_apply_image, Equiv.Perm.extendDomain_apply_image] at hi
    exact e.injective (Subtype.ext hi)
  · rintro ⟨π, hI, hsol⟩
    obtain ⟨u, hu⟩ : π ∈ (Equiv.Perm.ofSubtype : Equiv.Perm I →* Equiv.Perm (Fin n)).range :=
      Equiv.Perm.mem_range_ofSubtype_iff.mpr (by simp [hI])
    let δ := e.permCongr.symm u
    have he : δ.extendDomain e = π := by
      change Equiv.Perm.ofSubtype (e.permCongr δ) = π
      rw [e.permCongr.apply_symm_apply]
      exact hu
    exact ⟨⟨δ, (hsupport δ).mp (he ▸ hI),
      (permWordleSolvedIn_extendDomain_iff I S cyclicShiftStrategy hS _ _).mp (he ▸ hsol)⟩,
      Subtype.ext he⟩

private theorem no_small_derangement_solve {k : ℕ} (hk : k < 3)
    (δ : Equiv.Perm (Fin k)) (hδ : ∀ i, δ i ≠ i) :
    ¬ PermWordleSolvedIn cyclicShiftStrategy δ 3 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · intro h
    exact ((permWordleSolvedIn_succ_succ_iff _ _ 1).mp h).2 (Subsingleton.elim ..)
  · exact (hδ 0 (Subsingleton.elim ..)).elim
  · rw [permWordleSolvedIn_succ_succ_iff _ _ 1,
      permWordleGuess_one_of_forall_ne _ _ hδ, cyclicShiftStrategy_apply]
    have unique (a b c : Fin 2) : a ≠ c → b ≠ c → a = b := by decide +revert
    have moved (i : Fin 2) : (finRotate 2).symm i ≠ i := by decide +revert
    exact fun h => h.2 (funext fun i => unique _ _ _ (moved i) (hδ i))

private def weight (n k : ℕ) : ℕ := if 3 ≤ k ∧ k < n then 2 ^ k - (2 * k + 1) else 0

private theorem card_secrets_by_support {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))
    (hS : ∀ m < n, S m = finRotate m) :
    Nat.card {π : Equiv.Perm (Fin n) //
      PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1} =
        ∑ I : Finset (Fin n), weight n I.card := by
  classical
  let C := {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1}
  let supp (π : C) := π.val.support
  have proper (π : C) : (supp π).card < n := by
    obtain ⟨i, hi⟩ := (permWordleFirstCorrectAt_one_iff S π.val).mp π.property.2
    apply (card_lt_card (ssubset_univ_iff.mpr ?_)).trans_eq (by simp)
    intro he
    have hm : i ∈ supp π := he.symm ▸ mem_univ i
    exact Equiv.Perm.mem_support.mp hm hi
  calc
    Nat.card C = ∑ I, Nat.card {π : C // supp π = I} := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr (Equiv.sigmaFiberEquiv supp).symm
    _ = _ := by
      apply sum_congr rfl
      intro I _
      by_cases hn : I.card < n
      · have hST (m : ℕ) (hm : m ≤ I.card) : S m = cyclicShiftStrategy m := by
          rw [cyclicShiftStrategy_apply, hS m (hm.trans_lt hn)]
        have hI : I ≠ univ := by
          intro he
          simp [he] at hn
        have fixed (π : Equiv.Perm (Fin n)) (h : π.support = I) :
            PermWordleFirstCorrectAt S π 1 := by
          obtain ⟨i, hi⟩ := not_forall.mp (mt eq_univ_of_forall hI)
          exact (permWordleFirstCorrectAt_one_iff S π).mpr
            ⟨i, Equiv.Perm.notMem_support.mp (h.symm ▸ hi)⟩
        let e : {π : C // supp π = I} ≃
            {π : Equiv.Perm (Fin n) // π.support = I ∧ PermWordleSolvedIn S π 3} :=
          { toFun := fun π => ⟨π.val.val, π.property, π.val.property.1⟩
            invFun := fun π => ⟨⟨π.val, π.property.2, fixed π.val π.property.1⟩, π.property.1⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr (e.trans (fixedSupportEquiv I S hST).symm)]
        by_cases h : 3 ≤ I.card
        · rw [weight, ite_eq_left (show 3 ≤ I.card ∧ I.card < n from ⟨h, hn⟩)]
          exact card_derangements_solvedIn_three_cyclicShift I.card h
        · let : IsEmpty {δ : Equiv.Perm (Fin I.card) //
                (∀ i, δ i ≠ i) ∧ PermWordleSolvedIn cyclicShiftStrategy δ 3} :=
              ⟨fun δ => no_small_derangement_solve (by omega) δ.val δ.property.1 δ.property.2⟩
          simp [weight, h]
      · let : IsEmpty {π : C // supp π = I} := ⟨fun π => hn (π.property ▸ proper π.val)⟩
        simp [weight, hn]

private theorem sum_weight_by_card (n : ℕ) :
    (∑ I : Finset (Fin n), (weight n I.card : ℚ)) =
      ∑ k ∈ range n, (n.choose k : ℚ) * weight n k := by
  have hTo (I : Finset (Fin n)) (_ : I ∈ univ) : I.card ∈ range (n + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (card_finset_fin_le I))
  rw [← sum_fiberwise_of_maps_to' hTo (fun k => (weight n k : ℚ))]
  simp_rw [sum_const, nsmul_eq_mul]
  have hf (k : ℕ) : (univ.filter fun I : Finset (Fin n) => I.card = k).card = n.choose k := by
    rw [← Fintype.card_of_subtype _ (p := fun I : Finset (Fin n) => I.card = k) (by simp),
      Fintype.card_finset_len, Fintype.card_fin]
  simp only [hf, sum_range_succ, weight, lt_irrefl, and_false, ite_false, Nat.cast_zero,
    mul_zero, add_zero]

private theorem closedForm (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ range n, (n.choose k : ℚ) * weight n k) =
      1 - 2 ^ (n + 1) + 3 ^ n + (n : ℚ) ^ 2 / 2 + 5 * (n : ℚ) / 2 - n * 2 ^ n := by
  let f (k : ℕ) : ℚ := 2 ^ k - (2 * k + 1)
  have hw (k : ℕ) (hk : 3 ≤ k) (hkn : k < n) : (weight n k : ℚ) = f k := by
    have hp : 2 * k + 1 ≤ 2 ^ k := by
      induction k, hk using Nat.le_induction with
      | base => decide
      | succ j hj ih => rw [pow_succ]; omega
    simp [weight, hk, hkn, f, Nat.cast_sub hp]
  have hpow : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * 2 ^ k) = 3 ^ n := by
    simpa [mul_comm, show (2 : ℚ) + 1 = 3 by norm_num] using (add_pow (2 : ℚ) 1 n).symm
  have hconst : (∑ k ∈ range (n + 1), (n.choose k : ℚ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have hlin : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * k) = n * (2 : ℚ) ^ (n - 1) := by
    have hnat : (∑ k ∈ range (n + 1), n.choose k * k) = n * 2 ^ (n - 1) := by
      simpa only [Nat.mul_comm _ (n.choose _)] using Nat.sum_range_mul_choose n
    exact_mod_cast hnat
  have htwo : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * k + 1)) = (n + 1 : ℚ) * 2 ^ n := by
    simp only [mul_add, mul_one, mul_left_comm (a := (_ : ℚ)) (b := (2 : ℚ)), sum_add_distrib,
      ← mul_sum, hlin, hconst]
    have h : n - 1 + 1 = n := by omega
    rw [← h, pow_succ, h]
    ring
  have hall : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * f k) = 3 ^ n - (n + 1 : ℚ) * 2 ^ n := by
    simp only [f, mul_sub, sum_sub_distrib, hpow, htwo]
  have hsplit : (∑ k ∈ range (n + 1), (n.choose k : ℚ) * f k) =
      (∑ k ∈ range n, (n.choose k : ℚ) * weight n k) - n - (n.choose 2 : ℚ) + f n := by
    rw [sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul]
    congr 1
    calc
      _ = ∑ k ∈ range n, ((n.choose k : ℚ) * weight n k -
          (if k = 1 then n else 0) - (if k = 2 then (n.choose 2 : ℚ) else 0)) := by
        apply sum_congr rfl
        intro k hk
        by_cases h : 3 ≤ k
        · simp [← hw k h (mem_range.mp hk), show k ≠ 1 by omega, show k ≠ 2 by omega]
        · rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;>
            norm_num [f, weight, Nat.choose_one_right]
      _ = _ := by
        rw [sum_sub_distrib, sum_sub_distrib]
        simp [mem_range.mpr (by omega : 1 < n), mem_range.mpr (by omega : 2 < n)]
  have hchoose : (n.choose 2 : ℚ) = n * (n - 1) / 2 := by
    have h : (n - 1 + 1) * (n - 1).choose 1 = (n - 1 + 1).choose 2 * 2 :=
      Nat.add_one_mul_choose_eq (n - 1) 1
    have hn' : n - 1 + 1 = n := by omega
    rw [hn', Nat.choose_one_right] at h
    have hcast := congrArg (fun t : ℕ => (t : ℚ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at hcast
    linear_combination -hcast / 2
  rw [hsplit, hchoose] at hall
  dsimp [f] at hall
  rw [pow_succ]
  linear_combination hall

/-- **Three-guess solves of permutations with a fixed point.** Let $n \ge 4$ and let $S$ be a
permutation Wordle strategy (a permutation $S[m]$ of $\{0, \dots, m-1\}$ for each $m$) with
$S[m]$ equal to the cyclic shift $j \mapsto j + 1 \bmod m$ for every $m < n$. The number of
permutations $\pi$ of $\{0, \dots, n-1\}$ that $S$ guesses in exactly three guesses and whose
first guess (the identity) has a correct position, that is, $\pi$ has a fixed point, is
$1 - 2^{n+1} + 3^n + n^2/2 + 5n/2 - n \cdot 2^n$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 10 (`jis-2026-26.1.7-thm-10`). -/
public theorem card_solvedIn_three_firstCorrectAt_one (n : ℕ) (hn : 4 ≤ n)
    (S : (m : ℕ) → Equiv.Perm (Fin m)) (hS : ∀ m < n, S m = finRotate m) :
    (Nat.card {π : Equiv.Perm (Fin n) //
        PermWordleSolvedIn S π 3 ∧ PermWordleFirstCorrectAt S π 1} : ℚ) =
      1 - 2 ^ (n + 1) + 3 ^ n + (n : ℚ) ^ 2 / 2 + 5 * (n : ℚ) / 2 - n * 2 ^ n := by
  rw [card_secrets_by_support S hS, Nat.cast_sum, sum_weight_by_card]
  exact closedForm n hn

end MetaMathlibExt
