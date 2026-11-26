/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSymmetricFunctions

/-!
# Alternating blocks obstruct sum-plus-product vanishing

The alternating sequence of `1` and `-1` has no vanishing block for the sum-plus-product family
when the coefficient is neither zero nor a sign.

## References

* Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem to Some
  Symmetric Functions*, INTEGERS 26 (2026), Article A25, pp. 1–12, Theorem 2 (§2),
  gives the alternating-sequence argument.
* Arie Bialostocki and Paul Dierker, *Zero Sum Ramsey Theorems*, Congressus Numerantium 70
  (1990), pp. 119–130, §3, is cited there for the earlier symmetric-polynomial problem.
-/

namespace MetaMathlibExt

private def alternatingSign {n : ℕ} (s : ℕ) : ZMod n :=
  if s % 2 = 0 then 1 else -1

private theorem alternatingSign_pair {n : ℕ} (s : ℕ) :
    alternatingSign (n := n) s + alternatingSign (s + 1) = 0 ∧
      alternatingSign (n := n) s * alternatingSign (s + 1) = -1 := by
  by_cases h : s % 2 = 0
  · have h' : (s + 1) % 2 ≠ 0 := by omega
    simp [alternatingSign, h, h']
  · have h' : (s + 1) % 2 = 0 := by omega
    simp [alternatingSign, h, h']

private theorem alternatingBlock_sum_prod {n : ℕ} (s l : ℕ) :
    let b : Fin l → ZMod n := fun i => alternatingSign (s + i)
    ((∑ i, b i) = 0 ∨ (∑ i, b i) = 1 ∨ (∑ i, b i) = -1) ∧
      ((∏ i, b i) = 1 ∨ (∏ i, b i) = -1) := by
  induction l using Nat.twoStepInduction with
  | zero => simp
  | one =>
    by_cases hs : s % 2 = 0 <;> simp [alternatingSign, hs]
  | more l ih _ =>
    dsimp only at ih ⊢
    have hpair := alternatingSign_pair (n := n) (s + l)
    have hsum : (∑ i : Fin (l + 2), alternatingSign (n := n) (s + i)) =
        ∑ i : Fin l, alternatingSign (s + i) := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [add_assoc, ← Nat.add_assoc s l 1, hpair.1, add_zero]
    have hprod : (∏ i : Fin (l + 2), alternatingSign (n := n) (s + i)) =
        -(∏ i : Fin l, alternatingSign (s + i)) := by
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [mul_assoc, ← Nat.add_assoc s l 1, hpair.2, mul_neg, mul_one]
    rw [hsum, hprod]
    refine ⟨ih.1, ?_⟩
    rcases ih.2 with h | h
    · exact Or.inr (congrArg Neg.neg h)
    · exact Or.inl (by rw [h, neg_neg])

-- The argument does not need `hn`, but the statement retains the source's hypothesis.
set_option linter.unusedVariables false in
/-- **$F_c$ with $c \notin \{0, \pm 1\}$ is not $m$-vanishing for $m > 0$.** Let $n > 1$ and let
$c \in \mathbb{Z}/n$ with $c \ne 0$, $c \ne 1$ and $c \ne -1$. Then for every $m > 0$ the
sum-plus-product family $F_c$ over $\mathbb{Z}/n$,
$F_c(b_1, \dots, b_l) = b_1 + \dots + b_l + c\, b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 2
(`integers-2026-A25-thm-2`). -/
public theorem not_isMVanishingFamily_sumAddMulProd_of_ne {n : ℕ} (hn : 1 < n)
    (c : ZMod n) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcm1 : c ≠ -1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily c) := by
  intro h
  obtain ⟨l, -, s, hs⟩ := h.mono (m' := 1) hm (alternatingSign (n := n))
  have hzero := hs 0 Nat.zero_lt_one
  simp only [zero_mul, Nat.add_zero, sumAddMulProdFamily] at hzero
  obtain ⟨hsum, hprod⟩ := alternatingBlock_sum_prod (n := n) s l
  rw [add_comm, add_eq_zero_iff_eq_neg] at hzero
  have hc : c = -(∑ i : Fin l, alternatingSign (s + i)) ∨
      c = ∑ i : Fin l, alternatingSign (s + i) := by
    rcases hprod with hprod | hprod
    · exact Or.inl (by simpa only [hprod, mul_one] using hzero)
    · exact Or.inr (by simpa only [hprod, mul_neg, mul_one, neg_inj] using hzero)
  rcases hsum with hsum | hsum | hsum
  · simp [hsum, hc0] at hc
  · simp [hsum, hc1, hcm1] at hc
  · simp [hsum, hc1, hcm1] at hc

end MetaMathlibExt
