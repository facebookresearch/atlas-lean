/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Fin.Tuple
public import MathlibExt.Combinatorics.Additive.BoundedSubsequenceSums
public import MathlibExt.Combinatorics.Additive.YangChen

/-!
# Sharp lower bound for bounded subsequence sums of positive integers

Padding with zero gives the Yang–Chen lower bound. To obtain equality, translate the
extremizing generalized sumset so that its least term is zero.
-/

namespace MetaMathlibExt

private theorem card_generalizedHFoldSumset_sub_const {G : Type*} [AddCommGroup G] [DecidableEq G]
    {k : ℕ} (a : Fin k → G) (r : Fin k → ℕ) (h : ℕ) (c : G) :
    (generalizedHFoldSumset (fun i => a i - c) r h).card =
      (generalizedHFoldSumset a r h).card := by
  have htranslate : generalizedHFoldSumset (fun i => a i - c) r h =
      (generalizedHFoldSumset a r h).image (fun x => x - h • c) := by
    simp only [generalizedHFoldSumset, Finset.image_image]
    apply Finset.image_congr
    intro s hs
    -- Each admissible coefficient vector has the same total, so the shift is constant.
    have hlen : ∑ i, s i = h := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
    simp only [Function.comp_apply, nsmul_sub, Finset.sum_sub_distrib, Finset.sum_nsmul_assoc, hlen]
  rw [htranslate, Finset.card_image_of_injective _ sub_left_injective]

-- Keep the source's named hypothesis `hk`, although the reduction does not need it.
set_option linter.unusedVariables false in
/-- **Lower bound for bounded subsequence sums of a positive sequence.** Let $k \ge 2$, let
$t_1, \dots, t_k$ be positive integers, let $h = t_1 + \dots + t_k$, and let $\alpha, \beta$ be
natural numbers with $1 \le \alpha$ and $\alpha + \beta \le h - 1$. Put
$\bar r = (h - \alpha - \beta, t_1, \dots, t_k)$. For integers $0 < b_1 < \dots < b_k$, let
$\mathcal{A}$ be the sequence in which $b_i$ occurs $t_i$ times. Then
$|\Sigma^{\beta}_{\alpha}(\mathcal{A})| \ge L(\bar r, h - \beta)$ for all such $b$, and equality
holds for some such $b$. Here $\Sigma^{\beta}_{\alpha}(\mathcal{A})$ is the set of sums of
subsequences of $\mathcal{A}$ with at least $\alpha$ and at most $h - \beta$ terms, and $L$ is the
Yang–Chen bound.

Source: Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24
(2024), Article A116, Theorem 13 (`integers-2024-A116-thm-13`). -/
public theorem card_boundedSubsequenceSums_ge_of_pos {k : ℕ} (hk : 2 ≤ k)
    (t : Fin k → ℕ) (ht : ∀ i, 0 < t i) (h : ℕ) (hh : h = ∑ i, t i) (α β : ℕ) (hα : 1 ≤ α)
    (hαβ : α + β + 1 ≤ h) :
    (∀ b : Fin k → ℤ, StrictMono b → (∀ i, 0 < b i) →
      yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) ≤
        (boundedSubsequenceSums α β (repetitionSequence b t)).card) ∧
    ∃ b : Fin k → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
      ((boundedSubsequenceSums α β (repetitionSequence b t)).card : ℤ) =
        yangChenBound (Fin.cons (h - α - β) t : Fin (k + 1) → ℕ) (h - β) := by
  let r : Fin (k + 1) → ℕ := Fin.cons (h - α - β) t
  have hr (i : Fin (k + 1)) : 0 < r i :=
    Fin.cases (show 0 < h - α - β by omega) ht i
  have hcap : h - β ≤ ∑ i, r i := by
    simp only [r, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← hh]
    omega
  have hrewrite (b : Fin k → ℤ) (hb : StrictMono b) (hbpos : ∀ i, 0 < b i) :
      boundedSubsequenceSums α β (repetitionSequence b t) =
        generalizedHFoldSumset (Fin.cons 0 b) r (h - β) :=
    boundedSubsequenceSums_eq_generalizedHFoldSumset_of_zero_not_mem b hb.injective
      (fun i => (hbpos i).ne') t ht h hh α β hα hαβ
  obtain ⟨hlower, a, ha, heq⟩ :=
    yangChen_card_generalizedHFoldSumset_ge r hr (h - β) (by omega) hcap
  constructor
  · intro b hb hbpos
    rw [hrewrite b hb hbpos]
    exact hlower _ (Fin.strictMono_cons.2 ⟨hbpos, hb⟩)
  · let b (i : Fin k) : ℤ := a i.succ - a 0
    have hb : StrictMono b := fun _ _ hij => sub_lt_sub_right (ha (Fin.succ_lt_succ_iff.2 hij)) _
    have hbpos (i : Fin k) : 0 < b i := sub_pos.mpr (ha (Fin.succ_pos i))
    have hshift : (Fin.cons 0 b : Fin (k + 1) → ℤ) = fun i => a i - a 0 := by
      funext i
      refine Fin.cases ?_ (fun j => rfl) i
      simp
    refine ⟨b, hb, hbpos, ?_⟩
    rw [hrewrite b hb hbpos, hshift, card_generalizedHFoldSumset_sub_const]
    exact heq

end MetaMathlibExt
