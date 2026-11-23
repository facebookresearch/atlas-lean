/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.Coding.UniquelyDecodable
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.InformationTheory.PrefixFree
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.InformationTheory.KraftMcMillan

@[expose] public section

section
open Real BigOperators Finset

namespace MathlibExt.InformationTheory.ShannonSourceCodingWanted

/-!
# One-symbol Shannon source coding bounds

For finite alphabets `α`, `β` with `q = |β| ≥ 2`, pmf `p` on `α`,
base-`q` entropy `H_q`, and codes `α → List β`:

* any injective uniquely decodable code has `H_q ≤ E[length]`;
* there exists prefix-free with `E[length] < H_q + 1`.

These are single-letter bounds, not the asymptotic block-coding theorem
(block coding / typical sequences).

C. E. Shannon, A Mathematical Theory of Communication,
Bell System Technical Journal 27 (1948), 379–423 and 623–656,
DOI 10.1002/j.1538-7305.1948.tb01338.x and
10.1002/j.1538-7305.1948.tb00917.x.
-/

/-- **Prefix-free code (Shannon source coding).** A code $c$ assigning to each element of $\alpha$
a finite word over $\beta$ is prefix-free when, for all distinct $a_1, a_2 \in \alpha$, the word
$c(a_1)$ is not a prefix of the word $c(a_2)$. This is the general notion of a prefix-free code. -/
abbrev IsPrefixFree {α β : Type*} (code : α → List β) : Prop :=
  MathlibExt.InformationTheory.IsPrefixFree code

/-- Each source symbol has probability at most one. -/
private theorem pmf_le_one {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1) (a : α) :
    p a ≤ 1 := by
  calc p a ≤ ∑ a : α, p a :=
        Finset.single_le_sum (fun i _ => le_of_lt (hp_pos i)) (Finset.mem_univ a)
    _ = 1 := hp_sum

/-- The Shannon length argument is nonnegative. -/
private theorem ceil_arg_nonneg {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
    (q : ℕ) (hq : 2 ≤ q) (a : α) :
    (0:ℝ) ≤ -Real.log (p a) / Real.log (q : ℝ) := by
  have hlogQ : (0:ℝ) < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogpa : Real.log (p a) ≤ 0 :=
    Real.log_nonpos (le_of_lt (hp_pos a)) (pmf_le_one p hp_pos hp_sum a)
  exact div_nonneg (neg_nonneg.mpr hlogpa) (le_of_lt hlogQ)

/-- The Kraft term for a Shannon length is bounded by the probability. -/
private theorem ceil_inv_pow_le {α : Type*}
    (p : α → ℝ) (hp_pos : ∀ a, 0 < p a)
    (q : ℕ) (hq : 2 ≤ q) (a : α) :
    (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹ ≤ p a) := by
  have hqpos : (0:ℝ) < (q : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogQ : (0:ℝ) < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast lt_of_lt_of_le (by norm_num) hq
  have hlogQne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogQ
  have h1 : (p a)⁻¹ ≤ (q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊) := by
    have e1 : (p a)⁻¹ = Real.exp (-Real.log (p a)) := by
      rw [← Real.exp_log (inv_pos.mpr (hp_pos a)), Real.log_inv]
    have e2 : ((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))
        = Real.exp (((⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊ : ℕ) : ℝ)
          * Real.log (q : ℝ)) := by
      rw [← Real.exp_log (pow_pos hqpos _), Real.log_pow]
    rw [e1, e2, Real.exp_le_exp]
    calc -Real.log (p a)
        = (-Real.log (p a) / Real.log (q : ℝ)) * Real.log (q : ℝ) :=
          (div_mul_cancel₀ _ hlogQne).symm
      _ ≤ (((⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊ : ℕ)) : ℝ)
          * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (le_of_lt hlogQ)
  have h2 := inv_anti₀ (inv_pos.mpr (hp_pos a)) h1
  rwa [inv_inv] at h2

/-- The Shannon lengths satisfy Kraft's inequality. -/
private theorem kraft_of_ceil {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
    (q : ℕ) (hq : 2 ≤ q) :
    ((∑ a : α, (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹)) ≤ 1) := by
  calc (∑ a : α, (((q : ℝ) ^ (⌈-Real.log (p a) / Real.log (q : ℝ)⌉₊))⁻¹))
      ≤ ∑ a : α, p a :=
        Finset.sum_le_sum (fun a _ => ceil_inv_pow_le p hp_pos q hq a)
    _ = 1 := hp_sum

/-- Expected length under near-entropy lengths is below entropy plus one. -/
private theorem expected_of_ceil {α : Type*} [Fintype α]
    (p : α → ℝ) (hp_pos : ∀ a, 0 < p a) (hp_sum : ∑ a : α, p a = 1)
    (q : ℕ)
    (L : α → ℕ)
    (hL : ∀ a, ((L a : ℕ) : ℝ) < -Real.log (p a) / Real.log (q : ℝ) + 1) :
    (∑ a : α, p a * ((L a : ℕ) : ℝ))
      < -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
  have hne : (Finset.univ : Finset α).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hp_sum
    norm_num at hp_sum
  have hstep : ∀ a ∈ (Finset.univ : Finset α),
      p a * ((L a : ℕ) : ℝ) < p a * (-Real.log (p a) / Real.log (q : ℝ) + 1) :=
    fun a _ => mul_lt_mul_of_pos_left (hL a) (hp_pos a)
  calc (∑ a : α, p a * ((L a : ℕ) : ℝ))
      < ∑ a : α, p a * (-Real.log (p a) / Real.log (q : ℝ) + 1) :=
        Finset.sum_lt_sum_of_nonempty hne hstep
    _ = -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
        calc (∑ a : α, p a * (-Real.log (p a) / Real.log (q : ℝ) + 1))
            = ∑ a : α, (-(p a * Real.log (p a)) / Real.log (q : ℝ) + p a) :=
              Finset.sum_congr rfl (fun a _ => by ring)
          _ = (∑ a : α, -(p a * Real.log (p a)) / Real.log (q : ℝ)) + ∑ a : α, p a :=
              Finset.sum_add_distrib
          _ = -(∑ a : α, p a * Real.log (p a)) / Real.log (q : ℝ) + 1 := by
              rw [← Finset.sum_div, Finset.sum_neg_distrib, hp_sum]

/--
**Shannon source coding lower bound.** Let $\alpha$ and $\beta$ be finite types with
$q = |\beta| \ge 2$, and let $p : \alpha \to \mathbb{R}$ satisfy $p(a) > 0$ for every $a \in \alpha$
and $\sum_{a \in \alpha} p(a) = 1$. Let $c$ assign to each $a \in \alpha$ a finite word $c(a)$ over
$\beta$, of length $|c(a)|$, such that $c$ is injective and its set of codewords is uniquely
decodable: any two finite lists of codewords with the same concatenation are equal. Then the
expected length $\sum_{a \in \alpha} p(a)\,|c(a)|$ is at least the base-$q$ entropy
$-\left(\sum_{a \in \alpha} p(a) \log p(a)\right) / \log q$, where $\log$ is the natural logarithm.

Proves `Wanted` entry `shannon_source_coding_lower_bound`.

Source: C. E. Shannon, Bell Syst. Tech. J. 27 (1948), 379-423 and 623-656, DOI
10.1002/j.1538-7305.1948.tb01338.x.
-/
theorem shannon_source_coding_lower_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ)
    (hp_pos : ∀ a, 0 < p a)
    (hp_sum : ∑ a : α, p a = 1)
    (hq : 2 ≤ Fintype.card β)
    (code : α → List β)
    (h_inj : Function.Injective code)
    (h_ud : InformationTheory.IsUniquelyDecodable (Set.range code)) :
    -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ)
      ≤ ∑ a : α, p a * ((code a).length : ℝ) := by
  classical
  have hcard_pos : (0:ℝ) < (Fintype.card β : ℝ) := by
    have : 0 < Fintype.card β := by omega
    exact_mod_cast this
  have hcard1 : (1:ℝ) < (Fintype.card β : ℝ) := by
    have : 1 < Fintype.card β := by omega
    exact_mod_cast this
  have hlog_pos : 0 < Real.log (Fintype.card β : ℝ) := Real.log_pos hcard1
  have hβne : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  -- Kraft inequality for the finite image
  have hrange_eq : Set.range code = ↑(Finset.image code Finset.univ) := by
    ext x
    simp
  have h_ud' : InformationTheory.IsUniquelyDecodable
      (↑(Finset.image code Finset.univ) : Set (List β)) := by
    rw [← hrange_eq]
    exact h_ud
  have hkraft0 := InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := Finset.image code Finset.univ) h_ud'
  have hInjOn : Set.InjOn code ↑(Finset.univ : Finset α) :=
    Set.injOn_of_injective h_inj
  have hkraft1 : ∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (code a).length ≤ 1 := by
    have h := hkraft0
    rw [Finset.sum_image hInjOn] at h
    simpa using h
  -- Gibbs pointwise bound
  have hGibbs_sum :
      ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a) ≤ 0 := by
    have hpoint : ∀ a ∈ (Finset.univ : Finset α),
        p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
          ≤ (1 / (Fintype.card β : ℝ)) ^ (code a).length - p a := by
      intro a _
      have hpa : 0 < p a := hp_pos a
      have hpa_ne : p a ≠ 0 := ne_of_gt hpa
      have hr_pos : (0:ℝ) < (1 / (Fintype.card β : ℝ)) ^ (code a).length := by
        apply pow_pos
        rw [one_div]
        exact inv_pos.mpr hcard_pos
      have hr_ne : (1 / (Fintype.card β : ℝ)) ^ (code a).length ≠ 0 := ne_of_gt hr_pos
      have hdiv_pos : (0:ℝ) < ((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a :=
        div_pos hr_pos hpa
      have hlog_le := Real.log_le_sub_one_of_pos hdiv_pos
      have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpa)
      -- p * (r/p - 1) = r - p
      have heq : p a * (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a - 1)
          = (1 / (Fintype.card β : ℝ)) ^ (code a).length - p a := by
        field_simp
      rwa [heq] at hmul
    calc ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
        ≤ ∑ a : α, ((1 / (Fintype.card β : ℝ)) ^ (code a).length - p a) :=
          Finset.sum_le_sum hpoint
      _ = (∑ a : α, (1 / (Fintype.card β : ℝ)) ^ (code a).length) - (∑ a : α, p a) := by
          rw [Finset.sum_sub_distrib]
      _ ≤ 0 := by
          rw [hp_sum]
          linarith [hkraft1]
  -- relate log r to length
  have hlogr : ∀ a : α, Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
      = - ((code a).length : ℝ) * Real.log (Fintype.card β : ℝ) := by
    intro a
    rw [one_div, inv_pow, Real.log_inv]
    rw [Real.log_pow]
    ring
  -- expand Gibbs sum
  have hexpand : ∑ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
      = -(∑ a : α, p a * ((code a).length : ℝ)) * Real.log (Fintype.card β : ℝ)
        - (∑ a : α, p a * Real.log (p a)) := by
    have hterm : ∀ a : α, p a * Real.log (((1 / (Fintype.card β : ℝ)) ^ (code a).length) / p a)
        = (p a * Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
          - p a * Real.log (p a)) := by
      intro a
      have hpa_ne : p a ≠ 0 := ne_of_gt (hp_pos a)
      have hr_ne : (1 / (Fintype.card β : ℝ)) ^ (code a).length ≠ 0 := by
        apply pow_ne_zero
        rw [one_div]
        exact inv_ne_zero (ne_of_gt hcard_pos)
      rw [Real.log_div hr_ne hpa_ne]
      ring
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    rw [Finset.sum_sub_distrib]
    congr 1
    · -- ∑ p * log r = -(∑ p * len) * log q
      have : ∀ a : α, p a * Real.log ((1 / (Fintype.card β : ℝ)) ^ (code a).length)
          = p a * ((code a).length : ℝ) * (- Real.log (Fintype.card β : ℝ)) := by
        intro a
        rw [hlogr a]
        ring
      rw [Finset.sum_congr rfl (fun a _ => this a)]
      rw [← Finset.sum_mul]
      ring
  rw [hexpand] at hGibbs_sum
  -- conclude by dividing
  rw [div_le_iff₀ hlog_pos]
  linarith

/--
**Shannon source coding upper bound.** Let $\alpha$ and $\beta$ be finite types with
$q = |\beta| \ge 2$, and let $p : \alpha \to \mathbb{R}$ satisfy $p(a) > 0$ for every $a \in \alpha$
and $\sum_{a \in \alpha} p(a) = 1$. Then there is a prefix-free code $c$ assigning to each
$a \in \alpha$ a finite word $c(a)$ over $\beta$, of length $|c(a)|$, whose expected length
$\sum_{a \in \alpha} p(a)\,|c(a)|$ is strictly less than
$-\left(\sum_{a \in \alpha} p(a) \log p(a)\right) / \log q + 1$, where $\log$ is the natural
logarithm.

Proves `Wanted` entry `shannon_source_coding_upper_bound`.

Source: C. E. Shannon, Bell Syst. Tech. J. 27 (1948), 379-423 and 623-656, DOI
10.1002/j.1538-7305.1948.tb01338.x.
-/
theorem shannon_source_coding_upper_bound
    {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ)
    (hp_pos : ∀ a, 0 < p a)
    (hp_sum : ∑ a : α, p a = 1)
    (hq : 2 ≤ Fintype.card β) :
    ∃ (code : α → List β),
      IsPrefixFree code ∧
        (∑ a : α, p a * ((code a).length : ℝ)) <
          -(∑ a : α, p a * Real.log (p a)) / Real.log (Fintype.card β : ℝ) + 1 := by
  classical
  set ℓ : α → ℕ := fun a => ⌈-Real.log (p a) / Real.log (Fintype.card β : ℝ)⌉₊
    with hℓdef
  have hkraft : (∑ a : α, ((Fintype.card β : ℝ) ^ (ℓ a))⁻¹) ≤ 1 :=
    kraft_of_ceil p hp_pos hp_sum _ hq
  obtain ⟨code, hpf, hlen⟩ := (KraftMcMillan.kraft_mcmillan_lengths ℓ hq).mpr
    (by simpa [one_div] using hkraft)
  refine ⟨code, hpf, ?_⟩
  have hE : (∑ a : α, p a * ((code a).length : ℝ))
      = ∑ a : α, p a * (((ℓ a : ℕ)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [hlen a]
  rw [hE]
  have hL : ∀ a, (((ℓ a : ℕ)) : ℝ)
      < -Real.log (p a) / Real.log (Fintype.card β : ℝ) + 1 := by
    intro a
    simp only [hℓdef]
    exact Nat.ceil_lt_add_one (ceil_arg_nonneg p hp_pos hp_sum _ hq a)
  exact expected_of_ceil p hp_pos hp_sum _ ℓ hL

end MathlibExt.InformationTheory.ShannonSourceCodingWanted

end
