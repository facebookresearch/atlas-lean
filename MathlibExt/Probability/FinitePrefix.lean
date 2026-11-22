/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Prefix-dependent finite-horizon probability law

For a finite token alphabet and a normalized next-token law `q w` at every
finite prefix `w`, `law n q` is the horizon-`n` law of the whole word: the
first token is drawn from `q []`, and the remaining word from the law for
the kernel shifted by that token. The kernel may use the whole prefix; it
is not an i.i.d.-only construction. No infinite path law is made.
-/

open scoped ENNReal

@[expose] public section

namespace MathlibExt.Probability.FinitePrefix

private theorem map_cons_apply_eq {Token : Type*} (p : PMF (List Token)) (a : Token)
    (w : List Token) :
    (PMF.map (fun u => a :: u) p) (a :: w) = p w := by
  simp only [PMF.map_apply]
  refine (tsum_eq_single w (fun u hu => ?_)).trans ?_
  · apply ite_eq_right
    intro hcon
    have huw : w = u := by simpa using hcon
    exact hu huw.symm
  · exact ite_eq_left rfl

private theorem map_cons_apply_ne {Token : Type*} (p : PMF (List Token)) (x a : Token)
    (w : List Token) (h : x ≠ a) :
    (PMF.map (fun u => x :: u) p) (a :: w) = 0 := by
  simp only [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro u
  apply ite_eq_right
  intro hcon
  have hax : a = x ∧ w = u := by simpa using hcon
  exact h hax.1.symm

private theorem map_cons_apply_nil {Token : Type*} (p : PMF (List Token)) (x : Token) :
    (PMF.map (fun u => x :: u) p) [] = 0 := by
  simp only [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro u
  exact ite_eq_right (show ([] : List Token) ≠ x :: u from by simp)

section PrefixLaw

variable {Token : Type*} [Fintype Token]

/-- DEF (production): the horizon-`n` prefix-dependent word law.

`law 0 q = PMF.pure []`, and `law (n+1) q` draws the head token from
`q []`, then the tail from `law n` for the kernel shifted by that head. -/
noncomputable def law {Token : Type*} [Fintype Token] :
    (n : ℕ) → (List Token → PMF Token) → PMF (List Token)
  | 0, _ => PMF.pure []
  | n + 1, q =>
      PMF.bind (q [])
        (fun a => PMF.map (fun w => a :: w) (law n (fun p => q (a :: p))))

/-- DEF (production, auxiliary): product of next-token masses along a word.

For `a :: w`, this is `q [] a` times the same product for `w` under the
kernel shifted by `a`; prefixes are therefore `[]`, `[a]`,
`[a, b]`, and so on, in word order. -/
noncomputable def prefixProd {Token : Type*} [Fintype Token]
    (q : List Token → PMF Token) : List Token → ℝ≥0∞
  | [] => 1
  | a :: w => q [] a * prefixProd (fun p => q (a :: p)) w

/-- THM: the horizon-zero law is the point mass at the empty word. -/
theorem law_zero (q : List Token → PMF Token) :
    law 0 q = PMF.pure [] := by
  rfl

/-- THM: unfolding equation for positive horizons (the DEF, as a lemma). -/
theorem law_succ (n : ℕ) (q : List Token → PMF Token) :
    law (n + 1) q =
      PMF.bind (q [])
        (fun a => PMF.map (fun w => a :: w) (law n (fun p => q (a :: p)))) := by
  rfl

/-- THM: words of the wrong length have mass zero. -/
theorem law_apply_eq_zero_of_length_ne (n : ℕ) (q : List Token → PMF Token)
    {w : List Token} (hw : w.length ≠ n) :
    (law n q) w = 0 := by
  induction n generalizing w q with
  | zero =>
    have hnil : w ≠ [] := fun he => hw (by simp [he])
    rw [law_zero, PMF.pure_apply, ite_eq_right hnil]
  | succ n ih =>
    cases w with
    | nil =>
      rw [law_succ]
      simp only [PMF.bind_apply]
      rw [ENNReal.tsum_eq_zero]
      intro x
      rw [map_cons_apply_nil, mul_zero]
    | cons a w' =>
      have hw2 : w'.length + 1 ≠ n + 1 := by simpa [List.length_cons] using hw
      have hlen : w'.length ≠ n := by omega
      have hz : (law n (fun p => q (a :: p))) w' = 0 := by
        apply ih
        exact hlen
      rw [law_succ]
      simp only [PMF.bind_apply]
      rw [ENNReal.tsum_eq_zero]
      intro x
      by_cases hx : x = a
      · subst hx
        rw [map_cons_apply_eq, hz, mul_zero]
      · rw [map_cons_apply_ne _ _ _ _ hx, mul_zero]

/-- THM: one-step cons mass, the inductive heart of the product formula. -/
theorem mass_cons (n : ℕ) (q : List Token → PMF Token) (a : Token)
    (w : List Token) :
    (law (n + 1) q) (a :: w) =
      q [] a * (law n (fun p => q (a :: p))) w := by
  have houter : (∑' x, q [] x * (PMF.map (fun u => x :: u) (law n (fun p => q (x :: p)))) (a :: w))
      = q [] a * (PMF.map (fun u => a :: u) (law n (fun p => q (a :: p)))) (a :: w) := by
    refine tsum_eq_single a (fun x hx => ?_)
    show q [] x * (PMF.map (fun u => x :: u) (law n (fun p => q (x :: p)))) (a :: w) = 0
    rw [map_cons_apply_ne _ _ _ _ hx, mul_zero]
  rw [law_succ]
  simp only [PMF.bind_apply]
  rw [houter, map_cons_apply_eq]

/-- THM (proposed public symbol `mass_prefix_match`): product word mass.

The mass of a horizon-`n` word is the product, in order, of the
next-token masses at each of its proper prefixes. -/
theorem mass_prefix_match (n : ℕ) (q : List Token → PMF Token)
    {w : List Token} (hw : w.length = n) :
    (law n q) w = prefixProd q w := by
  induction n generalizing w q with
  | zero =>
    have hw' : w = [] := List.eq_nil_of_length_eq_zero hw
    subst hw'
    simp only [law_zero, PMF.pure_apply_self, prefixProd]
  | succ n ih =>
    cases w with
    | nil =>
      simp at hw
    | cons a w' =>
      have hw2 : w'.length + 1 = n + 1 := by simpa [List.length_cons] using hw
      have hlen : w'.length = n := by omega
      have hIH : (law n (fun p => q (a :: p))) w' = prefixProd (fun p => q (a :: p)) w' := by
        apply ih
        exact hlen
      rw [mass_cons]
      simp only [prefixProd]
      rw [hIH]

/-- THM: prefix marginal compatibility of PMF laws (equality of PMFs).

Mapping a horizon-`n` word to its length-`m` prefix gives exactly the
horizon-`m` law, for `m ≤ n`, with the same prefix-dependent kernel. -/
theorem map_take (m n : ℕ) (q : List Token → PMF Token) (h : m ≤ n) :
    PMF.map (fun w => List.take m w) (law n q) = law m q := by
  induction m generalizing n q with
  | zero =>
    have htake : (fun w : List Token => List.take 0 w) = Function.const _ [] := by
      funext w
      exact List.take_zero
    rw [htake, PMF.map_const, law_zero]
  | succ m ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hle : m ≤ n' := by omega
    rw [law_succ, law_succ]
    simp only [PMF.map_bind]
    congr 1
    funext a
    have hcomp : (fun w : List Token => List.take (m + 1) w) ∘ (fun w => a :: w)
        = (fun w => a :: w) ∘ (fun w => List.take m w) := by
      funext w
      simp only [Function.comp_apply]
      exact List.take_succ_cons
    have hIH : PMF.map (fun w : List Token => List.take m w) (law n' (fun p => q (a :: p)))
        = law m (fun p => q (a :: p)) := by
      apply ih
      exact hle
    rw [PMF.map_comp, hcomp, ← PMF.map_comp, hIH]

end PrefixLaw

end MathlibExt.Probability.FinitePrefix
