/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Separable

/-!
# Irreducible polynomials as expansions of separable irreducibles

Corollary 4.5 of ATLAS `NumberTheoryI`: if `f` is irreducible over a field
`K` of characteristic `p`, then `f(x) = g(x ^ (p ^ n))` for some irreducible
separable `g` and some `n ≥ 0`, and the pair `(n, g)` is uniquely
determined by `f`.

Mathlib already has the two ingredients separately:
`Polynomial.exists_separable_of_irreducible` produces a separable `g`
without irreducibility, and `Polynomial.unique_separable_of_irreducible`
gives uniqueness among separable polynomials in positive characteristic.
The new content here is the irreducibility of `g` (from
`Polynomial.of_irreducible_expand_pow`) and the characteristic-zero
uniqueness (a degree argument: an expansion by `0 ^ n` with `n > 0` is
constant, while `f` has positive degree).

## Main results

* `Polynomial.exists_irreducible_separable_expand_eq`: existence of
  `(n, g)` with `g` irreducible and separable and
  `expand K ((ringChar K) ^ n) g = f`.
* `Polynomial.unique_irreducible_separable_expand_eq`: the pair
  `(n, g)` is unique.
* `Polynomial.exists_unique_irreducible_separable_expand_eq`: existence
  and uniqueness combined.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K]

/-- **Irreducible polynomials are expansions of separable irreducibles.** Let $K$ be a field
of characteristic $p$ (with $p = 0$ in characteristic zero) and let $f \in K[x]$ be irreducible.
Then there exist $n \in \mathbb{N}$ and an irreducible separable polynomial $g \in K[x]$ such
that $f(x) = g(x^{p^n})$, where $0^0 = 1$.

Source: ATLAS NumberTheoryI, Corollary 4.5 (existence). -/
theorem exists_irreducible_separable_expand_eq {f : K[X]}
    (hf : Irreducible f) :
    ∃ (n : ℕ) (g : K[X]),
      Irreducible g ∧ g.Separable ∧
        expand K ((ringChar K) ^ n) g = f := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp0
  · obtain ⟨n, g, hg_sep, hgf⟩ :=
      exists_separable_of_irreducible (ringChar K) hf hp.ne_zero
    refine ⟨n, g, ?_, hg_sep, hgf⟩
    have hirr : Irreducible (expand K ((ringChar K) ^ n) g) :=
      hgf.symm ▸ hf
    exact of_irreducible_expand_pow hp.ne_zero hirr
  · have h0 : CharP K 0 := by
      rw [← hp0]
      infer_instance
    have : CharZero K := CharP.charP_to_charZero K
    exact ⟨0, f, hf, hf.separable, by rw [pow_zero, expand_one]⟩

/-- **The separable irreducible underlying an irreducible polynomial is unique.** Let $K$ be a
field of characteristic $p$ (with $p = 0$ in characteristic zero) and let $f \in K[x]$ be
irreducible. If $n_1, n_2 \in \mathbb{N}$ and irreducible separable polynomials
$g_1, g_2 \in K[x]$ satisfy $f(x) = g_1(x^{p^{n_1}})$ and $f(x) = g_2(x^{p^{n_2}})$, where
$0^0 = 1$, then $n_1 = n_2$ and $g_1 = g_2$.

Source: ATLAS NumberTheoryI, Corollary 4.5 (uniqueness). -/
theorem unique_irreducible_separable_expand_eq {f : K[X]}
    (hf : Irreducible f) {n₁ n₂ : ℕ} {g₁ g₂ : K[X]}
    (h₁ : Irreducible g₁ ∧ g₁.Separable ∧
      expand K ((ringChar K) ^ n₁) g₁ = f)
    (h₂ : Irreducible g₂ ∧ g₂.Separable ∧
      expand K ((ringChar K) ^ n₂) g₂ = f) :
    n₁ = n₂ ∧ g₁ = g₂ := by
  obtain ⟨-, hg₁_sep, hgf₁⟩ := h₁
  obtain ⟨-, hg₂_sep, hgf₂⟩ := h₂
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp0
  · exact unique_separable_of_irreducible (ringChar K) hf hp.pos n₁ g₁
      hg₁_sep hgf₁ n₂ g₂ hg₂_sep hgf₂
  · have hn₁ : n₁ = 0 := by
      by_contra hn
      have hpow : (ringChar K) ^ n₁ = 0 := by
        rw [hp0]
        exact zero_pow hn
      have hdeg : f.natDegree = g₁.natDegree * (ringChar K) ^ n₁ := by
        rw [← hgf₁, natDegree_expand]
      rw [hpow, mul_zero] at hdeg
      exact hf.natDegree_pos.ne' hdeg
    have hn₂ : n₂ = 0 := by
      by_contra hn
      have hpow : (ringChar K) ^ n₂ = 0 := by
        rw [hp0]
        exact zero_pow hn
      have hdeg : f.natDegree = g₂.natDegree * (ringChar K) ^ n₂ := by
        rw [← hgf₂, natDegree_expand]
      rw [hpow, mul_zero] at hdeg
      exact hf.natDegree_pos.ne' hdeg
    subst hn₁
    subst hn₂
    refine ⟨rfl, ?_⟩
    rw [pow_zero, expand_one] at hgf₁ hgf₂
    rw [hgf₁, hgf₂]

/-- **Irreducible polynomials are uniquely expansions of separable irreducibles.** Let $K$ be a
field of characteristic $p$ (with $p = 0$ in characteristic zero, and $0^0 = 1$) and let
$f \in K[x]$ be irreducible. Then there exist $n \in \mathbb{N}$ and an
irreducible separable polynomial $g \in K[x]$ with $f(x) = g(x^{p^n})$, and for every
$n' \in \mathbb{N}$ and every irreducible separable polynomial $g' \in K[x]$ with
$f(x) = g'(x^{p^{n'}})$ we have $n' = n$ and $g' = g$.

Source: ATLAS NumberTheoryI, Corollary 4.5. -/
theorem exists_unique_irreducible_separable_expand_eq {f : K[X]}
    (hf : Irreducible f) :
    ∃ (n : ℕ) (g : K[X]),
      (Irreducible g ∧ g.Separable ∧
        expand K ((ringChar K) ^ n) g = f) ∧
        ∀ (n' : ℕ) (g' : K[X]),
          Irreducible g' ∧ g'.Separable ∧
            expand K ((ringChar K) ^ n') g' = f →
              n' = n ∧ g' = g := by
  obtain ⟨n, g, hg_irr, hg_sep, hgf⟩ :=
    exists_irreducible_separable_expand_eq hf
  exact ⟨n, g, ⟨hg_irr, hg_sep, hgf⟩, fun n' g' h' =>
    unique_irreducible_separable_expand_eq hf h' ⟨hg_irr, hg_sep, hgf⟩⟩

end Polynomial
