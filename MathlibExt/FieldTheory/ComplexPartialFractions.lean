/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Partial fraction decomposition over `ℂ`

Every complex rational function `f ∈ ℂ(X)` is a polynomial plus a finite sum of fractions
`g / p ^ (k + 1)`, where each `p` is a monic polynomial of degree `1` and each numerator `g` has
degree less than that of `p`.

Write `f = num / denom` with `denom` monic (`RatFunc.num_div_denom`). As `ℂ` is algebraically
closed, `denom` is the product of the powers `(X - a) ^ μ(a)` over its distinct roots `a`, where
`μ(a)` is the multiplicity of `a`, and the polynomials `X - a` are monic and pairwise coprime.
Mathlib's partial fraction decomposition for a product of powers of such polynomials
(`Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`) then writes `f` as
`q + ∑ a, ∑ k < μ(a), r a k / (X - a) ^ (k + 1)` with `deg (r a k) < 1`. The finite set of the
statement is that of the factors `X - a`.

## Main statements

* `ratFunc_partial_fractions_complex`: the decomposition above (existence only).

## References

* S. Lang, *Algebra*, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions).
* Mathlib's `docs/undergrad.yaml`: partial fraction decomposition in `ℂ(X)`.
-/

@[expose] public section

open scoped Polynomial RatFunc

namespace MathlibExt.FieldTheory.ComplexPartialFractionsWanted

open Polynomial

/--
**Partial fraction decomposition over $\mathbb{C}$.** For every complex rational function
$f \in \mathbb{C}(X)$ there exist a polynomial $q \in \mathbb{C}[X]$, a finite set $S$ of monic
polynomials of degree $1$ in $\mathbb{C}[X]$, and, for each $p \in S$, a natural number $m_p$
and polynomials $g_{p,k} \in \mathbb{C}[X]$ for $k < m_p$, each of degree less than the degree
of $p$, such that, in $\mathbb{C}(X)$,
$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

Sources: Field theory / `ℂ(X)`-partial fraction decomposition in `docs/undergrad.yaml`;
S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187;
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#Statement
-/
public theorem ratFunc_partial_fractions_complex (f : ℂ⟮X⟯) :
    ∃ (q : ℂ[X]) (s : Finset ℂ[X]) (g : ℂ[X] → ℕ → ℂ[X]) (m : ℂ[X] → ℕ),
      (∀ p ∈ s, p.Monic ∧ p.natDegree = 1)
        ∧ (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree)
        ∧ f = algebraMap ℂ[X] ℂ⟮X⟯ q
            + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
                algebraMap ℂ[X] ℂ⟮X⟯ (g p k) / algebraMap ℂ[X] ℂ⟮X⟯ p ^ (k + 1) := by
  classical
  -- `root p` recovers `a` from `p = X - C a`.
  let root : ℂ[X] → ℂ := fun p => -p.coeff 0
  have hroot (a : ℂ) : root (X - C a) = a := by
    simp only [root, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg]
  -- The set `t` of the factors `X - C a` of the denominator, at the distinct roots `a`, and the
  -- multiplicity `n p` of each factor `p`.
  let t : Finset ℂ[X] := f.denom.roots.toFinset.image fun a => X - C a
  let n : ℂ[X] → ℕ := fun p => rootMultiplicity (root p) f.denom
  have hinj : Set.InjOn (fun a : ℂ => X - C a) f.denom.roots.toFinset := fun a _ b _ hab => by
    simpa only [hroot] using congrArg root hab
  have ht : ∀ p ∈ t, p.Monic ∧ p.natDegree = 1 := by
    intro p hp
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨monic_X_sub_C a, natDegree_X_sub_C a⟩
  have hcop : Set.Pairwise (t : Set ℂ[X]) fun p p' => IsCoprime p p' := by
    intro p hp p' hp' hpp'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hp'
    exact pairwise_coprime_X_sub_C Function.injective_id fun hab => hpp' (by rw [hab])
  -- Over `ℂ`, the monic denominator is the product of the powers `p ^ n p` for `p ∈ t`.
  have hden : algebraMap ℂ[X] ℂ⟮X⟯ f.denom = ∏ p ∈ t, algebraMap ℂ[X] ℂ⟮X⟯ p ^ n p := by
    have hsplit : ∏ a ∈ f.denom.roots.toFinset, (X - C a) ^ rootMultiplicity a f.denom =
        f.denom :=
      prod_multiset_root_eq_finset_root.symm.trans
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq f.monic_denom
          IsAlgClosed.card_roots_eq_natDegree)
    rw [Finset.prod_image hinj]
    conv_lhs => rw [← hsplit]
    simp only [map_prod, map_pow, n, hroot]
  -- Partial fractions for `num / denom = num * ∏ p ∈ t, p⁻¹ ^ n p`.
  obtain ⟨q, r, hr, hf⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := ℂ⟮X⟯) (g := id) (gi := fun p => (algebraMap ℂ[X] ℂ⟮X⟯ p)⁻¹) f.num
    (fun p hp => (ht p hp).1) hcop n
    (fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (ht p hp).1.ne_zero))
  refine ⟨q, t, fun p k => if h : k < n p then r p ⟨k, h⟩ else 0, n, ht, ?_, ?_⟩
  · -- Each numerator has degree less than `1`.
    intro p hp k hk
    simp only [dite_eq_left hk]
    by_cases h0 : r p ⟨k, hk⟩ = 0
    · rw [h0, natDegree_zero, (ht p hp).2]
      exact one_pos
    · exact natDegree_lt_natDegree h0 (hr p hp ⟨k, hk⟩)
  · calc f = algebraMap ℂ[X] ℂ⟮X⟯ f.num / algebraMap ℂ[X] ℂ⟮X⟯ f.denom :=
          (RatFunc.num_div_denom f).symm
      _ = algebraMap ℂ[X] ℂ⟮X⟯ f.num * ∏ p ∈ t, (algebraMap ℂ[X] ℂ⟮X⟯ p)⁻¹ ^ n p := by
          rw [hden, div_eq_mul_inv, ← Finset.prod_inv_distrib]
          simp only [inv_pow]
      _ = algebraMap ℂ[X] ℂ⟮X⟯ q + ∑ p ∈ t, ∑ j : Fin (n p),
            algebraMap ℂ[X] ℂ⟮X⟯ (r p j) * (algebraMap ℂ[X] ℂ⟮X⟯ p)⁻¹ ^ (j.1 + 1) := hf
      _ = _ := by
          -- Reindex each inner sum by `Finset.range (n p)`.
          refine congrArg (algebraMap ℂ[X] ℂ⟮X⟯ q + ·) (Finset.sum_congr rfl fun p _ => ?_)
          rw [Finset.sum_range]
          refine Fintype.sum_congr _ _ fun j => ?_
          simp only [dite_eq_left j.isLt, Fin.eta, div_eq_mul_inv, inv_pow]

end MathlibExt.FieldTheory.ComplexPartialFractionsWanted
