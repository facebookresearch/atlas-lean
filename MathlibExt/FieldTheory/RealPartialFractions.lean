/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Partial fraction decomposition over the reals

Every real rational function is a polynomial plus a sum of fractions over powers of its
denominator's monic irreducible factors. These factors are linear or quadratic, and each
numerator has degree strictly smaller than its factor.
-/

@[expose] public section

open scoped Polynomial RatFunc

namespace MathlibExt.FieldTheory.RealPartialFractionsWanted

open Polynomial UniqueFactorizationMonoid

/--
**Partial fraction decomposition over $\mathbb{R}$.** For every real rational function
$f \in \mathbb{R}(X)$ there exist a polynomial $q \in \mathbb{R}[X]$, a finite set $S$ of monic
polynomials in $\mathbb{R}[X]$, each of degree $1$ or irreducible of degree $2$, and, for each
$p \in S$, a natural number $m_p$ and polynomials $g_{p,k} \in \mathbb{R}[X]$ for $k < m_p$, each
of degree less than the degree of $p$, such that, in $\mathbb{R}(X)$,
$$f = q + \sum_{p \in S} \sum_{k=0}^{m_p - 1} \frac{g_{p,k}}{p^{k+1}}.$$

Only existence is stated: the standard uniqueness of the decomposition (support and
multiplicities fixed by the denominator's irreducible factors) is not, so a witness may include
polynomials $p \in S$ with $m_p = 0$ or zero numerators $g_{p,k}$.

Sources: Field theory / `ℝ(X)`-partial fraction decomposition in `docs/undergrad.yaml`;
S. Lang, Algebra, rev. 3rd ed., Springer, 2002, Ch. IV, §5 (Partial fractions), p. 187;
https://en.wikipedia.org/wiki/Partial_fraction_decomposition#General_result
-/
public theorem ratFunc_partial_fractions_real (f : ℝ⟮X⟯) :
    ∃ (q : ℝ[X]) (s : Finset ℝ[X]) (g : ℝ[X] → ℕ → ℝ[X]) (m : ℝ[X] → ℕ),
      (∀ p ∈ s, p.Monic ∧ (p.natDegree = 1 ∨ (p.natDegree = 2 ∧ Irreducible p)))
        ∧ (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree)
        ∧ f = algebraMap ℝ[X] ℝ⟮X⟯ q
            + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
                algebraMap ℝ[X] ℝ⟮X⟯ (g p k) / algebraMap ℝ[X] ℝ⟮X⟯ p ^ (k + 1) := by
  classical
  let factors := normalizedFactors f.denom
  let s := factors.toFinset
  let m := fun p => factors.count p
  have hfactor (p : ℝ[X]) (hp : p ∈ s) : Irreducible p ∧ p.Monic := by
    obtain ⟨hirr, hmonic, _⟩ := (Polynomial.mem_normalizedFactors_iff f.denom_ne_zero).mp
      (Multiset.mem_toFinset.mp hp)
    exact ⟨hirr, hmonic⟩
  have hcop : Set.Pairwise (s : Set ℝ[X]) IsCoprime := by
    intro p hp t ht hne
    obtain ⟨hpirr, hpmon⟩ := hfactor p hp
    obtain ⟨htirr, htmon⟩ := hfactor t ht
    exact hpirr.coprime_iff_not_dvd.mpr fun h =>
      hne (eq_of_monic_of_associated hpmon htmon (hpirr.associated_of_dvd htirr h))
  have hden : f.denom = ∏ p ∈ s, p ^ m p := by
    calc
      f.denom = factors.prod := by
        simpa only [f.monic_denom.leadingCoeff, C_1, one_mul, factors] using
          (leadingCoeff_mul_prod_normalizedFactors f.denom).symm
      _ = _ := Finset.prod_multiset_count factors
  obtain ⟨q, r, hr, hsum⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := ℝ⟮X⟯) (g := id) (gi := fun p => (algebraMap ℝ[X] ℝ⟮X⟯ p)⁻¹) f.num
    (fun p hp => (hfactor p hp).2) hcop m
    (fun p hp => inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (hfactor p hp).2.ne_zero))
  refine ⟨q, s, fun p k => if h : k < m p then r p ⟨k, h⟩ else 0, m, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hirr, hmon⟩ := hfactor p hp
    refine ⟨hmon, or_iff_not_imp_left.mpr fun h => ⟨?_, hirr⟩⟩
    have := hirr.natDegree_pos
    have := hirr.natDegree_le_two
    omega
  · intro p hp k hk
    simp only [dite_eq_left hk]
    by_cases hz : r p ⟨k, hk⟩ = 0
    · simpa only [hz, natDegree_zero] using (hfactor p hp).1.natDegree_pos
    · exact natDegree_lt_natDegree hz (hr p hp ⟨k, hk⟩)
  · calc
      f = algebraMap ℝ[X] ℝ⟮X⟯ f.num / algebraMap ℝ[X] ℝ⟮X⟯ f.denom :=
        (RatFunc.num_div_denom f).symm
      _ = algebraMap ℝ[X] ℝ⟮X⟯ f.num * ∏ p ∈ s, (algebraMap ℝ[X] ℝ⟮X⟯ p)⁻¹ ^ m p := by
        rw [hden, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
        simp only [map_pow, inv_pow]
      _ = _ := by
        rw [hsum]
        congr 1
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_range]
        exact Fintype.sum_congr _ _ fun j => by
          simp only [dite_eq_left j.isLt, Fin.eta, div_eq_mul_inv, inv_pow]

end MathlibExt.FieldTheory.RealPartialFractionsWanted
