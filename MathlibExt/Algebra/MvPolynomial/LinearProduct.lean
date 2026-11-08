/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Portions modified by Meta Platforms, Inc. and affiliates.

The modifications generalize the coefficient ring and variable type, replace
the source-local linearity predicate with `MvPolynomial.IsHomogeneous`, and
reuse Mathlib's characterization of degree-one finitely supported functions.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coefficients of a product with a homogeneous linear polynomial

If `p` is homogeneous of degree one, the coefficient of a monomial in `p * q`
is a sum over the variables occurring in that monomial. This is adapted from
`eth/proof/rates/GeneralPieces/GenF/Bra.lean` in Anthropic's `formal-math`
repository, commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

set_option autoImplicit false

namespace MvPolynomial

/-- The coefficient of `p * q`, when `p` is homogeneous of degree one, is the
sum obtained by removing one occurrence of each variable in the monomial. -/
public theorem IsHomogeneous.coeff_mul_eq_sum_support {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} (hp : p.IsHomogeneous 1) (q : MvPolynomial σ R)
    (m : σ →₀ ℕ) :
    (p * q).coeff m =
      ∑ i ∈ m.support, p.coeff (Finsupp.single i 1) *
        q.coeff (m - Finsupp.single i 1) := by
  classical
  have hsub {d : σ →₀ ℕ} {i : σ} (hi : i ∈ d.support) :
      d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
    tsub_add_cancel_of_le
      (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)))
  rw [MvPolynomial.coeff_mul]
  have hinj : Set.InjOn
      (fun i : σ => ((Finsupp.single i 1 : σ →₀ ℕ), m - Finsupp.single i 1))
      m.support := fun a _ b _ hab => by
    have hab' := congrArg Prod.fst hab
    exact (Finsupp.single_left_injective one_ne_zero) hab'
  rw [← Finset.sum_image
    (f := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => p.coeff x.1 * q.coeff x.2) hinj]
  symm
  refine Finset.sum_subset (fun x hx => ?_) fun x hx hn => ?_
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_comm]
    exact hsub hi
  · by_contra hne
    have hdegree : x.1.degree = 1 := by
      by_contra hd
      exact (left_ne_zero_of_mul hne) (hp.coeff_eq_zero hd)
    have hrange : x.1 ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]
      exact hdegree
    obtain ⟨i, hi⟩ := hrange
    have hsum : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    refine hn (Finset.mem_image.2 ⟨i, ?_, ?_⟩)
    · rw [Finsupp.mem_support_iff, ← hsum, ← hi]
      simp
    · refine Prod.ext hi ?_
      rw [← hsum, ← hi]
      simp

end MvPolynomial
