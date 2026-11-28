/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.ProductFormula

/-!
# Hilbert reciprocity gives an odd prime where the Hilbert symbol is $-1$

For nonzero rationals $a, b$ with $b > 0$ and $2$-adic Hilbert symbol $(a, b)_2 = -1$, there is an
odd prime $\ell$ with $(a, b)_\ell = -1$. The real symbol $(a, b)_\infty$ is $1$ as $b > 0$, so by
Hilbert's product formula (`Rat.hilbertSymbol_product_formula`) the $p$-adic symbols multiply to
$1$, and the factor $-1$ at $p = 2$ needs a partner at an odd prime.

This is a step of the proof of Proposition 16(a) of J. Koenigsmann, "Defining $\mathbb{Z}$ in
$\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93.
-/

set_option autoImplicit false

@[expose] public section

/-- **Hilbert reciprocity gives an odd prime where the Hilbert symbol is $-1$.** Let $a$ and $b$ be
nonzero rational numbers with $b > 0$, and suppose that the $2$-adic Hilbert symbol of their images
in $\mathbb{Q}_2$ is $(a, b)_2 = -1$. Then there is an odd prime $\ell$ such that the $\ell$-adic
Hilbert symbol of their images in $\mathbb{Q}_\ell$ is $(a, b)_\ell = -1$.

The proof: $(a, b)_\infty = 1$ since $b > 0$ (`realHilbertSymbol.eq_neg_one_iff_both_neg`), so
Hilbert's product formula (`Rat.hilbertSymbol_product_formula`) gives $\prod_p (a, b)_p = 1$. If
$(a, b)_\ell \ne -1$, hence $(a, b)_\ell = 1$, at every odd prime $\ell$, the product would be
$(a, b)_2 = -1$.

Source: J. Koenigsmann, "Defining $\mathbb{Z}$ in $\mathbb{Q}$", Ann. of Math. 183 (2016), 73–93,
<https://doi.org/10.4007/annals.2016.183.1.2>, proof of Proposition 16(a), read in the accepted
version arXiv:1011.3424v2, pp. 14–15: "we have, by Observation 5, $(2p, q)_2 = -1$. By Hilbert
reciprocity, there must also be an odd prime $l$ such that $(2p, q)_l = -1$", where $p, q$ are
squarefree positive integers. Here $a$ and $b$ stand for $2p$ and $q$; the statement needs only
$b > 0$. -/
theorem Rat.exists_odd_prime_padicHilbertSymbol_eq_neg_one {a b : ℚˣ} (hb : 0 < (b : ℚ))
    (h2 : padicHilbertSymbol 2 (Units.map (Rat.castHom ℚ_[2]).toMonoidHom a)
      (Units.map (Rat.castHom ℚ_[2]).toMonoidHom b) = -1) :
    ∃ ℓ : Nat.Primes, (ℓ : ℕ) ≠ 2 ∧
      haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
      padicHilbertSymbol ℓ (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom a)
        (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom b) = -1 := by
  obtain ⟨-, hprod⟩ := Rat.hilbertSymbol_product_formula a b
  have hreal : realHilbertSymbol (Units.map (Rat.castHom ℝ).toMonoidHom a)
      (Units.map (Rat.castHom ℝ).toMonoidHom b) = 1 := by
    rcases realHilbertSymbol.eq_one_or_neg_one (Units.map (Rat.castHom ℝ).toMonoidHom a)
      (Units.map (Rat.castHom ℝ).toMonoidHom b) with h | h
    · exact h
    · rw [realHilbertSymbol.eq_neg_one_iff_both_neg] at h
      have hb' : ((b : ℚ) : ℝ) < 0 := by simpa using h.2
      exact absurd hb' (not_lt.2 (by exact_mod_cast hb.le))
  rw [hreal, one_mul] at hprod
  by_contra hcon
  push Not at hcon
  have hall : ∀ ℓ : Nat.Primes, ℓ ≠ ⟨2, Nat.prime_two⟩ →
      (haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
      padicHilbertSymbol ℓ (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom a)
        (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom b)) = 1 := by
    intro ℓ hℓ
    have hℓ2 : (ℓ : ℕ) ≠ 2 := fun h => hℓ (Subtype.ext h)
    have : Fact (ℓ : ℕ).Prime := ⟨ℓ.prop⟩
    rcases padicHilbertSymbol.eq_one_or_neg_one (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom a)
      (Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom b) with h | h
    · exact h
    · exact absurd h (hcon ℓ hℓ2)
  rw [finprod_eq_single _ ⟨2, Nat.prime_two⟩ hall] at hprod
  have : (-1 : ℤ) = 1 := h2.symm.trans hprod
  exact absurd this (by decide)
