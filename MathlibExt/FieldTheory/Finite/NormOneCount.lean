/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Elements of norm one in a finite field with $q^2$ elements

A finite field $K$ with $q^2$ elements has exactly $q + 1$ elements $\beta$ with
$\beta^{q + 1} = 1$, that is, with norm $N(\beta) = \beta^{q+1} = 1$ for the quadratic extension
$K \supseteq \mathbb{F}_q$. For an extension $L / K$ of finite fields with $\# K = q$ and
$\# L = q^2$, this counts the elements of $L$ whose norm `Algebra.norm K` is $1$.

The proof: $K^\times$ is cyclic of order $q^2 - 1 = (q - 1)(q + 1)$, so it holds a primitive
$(q + 1)$-th root of unity, and then the equation $\beta^{q + 1} = 1$ has exactly $q + 1$ solutions
(`IsPrimitiveRoot.card_nthRootsFinset`).

This is the statement "$\mathbb{F}_{q^2}$ contains $q + 1$ norm-1 elements" of the proof of
Lemma 2.3 of B. Poonen, "Characterizing integers among rational numbers with a
universal-existential formula", Amer. J. Math. 131 (2009), 675–682.
-/

set_option autoImplicit false

public section

namespace FiniteField

/-- **$\mathbb{F}_{q^2}$ has exactly $q + 1$ elements with $\beta^{q+1} = 1$.** Let $K$ be a finite
field with $q^2$ elements. Then exactly $q + 1$ elements $\beta \in K$ satisfy
$\beta^{q + 1} = 1$.

For the quadratic extension $K \supseteq \mathbb{F}_q$, $\beta^{q+1}$ is the norm of $\beta$
(`FiniteField.card_norm_eq_one_of_card_eq_sq` states the count with `Algebra.norm`). The source
takes $q$ to be a prime power; that follows from $\# K = q^2$, so it is not a hypothesis here.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, read in the author's version
with the corrections of April 15, 2019, p. 3: "Since $\mathbb{F}_{q^2}$ contains $q + 1$ norm-1
elements, $U_q \neq \emptyset$", with $N$ the norm for $\mathbb{F}_{q^2}/\mathbb{F}_q$. -/
theorem card_pow_add_one_eq_one_of_card_eq_sq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q : ℕ} (hK : Fintype.card K = q ^ 2) :
    (Finset.univ.filter fun β : K => β ^ (q + 1) = 1).card = q + 1 := by
  have hq : 2 ≤ q := by
    have h2 := Fintype.one_lt_card (α := K)
    rw [hK] at h2
    rcases q with _ | _ | q
    · simp at h2
    · simp at h2
    · omega
  -- A generator of the cyclic group `Kˣ`, of order `q ^ 2 - 1`.
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hK]
    have h1 : (q - 1) * (q + 1) = q * q - 1 := by
      zify [show 1 ≤ q by omega, show 1 ≤ q * q by nlinarith]
      ring
    rw [h1, sq]
  have hprim : IsPrimitiveRoot g ((q - 1) * (q + 1)) := by
    rw [← hcard, ← hg]
    exact IsPrimitiveRoot.orderOf g
  have hζ : IsPrimitiveRoot ((g : K) ^ (q - 1)) (q + 1) := by
    have := (hprim.pow_of_dvd (show q - 1 ≠ 0 by omega) (dvd_mul_right _ _))
    rw [Nat.mul_div_cancel_left _ (show 0 < q - 1 by omega)] at this
    rw [← Units.val_pow_eq_pow_val]
    exact IsPrimitiveRoot.coe_units_iff.2 this
  have hset : (Finset.univ.filter fun β : K => β ^ (q + 1) = 1) =
      Polynomial.nthRootsFinset (q + 1) (1 : K) := by
    ext β
    simp [Polynomial.mem_nthRootsFinset (Nat.succ_pos q)]
  rw [hset, hζ.card_nthRootsFinset]

/-- **The norm-one elements of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$.** Let $L / K$ be an extension
of finite fields with $\# K = q$ and $\# L = q^2$. Then exactly $q + 1$ elements $\beta \in L$ have
norm $N_{L/K}(\beta) = 1$.

The norm is $\beta^{q+1}$ (`FiniteField.algebraMap_norm_eq_pow`), so this is
`FiniteField.card_pow_add_one_eq_one_of_card_eq_sq`.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, read in the author's version
with the corrections of April 15, 2019, p. 3: "Since $\mathbb{F}_{q^2}$ contains $q + 1$ norm-1
elements, $U_q \neq \emptyset$". -/
theorem card_norm_eq_one_of_card_eq_sq {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L]
    [DecidableEq K] [Algebra K L] {q : ℕ} (hK : Fintype.card K = q)
    (hL : Fintype.card L = q ^ 2) :
    (Finset.univ.filter fun β : L => Algebra.norm K β = 1).card = q + 1 := by
  classical
  have hq : 2 ≤ q := by
    have h2 := Fintype.one_lt_card (α := K)
    omega
  have hexp : (Nat.card L - 1) / (Nat.card K - 1) = q + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hK, hL]
    have h1 : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      zify [show 1 ≤ q by omega, show 1 ≤ q ^ 2 by nlinarith]
      ring
    rw [h1, Nat.mul_div_cancel _ (show 0 < q - 1 by omega)]
  have hset : (Finset.univ.filter fun β : L => Algebra.norm K β = 1) =
      (Finset.univ.filter fun β : L => β ^ (q + 1) = 1) := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hexp, ← FiniteField.algebraMap_norm_eq_pow, ← map_one (algebraMap K L),
      (algebraMap K L).injective.eq_iff]
  rw [hset, card_pow_add_one_eq_one_of_card_eq_sq hL]

end FiniteField
