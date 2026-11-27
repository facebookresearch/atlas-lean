/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.Hensel

/-!
# A trace that is not a $p$-adic integer gives two distinct roots

For a prime $p$ and $s \in \mathbb{Q}_p \setminus \mathbb{Z}_p$, that is, $\lVert s \rVert > 1$,
the polynomial $x^2 - sx + 1$ splits over $\mathbb{Q}_p$ into two distinct linear factors
$(x - r_1)(x - r_2)$, with $\lVert r_1 \rVert = \lVert s \rVert$ and
$\lVert r_2 \rVert = \lVert s \rVert^{-1}$.

This is the step "If $s \in \mathbb{Q}_p - \mathbb{Z}_p$, then $x^2 - sx + 1$ is a product of
two distinct factors, by the theory of Newton polygons" of the proof of Lemma 2.1(ii) of
B. Poonen, "Characterizing integers among rational numbers with a universal-existential formula",
Amer. J. Math. 131 (2009), 675–682. The proof here uses Hensel's lemma (`hensels_lemma`) instead
of Newton polygons: with $x = su$, the polynomial becomes $s^2 (u^2 - u + s^{-2})$, and
$u^2 - u + s^{-2} \in \mathbb{Z}_p[u]$ has a root $u \equiv 1 \pmod p$.
-/

set_option autoImplicit false

public section

open Polynomial

namespace Padic

/-- **A trace outside $\mathbb{Z}_p$ gives two distinct roots.** Let $p$ be a prime and let
$s \in \mathbb{Q}_p$ with $\lVert s \rVert > 1$, that is, $s \in \mathbb{Q}_p \setminus
\mathbb{Z}_p$. Then there are $r_1, r_2 \in \mathbb{Q}_p$ with
$$x^2 - sx + 1 = (x - r_1)(x - r_2)$$
in $\mathbb{Q}_p[x]$, $r_1 \neq r_2$, $\lVert r_1 \rVert = \lVert s \rVert$ and
$\lVert r_2 \rVert = \lVert s \rVert^{-1}$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.1(ii), read in the author's
version with the corrections of April 15, 2019, p. 3: "If $s \in \mathbb{Q}_p - \mathbb{Z}_p$,
then $x^2 - sx + 1$ is a product of two distinct factors, by the theory of Newton polygons". The
norms of the roots are the slopes $\pm v_p(s)$ of that Newton polygon. -/
theorem exists_eq_mul_X_sub_C_of_one_lt_norm {p : ℕ} [Fact p.Prime] {s : ℚ_[p]}
    (hs : 1 < ‖s‖) :
    ∃ r₁ r₂ : ℚ_[p], (X ^ 2 - C s * X + 1 : ℚ_[p][X]) = (X - C r₁) * (X - C r₂) ∧
      r₁ ≠ r₂ ∧ ‖r₁‖ = ‖s‖ ∧ ‖r₂‖ = ‖s‖⁻¹ := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hs
    linarith
  -- The constant term `s⁻² ∈ ℤ_p` of the rescaled polynomial.
  have hc : ‖s⁻¹ ^ 2‖ < 1 := by
    rw [norm_pow, norm_inv]
    have : ‖s‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
    nlinarith [norm_nonneg s, inv_nonneg.2 (norm_nonneg s)]
  let c : ℤ_[p] := ⟨s⁻¹ ^ 2, hc.le⟩
  have hcn : ‖c‖ < 1 := hc
  let F : ℤ_[p][X] := X ^ 2 - X + C c
  have hF1 : aeval (1 : ℤ_[p]) F = c := by simp [F]
  have hF'1 : aeval (1 : ℤ_[p]) (derivative F) = 1 := by
    simp only [F, derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_C]
    simp
    norm_num
  obtain ⟨z, hz, hz1, -, -⟩ := hensels_lemma (F := F) (a := 1) (by
    rw [hF1, hF'1, norm_one, one_pow]
    exact hcn)
  rw [hF'1, norm_one] at hz1
  -- `z` is a unit of `ℤ_p`.
  have hzn : ‖z‖ = 1 := by
    have h := PadicInt.norm_add_eq_max_of_ne (q := 1) (r := z - 1)
      (by rw [norm_one]; exact hz1.ne')
    rw [add_sub_cancel, norm_one] at h
    rw [h]
    exact max_eq_left hz1.le
  have hzq : ((z : ℚ_[p])) ^ 2 - (z : ℚ_[p]) + s⁻¹ ^ 2 = 0 := by
    have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz
    simp only [F, map_add, map_sub, map_pow, aeval_X, aeval_C, PadicInt.coe_add,
      PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_zero] at this
    exact this
  set r : ℚ_[p] := s * (z : ℚ_[p]) with hr
  have hrn : ‖r‖ = ‖s‖ := by
    rw [hr, norm_mul, PadicInt.norm_coe, hzn, mul_one]
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, norm_zero] at hrn
    exact hs0 (norm_eq_zero.1 hrn.symm)
  have hroot : r ^ 2 - s * r + 1 = 0 := by
    have : r ^ 2 - s * r + 1 = s ^ 2 * ((z : ℚ_[p]) ^ 2 - (z : ℚ_[p]) + s⁻¹ ^ 2) := by
      rw [hr]
      field_simp
    rw [this, hzq, mul_zero]
  have hsum : s = r + r⁻¹ := by
    field_simp
    linear_combination -hroot
  refine ⟨r, r⁻¹, ?_, ?_, hrn, by rw [norm_inv, hrn]⟩
  · have h1 : C r * C r⁻¹ = (1 : ℚ_[p][X]) := by
      rw [← C_mul, mul_inv_cancel₀ hr0, C_1]
    rw [hsum, C_add]
    linear_combination (-1 : ℚ_[p][X]) * h1
  · intro h
    have h' := congrArg norm h
    rw [norm_inv, hrn] at h'
    have : ‖s‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
    linarith

end Padic
