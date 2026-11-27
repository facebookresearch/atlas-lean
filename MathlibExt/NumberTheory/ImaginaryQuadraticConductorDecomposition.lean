/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ImaginaryQuadraticDiscriminant
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Conductor decompositions of imaginary quadratic discriminants

Every imaginary quadratic discriminant `D` has a conductor decomposition `D = f ^ 2 * D_K` with
`f ≥ 1` and `D_K` a fundamental imaginary quadratic discriminant
(`ImaginaryQuadraticDiscriminant.exists_conductor_decomposition`).

## Proof

Write `|D| = b ^ 2 * a` with `a` squarefree (`Nat.sq_mul_squarefree_of_pos`), so that
`D = b ^ 2 * (-a)` and `-a` is squarefree. Then `a ≢ 0 (mod 4)`.

* If `-a ≡ 1 (mod 4)`, take `f = b` and `D_K = -a`.
* Otherwise `-a ≡ 2` or `3 (mod 4)`. If `b` were odd, then `b ^ 2 ≡ 1 (mod 4)` and
  `D ≡ -a (mod 4)` would be `2` or `3`, against `D ≡ 0` or `1 (mod 4)`. So `b = 2k`, and
  `D = k ^ 2 * (4 * (-a))`: take `f = k` and `D_K = 4 * (-a)`.
-/

namespace ImaginaryQuadraticDiscriminant

/-- **Every imaginary quadratic discriminant has a conductor decomposition.** Every imaginary
quadratic discriminant $D$, that is, every integer $D < 0$ with $D \equiv 0$ or
$1 \pmod 4$, has a conductor decomposition: there are an integer $f \ge 1$ and a fundamental
imaginary quadratic discriminant $D_K$ with $D = f^2 D_K$.

Fowler takes $D_K$ to be the discriminant of $K = \mathbb{Q}(\sqrt{D})$.

Source: Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in*
$\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, proof of
Proposition 2.7, p. 615, https://doi.org/10.1017/S0305004125101825 ("Write $\Delta = f^2 D$,
where $D$ is the discriminant of $\mathbb{Q}(\sqrt{\Delta})$"). -/
public theorem exists_conductor_decomposition {D : ℤ}
    (hD : IsImaginaryQuadraticDiscriminant D) :
    Nonempty (ImaginaryQuadraticDiscriminantDecomposition D) := by
  obtain ⟨hneg, hmod⟩ := hD
  obtain ⟨a, b, ha0, hb0, hab, ha⟩ :=
    Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hneg.ne)
  -- `D = b ^ 2 * (-a)` with `-a` squarefree and negative
  have hDab : D = (b : ℤ) ^ 2 * (-(a : ℤ)) := by
    have h1 : ((D.natAbs : ℕ) : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hneg.le
    rw [← hab] at h1
    push_cast at h1
    linarith
  have hsq : Squarefree (-(a : ℤ)) := by
    rw [← Int.squarefree_natAbs]
    simpa using ha
  have hna : -(a : ℤ) < 0 := by omega
  -- a squarefree `a` is not divisible by `4`
  have ha4 : a % 4 ≠ 0 := by
    intro h
    have h4 : (2 : ℕ) * 2 ∣ a := Nat.dvd_of_mod_eq_zero h
    exact absurd (Nat.isUnit_iff.mp (ha 2 h4)) (by norm_num)
  rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
  · by_cases h3 : a % 4 = 3
    · -- `-a ≡ 1 (mod 4)`: `D = b ^ 2 * (-a)` is the decomposition
      exact ⟨.ofFundamental ((2 * k : ℕ) : ℤ) (-(a : ℤ)) (by omega)
        ⟨hna, Or.inl ⟨hsq, by omega⟩⟩ hDab⟩
    · -- `-a ≡ 2` or `3 (mod 4)`: `D = k ^ 2 * (4 * (-a))`
      exact ⟨.ofFundamental (k : ℤ) (4 * -(a : ℤ)) (by omega)
        ⟨by omega, Or.inr ⟨-(a : ℤ), rfl, hsq, by omega⟩⟩ (by rw [hDab]; push_cast; ring)⟩
  · -- `b` odd: `D ≡ -a (mod 4)`, so `-a ≡ 1 (mod 4)`
    have hD' : D = -(4 * (((k : ℤ) ^ 2 + k) * a) + a) := by
      rw [hDab]
      push_cast
      ring
    have h3 : a % 4 = 3 := by
      generalize ((k : ℤ) ^ 2 + k) * a = t at hD'
      omega
    exact ⟨.ofFundamental ((2 * k + 1 : ℕ) : ℤ) (-(a : ℤ)) (by omega)
      ⟨hna, Or.inl ⟨hsq, by omega⟩⟩ hDab⟩

end ImaginaryQuadraticDiscriminant
