/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Order of the unitary group over a finite field
-/

open scoped BigOperators

namespace MetaMathlibExt

universe u v

/-- Let `F` be a field of order `q²` for a prime power `q`, with involution `a ↦ a ^ q`.
Let `h` be a nondegenerate Hermitian form on an `F`-vector space `W` of dimension `m ≥ 1`,
linear in its first argument. If `n` is the number of `F`-linear automorphisms of `W`
preserving `h`, then $n = q^{m(m-1)/2}\prod_{j=1}^m(q^j - (-1)^j)$ and
$q^{-m^2} n = \prod_{j=1}^m(1 - (-q)^{-j})$.

Source: M. Kirschmer, *Definite quadratic and hermitian forms with small class number*,
Habilitationsschrift (2016), Section 4.2, p. 53, the table after Lemma 4.2.5. -/
public theorem_wanted card_finiteUnitaryGroup
    (q : ℕ) (hq : IsPrimePow q) {F : Type u} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (hm : 1 ≤ Module.finrank F W) (h : W →ₗ[F] (W → F))
    (hHermitian : ∀ x y : W, h y x = h x y ^ q)
    (hNondegenerate : ∀ x : W, (∀ y : W, h x y = 0) → x = 0) :
    let m := Module.finrank F W
    let n := Nat.card {g : W ≃ₗ[F] W // ∀ x y : W, h (g x) (g y) = h x y}
    (n : ℤ) = (q : ℤ) ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 1 m, ((q : ℤ) ^ j - (-1) ^ j) ∧
      (q : ℚ) ^ (-((m : ℤ) ^ 2)) * (n : ℚ) =
        ∏ j ∈ Finset.Icc 1 m, (1 - (-(q : ℚ)) ^ (-(j : ℤ)))

end MetaMathlibExt
