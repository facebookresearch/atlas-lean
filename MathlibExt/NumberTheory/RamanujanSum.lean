/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun, Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Ramanujan sums

This file defines the classical Ramanujan sum using the standard additive character of `ZMod n`.

## Main definitions

* `MetaMathlibExt.ramanujanSum`

## Main statements

* `MetaMathlibExt.ramanujanSum_zero`
* `MetaMathlibExt.ramanujanSum_modulus_one`
* `MetaMathlibExt.ramanujanSum_add_mul_modulus`

## References

The definition follows the convention
`c_n(t) = ∑_{a ∈ (ZMod n)ˣ} e_n(a * t)`. Its Lean representation is adapted from the
Apache-2.0 licensed `ramanujanSum` declaration in
[UW Lean Pool](https://github.com/Vilin97/lean-pool), revision
`faa8c032722c955187fae103c96e8e93066f4592`, in `LeanPool.LatticeTriangle.Solution`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Ramanujan sum.** For a positive integer $n$ and an integer $t$, the Ramanujan sum of modulus
$n$ at $t$ is the complex number
$$c_n(t) = \sum_{a \in (\mathbb{Z}/n\mathbb{Z})^\times} e^{2\pi i a t / n},$$
the sum over the units $a$ modulo $n$ of the standard additive character of $\mathbb{Z}/n\mathbb{Z}$
evaluated at $a t$. -/
noncomputable def ramanujanSum (n : ℕ) [NeZero n] (t : ℤ) : ℂ :=
  ∑ a : (ZMod n)ˣ, ZMod.stdAddChar ((a : ZMod n) * (t : ZMod n))

/-- **Ramanujan sum at zero.** For every positive integer $n$, the Ramanujan sum $c_n(0)$ equals
Euler's totient $\varphi(n)$. -/
@[simp]
theorem ramanujanSum_zero (n : ℕ) [NeZero n] :
    ramanujanSum n 0 = Nat.totient n := by
  simp [ramanujanSum, ZMod.card_units_eq_totient]

/-- **Ramanujan sums of modulus one.** For every integer $t$, the Ramanujan sum $c_1(t)$ equals
$1$. -/
@[simp]
theorem ramanujanSum_modulus_one (t : ℤ) : ramanujanSum 1 t = 1 := by
  have ht : (t : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ramanujanSum, ht]

/-- **Periodicity of Ramanujan sums.** For every positive integer $n$ and all integers $t$ and $k$,
the Ramanujan sum $c_n$ of modulus $n$ satisfies $c_n(t + kn) = c_n(t)$. -/
@[simp]
theorem ramanujanSum_add_mul_modulus (n : ℕ) [NeZero n] (t k : ℤ) :
    ramanujanSum n (t + k * n) = ramanujanSum n t := by
  simp [ramanujanSum]

end MetaMathlibExt
