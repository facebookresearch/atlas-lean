/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Morita's p-adic gamma function

This file defines the finite values interpolated by Morita's p-adic gamma function and a
specification for its continuous extension to the p-adic integers.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Morita's p-adic gamma values at natural numbers.** For a prime $p$ and a natural number
$n$, this is the $p$-adic integer $(-1)^n \prod_{0 < j < n,\ p \nmid j} j$: $(-1)^n$ times the
product of the positive integers below $n$ that are not divisible by $p$. At $n = 0$ the product is
empty and the value is $1$. These are the finite values that Morita's $p$-adic gamma function
interpolates. -/
noncomputable def moritaGammaNat (p n : ℕ) [Fact p.Prime] : PadicInt p :=
  (-1 : PadicInt p) ^ n *
    ∏ k ∈ (Finset.range n).filter (fun k => ¬p ∣ k), (k : PadicInt p)

@[simp]
theorem moritaGammaNat_zero (p : ℕ) [Fact p.Prime] :
    moritaGammaNat p 0 = 1 := by
  simp [moritaGammaNat]

/-- **Morita's p-adic gamma function.** For a prime $p$, a continuous function
$\Gamma : \mathbb{Z}_p \to \mathbb{Z}_p$ is a Morita $p$-adic gamma function when $\Gamma(0) = 1$,
$\Gamma(n)$ equals Morita's finite value $(-1)^n \prod_{0 < j < n,\ p \nmid j} j$ for every
positive integer $n$, and $\Gamma(x)$ is a unit of $\mathbb{Z}_p$ for every $x \in \mathbb{Z}_p$. -/
def IsMoritaPadicGamma (p : ℕ) [Fact p.Prime]
    (Γ : C(PadicInt p, PadicInt p)) : Prop :=
  Γ 0 = 1 ∧
    (∀ n : ℕ, 0 < n → Γ (n : PadicInt p) = moritaGammaNat p n) ∧
    ∀ x : PadicInt p, IsUnit (Γ x)

theorem IsMoritaPadicGamma.zero_eq {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ) :
    Γ 0 = 1 :=
  hΓ.1

theorem IsMoritaPadicGamma.natCast_eq {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ)
    {n : ℕ} (hn : 0 < n) : Γ (n : PadicInt p) = moritaGammaNat p n :=
  hΓ.2.1 n hn

theorem IsMoritaPadicGamma.isUnit {p : ℕ} [Fact p.Prime]
    {Γ : C(PadicInt p, PadicInt p)} (hΓ : IsMoritaPadicGamma p Γ)
    (x : PadicInt p) : IsUnit (Γ x) :=
  hΓ.2.2 x

end MetaMathlibExt
