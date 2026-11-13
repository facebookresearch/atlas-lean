/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 398, Analysis 399

/-!
# Ramanujan Sum in the Stirling-Ramanujan Setting; Stirling-Ramanujan Constant

## References

* The Stirling-Ramanujan constants are defined through these Euler-Maclaurin asymptotic expansions
  and interpreted as Ramanujan sums in: V. Munoz and R. Perez-Marco, Stirling-Ramanujan Constants
  Are Exponential Periods, Communications in Number Theory and Physics 18 (2024), 485--507. DOI:
  10.4310/CNTP.240904005850. https://arxiv.org/abs/2402.02660 (for `IsRamanujanSum`)
* This is the definition and natural extension of the Stirling-Ramanujan constants used in: V.
  Munoz and R. Perez-Marco, Stirling-Ramanujan Constants Are Exponential Periods, Communications
  in Number Theory and Physics 18 (2024), 485--507. DOI: 10.4310/CNTP.240904005850.
  https://arxiv.org/abs/2402.02660 (for `IsStirlingRamanujanConstant`)
-/

namespace MetaMathlibExt

-- Analysis 398: Ramanujan Sum in the Stirling-Ramanujan Setting

/-- Let a:ℕ→ℝ be a sequence. In the Euler-Maclaurin setting relevant to the Stirling-Ramanujan
constants, a real number S∈ℝ is the Ramanujan sum of a if there exist polynomials

A,B∈ℚ[s],   B(0)=0,

such that

∑ₖ₌₁ˢ a(k)=A(s)log s+B(s)+S+O(s⁻¹)

as s→+∞.

Thus S is the constant term remaining after the divergent polynomial and polynomial-logarithmic
terms have been removed.

This definition is tailored to the class of Euler-Maclaurin expansions occurring in the
Stirling-Ramanujan problem. It is not intended to formalize every possible version of Ramanujan
summation.
-/
def IsRamanujanSum
    (a : ℕ → ℝ)
    (S : ℝ) : Prop :=
  ∃ A B : Polynomial ℚ,
    B.coeff 0 = 0 ∧
    Asymptotics.IsBigO
      Filter.atTop
      (fun s : ℕ =>
        (∑ k ∈ Finset.Icc 1 s, a k) -
          Polynomial.eval₂
              (algebraMap ℚ ℝ) (s : ℝ) A *
            Real.log (s : ℝ) -
          Polynomial.eval₂
              (algebraMap ℚ ℝ) (s : ℝ) B -
          S)
      (fun s : ℕ => 1 / (s : ℝ))

-- Analysis 399: Stirling-Ramanujan Constant

/-- For n∈ℤ, a real number S is the n-th Stirling-Ramanujan constant if it is the Ramanujan sum of
the appropriate sequence.

For n≥0, the relevant sequence is

aₖ=kⁿlog k,

so
$$
S=\mathop{\mathcal R\sum}_{k\geq1} k^n\log k.
$$

For n<0, the natural completion of the family instead uses

aₖ=kⁿ,

so S is the constant term in the asymptotic expansion of

∑ₖ₌₁ˢ kⁿ.

In particular,

S₋₁=γ,

and, for n≤-2, one has

Sₙ=ζ(-n).
-/
def IsStirlingRamanujanConstant
    (n : ℤ)
    (S : ℝ) : Prop :=
  if 0 ≤ n then
    IsRamanujanSum
      (fun k : ℕ =>
        ((k : ℝ) ^ n.toNat) *
          Real.log (k : ℝ))
      S
  else
    IsRamanujanSum
      (fun k : ℕ =>
        (((k : ℝ) ^ n.natAbs)⁻¹))
      S

end MetaMathlibExt

end
