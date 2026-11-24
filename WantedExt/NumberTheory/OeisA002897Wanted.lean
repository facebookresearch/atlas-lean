/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
# OEIS A002897
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA002897Wanted

/-! Source record `FC-OeisA002897`, ported from FormalConjectures
`OEIS/2897.lean` and checked against oeis.org/A002897. Cubed central
binomial coefficients; `AddMonoidAlgebra.coeff` is Mathlib's. Test
evaluations omitted (proofs live upstream). Status: resolved true. -/

/-- **Cubed central binomial coefficients.** For a natural number $n$, $a(n) = \binom{2n}{n}^3$. -/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

/-- **Indices for three variables.** Three polynomial variables are indexed by the set
$\{0, 1, 2\}$. -/
abbrev Vars := Fin 3

/-- **Exponent vector of $x^n y^n z^n$.** For a natural number $n$, the exponent vector assigning
exponent $n$ to each of the three variables $x, y, z$, that is, the monomial $x^n y^n z^n$. -/
noncomputable def xyzPowN (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

local notation "P" => MvPolynomial Vars ℤ

/-- **Product polynomial for the cubed central binomial coefficients.** For a natural number $n$,
this is the polynomial $(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three
variables $x, y, z$ (indexed by $0, 1, 2$) with integer coefficients. -/
noncomputable def pPoly (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

/-- **Diagonal-coefficient property of the cubed central binomial coefficients.** This is the
proposition that for every natural number $n$, the coefficient of $x^n y^n z^n$ in the
polynomial $(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three variables
$x, y, z$ with integer coefficients equals $\binom{2n}{n}^3$. -/
def a_eq_coeff : Prop :=
  ∀ (n : ℕ), (a n : ℤ) = AddMonoidAlgebra.coeff (pPoly n) (xyzPowN n)

/--
**Cubed central binomial coefficients as diagonal coefficients.** For every natural number $n$,
the coefficient of $x^n y^n z^n$ in the polynomial
$(1 + x + y + z)^{2n} (1 + x + y - z)^n (1 + x - y + z)^n$ in three variables $x, y, z$ with
integer coefficients equals $\binom{2n}{n}^3$.

Source: Formal proof of the A002897 diagonal-coefficient identity
(methods of Tsoukalas et al. [arXiv/2605.22763]),
https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/2897.wip.lean#L408.
Moved from `OpenConjectures/NumberTheory/OeisA002897`.
-/
public theorem_wanted a_eq_coeff_holds : a_eq_coeff

end MathlibExt.NumberTheory.OeisA002897Wanted
