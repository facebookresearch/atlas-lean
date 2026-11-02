/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Chowla and twin primes conjectures over 𝔽_q[T]

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ChowlaAndTwinPrimeOverFqT` — annals_chowla_and_twin_prime_over_fq_t (manifest `manifests/problems/annals_chowla_and_twin_prime_over_fq_t.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ChowlaAndTwinPrimeOverFqTWanted` namespace. Mathematical
statements are unchanged. Source: W. Sawin and M. Shusterman, `On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-196-2-ChowlaAndTwinPrimeOverFqT.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

@[expose] public section

namespace MathlibExt.NumberTheory.ChowlaAndTwinPrimeOverFqTWanted
/-!
# Main Statements from On the Chowla and twin primes conjectures over 𝔽_q[T]

We formalise the statements of the main results from W. Sawin and M. Shusterman,
`On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022.
-/

set_option autoImplicit false

namespace ChowlaAndTwinPrimeOverFqT

open Submonoid UniqueFactorizationMonoid

open scoped Asymptotics Polynomial

variable {F : Type*} [Field F]

/-- **Size of the quotient of $F[T]$ by a nonzero polynomial.** Let $F$ be a field and let
$f \in F[T]$ be a nonzero polynomial. Then the cardinality of the quotient ring $F[T]/(f)$ is
$|F|^{\deg f}$, where cardinalities are natural numbers and an infinite set has cardinality $0$.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.1). -/
theorem cardQuot_span_eq_pow_natDegree {f : F[X]} (hf : f ≠ 0) :
    (Ideal.span {f}).cardQuot = Nat.card F ^ f.natDegree := by
  have : FiniteDimensional F (F[X] ⧸ Ideal.span {f}) := (AdjoinRoot.powerBasis hf).finite
  rw [Submodule.cardQuot_apply, ← finrank_quotient_span_eq_natDegree]
  exact Module.natCard_eq_pow_finrank

variable [Finite F]

/-- **The norm on $F[T]$.** Let $F$ be a finite field. The ring norm on the polynomial ring $F[T]$
sends $f$ to the number of elements of the quotient ring $F[T]/(f)$, written
$|f| = |F[T]/(f)|$; for $f = 0$ the quotient is infinite and $|0| = 0$. It is a ring norm: $|f| = 0$
only for $f = 0$, $|-f| = |f|$, $|f + g| \le |f| + |g|$ and $|fg| \le |f|\,|g|$.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.1). -/
noncomputable def ringNorm : RingNorm (F[X]) where
  toFun f := (Ideal.span {f}).cardQuot
  map_zero' := by simp
  add_le' f g := by
    norm_cast
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    by_cases hfg : f + g = 0
    · simp [hfg]
    grw [cardQuot_span_eq_pow_natDegree hf, cardQuot_span_eq_pow_natDegree hg,
      cardQuot_span_eq_pow_natDegree hfg, Polynomial.natDegree_add_le f g, max_def]
    · split_ifs
      · apply self_le_add_left
      · apply self_le_add_right
    · exact Nat.card_pos
  neg' := by simp
  mul_le' f g := by
    norm_cast
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    have hfg : f * g ≠ 0 := mul_ne_zero hf hg
    rw [cardQuot_span_eq_pow_natDegree hf, cardQuot_span_eq_pow_natDegree hg,
      cardQuot_span_eq_pow_natDegree hfg, Polynomial.natDegree_mul hf hg, pow_add]
  eq_zero_of_map_eq_zero' f hf := by
    contrapose! hf
    rw [cardQuot_span_eq_pow_natDegree hf, Nat.cast_ne_zero]
    exact pow_ne_zero _ Nat.card_pos.ne'

/-- The norm of `f ∈ F[T]` is defined to be `|F[T]/(f)|`; see Equation (1.1) in the paper. -/
noncomputable scoped instance : NormedCommRing (F[X]) where
  __ := ringNorm.toNormedRing
  mul_comm := mul_comm

/-- **The norm of a polynomial is the size of its quotient ring.** Let $F$ be a finite field and
give $F[T]$ its ring norm. For every $f \in F[T]$, the norm $|f|$ equals the number of elements of
the quotient ring $F[T]/(f)$, where an infinite quotient (the case $f = 0$) counts as $0$.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.1). -/
theorem norm_eq_cardQuot (f : F[X]) : ‖f‖ = (Ideal.span {f}).cardQuot := by
  rfl

/-- **Norm of a nonzero polynomial.** Let $F$ be a finite field and give $F[T]$ its ring norm.
For every nonzero $f \in F[T]$, the norm of $f$ is $|f| = |F|^{\deg f}$, where $|F|$ is the number
of elements of $F$.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.1). -/
theorem norm_eq_pow_natDegree {f : F[X]} (hf : f ≠ 0) : ‖f‖ = Nat.card F ^ f.natDegree := by
  rw [norm_eq_cardQuot, cardQuot_span_eq_pow_natDegree hf, Nat.cast_pow]

variable (F) in
/-- **Primes of $F[T]$.** Let $F$ be a finite field. The primes of the polynomial ring $F[T]$ are
its monic irreducible polynomials.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, the sentence after Equation (1.4). -/
def primes : Set F[X] :=
  {P : F[X] | P.Monic ∧ Irreducible P}

/-- The norm on `F[T]` can be applied to the primes of `F[T]`. -/
noncomputable instance : Norm (primes F) where
  norm := fun ⟨P, _, _⟩ ↦ ‖P‖

open Classical in
/-- **Indicator of a statement.** For a proposition $P$, the indicator $\mathbf{1}_P$ is the real
number $1$ if $P$ holds and $0$ otherwise.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.4). -/
noncomputable def indicator (pred : Prop) : ℝ := if pred then 1 else 0

open Classical in
/-- **Singular series for twin primes in $F[T]$.** Let $F$ be a finite field with $q$ elements and
let $h \in F[T]$. The Hardy–Littlewood constant of the prime pair $\{f, f + h\}$ is the infinite
product over all primes $P$ of $F[T]$ (the monic irreducible polynomials)
$$\mathfrak{S}_q(h) =
\prod_P \frac{1 - |P|^{-1} - |P|^{-1}\,\mathbf{1}_{P \nmid h}}{(1 - |P|^{-1})^2},$$
where $|P|$ is the norm of $P$ and $\mathbf{1}_{P \nmid h}$ is $1$ if $P$ does not divide $h$ and
$0$ otherwise.

The product is an unconditional infinite product of real numbers; when it does not converge its
value is taken to be $1$.

Source: W. Sawin and M. Shusterman, *On the Chowla and twin primes conjectures over
$\mathbb{F}_q[T]$*, Annals of Math. 196 (2) 2022, Equation (1.4). -/
noncomputable def 𝔖_q (h : F[X]) : ℝ :=
  ∏' P : primes F, (1 - ‖P‖⁻¹ - ‖P‖⁻¹ * indicator (¬ (P : F[X]) ∣ h)) / (1 - ‖P‖⁻¹) ^ 2

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- The cardinality of the finite field `𝔽_q`. -/
local notation "q" => p ^ n
/-- The finite field of cardinality `q`. -/
local notation "𝔽_q" => GaloisField p n

/--
**Twin prime asymptotic over $\mathbb{F}_q[T]$ for large $q$.** Let $p$ be an odd prime and let
$q$ be a power of $p$ with $q > 685090\,p^2$; write $\mathbb{F}_q$ for the finite field with $q$
elements. Then there is a real number $\varepsilon > 0$ such that for every nonzero
$h \in \mathbb{F}_q[T]$, as $X \to \infty$ through the powers of $q$,
$$\#\{f \in \mathbb{F}_q[T] : |f| = X,\ f \text{ and } f + h \text{ are prime}\} =
\frac{\mathfrak{S}_q(h)\, X}{(\log_q X)^2} + O\bigl(X^{1 - \varepsilon}\bigr),$$
where $|f| = |\mathbb{F}_q[T]/(f)|$ is the norm of $f$, the primes of $\mathbb{F}_q[T]$ are its
monic irreducible polynomials, $\mathfrak{S}_q(h)$ is the singular series for twin primes, and
the implied constant may depend on $h$ (but $\varepsilon$ does not).

Source: W. Sawin and M. Shusterman, `On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-196-2-ChowlaAndTwinPrimeOverFqT.lean Via leanprover/lean-eval@38361be, problem `annals_chowla_and_twin_prime_over_fq_t`.
-/
public theorem_wanted theorem_1_1 (hp : Odd p) (hq : q > 685090 * p ^ 2) :
    ∃ ε > (0 : ℝ), -- there exists a power saving such that ...
      ∀ h ≠ 0, (fun X : powers q ↦ Set.ncard {f | ‖f‖ = X ∧ f ∈ primes 𝔽_q ∧ f + h ∈ primes 𝔽_q} -
        𝔖_q h * X / (Real.logb q X) ^ 2) =O[Filter.atTop] (fun X : powers q ↦ (X : ℝ) ^ (1 - ε))

variable (F) in
/-- **Monic polynomials of bounded norm.** Let $F$ be a finite field and let $X$ be a real number.
This is the set of monic polynomials $f \in F[T]$ whose norm $|f| = |F[T]/(f)|$, the number of
elements of the quotient ring $F[T]/(f)$, satisfies $|f| \le X$. -/
def monicBounded (X : ℝ) : Set (F[X]) :=
  {f : F[X] | f.Monic ∧ ‖f‖ ≤ X}

/-- Euler's number `2.718...`. -/
local notation "e" => Real.exp 1

/--
**Chowla's conjecture over $\mathbb{F}_q[T]$ for large $q$.** Let $p$ be an odd prime, let $k \ge 1$
be a natural number, and let $q$ be a power of $p$ with $q > p^2 k^2 e^2$, where $e$ is Euler's
number; write $\mathbb{F}_q$ for the finite field with $q$ elements. Let
$h_1, \dots, h_k \in \mathbb{F}_q[T]$ be distinct polynomials. Then, as the real number $X$ tends
to $\infty$,
$$\sum_{f \text{ monic},\ |f| \le X} \mu(f + h_1)\,\mu(f + h_2) \cdots \mu(f + h_k) = o(X),$$
where the sum runs over the monic $f \in \mathbb{F}_q[T]$ of norm $|f| = |\mathbb{F}_q[T]/(f)|$ at
most $X$, and $\mu$ is the Möbius function of $\mathbb{F}_q[T]$: $\mu(g) = (-1)^r$ if $g$ is
squarefree with $r$ irreducible factors, and $\mu(g) = 0$ otherwise.

Source: W. Sawin and M. Shusterman, `On the Chowla and twin primes conjectures over 𝔽_q[T]`, Annals of Math, 196 (2) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-196-2-ChowlaAndTwinPrimeOverFqT.lean Via leanprover/lean-eval@38361be, problem `annals_chowla_and_twin_prime_over_fq_t`.
-/
public theorem_wanted theorem_1_3 (hp : Odd p) (k : ℕ) (hk : k ≥ 1) (hq : q > p ^ 2 * k ^ 2 * e ^ 2)
    (h : Fin k → 𝔽_q[X]) (h_distinct : Function.Injective h) :
    (fun X : ℝ ↦ ∑' f : monicBounded 𝔽_q X, ∏ i, moebius (f + h i)) =o[Filter.atTop] id

end ChowlaAndTwinPrimeOverFqT

end MathlibExt.NumberTheory.ChowlaAndTwinPrimeOverFqTWanted
