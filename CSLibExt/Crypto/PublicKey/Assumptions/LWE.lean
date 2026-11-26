/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Learning with errors

Regev's learning-with-errors (LWE) problems and the decision LWE assumption, as experiments
`PMF Bool` in the style of `CSLibExt.Crypto.Framework` and `CSLibExt.Crypto.PublicKey.Assumptions`:
every adversary is a deterministic function of its uniformly random coins in a finite nonempty
type `S`, a search problem is measured by the success probability `winProb`, and the decision
problem by the distinguishing `advantage`.

The parameters are the dimension `n`, the number of samples `m`, a modulus `q ≥ 1` (`NeZero q`)
and an error distribution `χ : PMF (ZMod q)`, a distribution on `ℤ_q` as in Regev, Section 2
(Peikert's error distribution on `ℤ` enters only through its reduction modulo `q`). The `m`
samples `(aᵢ, ⟨aᵢ, s⟩ + eᵢ)` are written as a matrix `A : Matrix (Fin m) (Fin n) (ZMod q)` whose
rows are the `aᵢ` and the vector `A *ᵥ s + e`, as in Regev, Section 1 (Peikert, Section 4.2.1,
takes the `aᵢ` as the columns of an `n × m` matrix instead).

* `lweErrors χ m`: the law `χᵐ` of an error vector in `ZMod q` with `m` independent entries,
  each distributed according to `χ`.
* `lweSearchGame χ F`, `lweSearchAdvantage`: the search problem (Peikert, Definition 4.2.2): for
  uniform `A`, a uniform secret `s` and `e ∼ χᵐ`, the solver `F` gets `(A, A *ᵥ s + e)` and wins
  when it outputs `s`.
* `lweReal χ D`, `lweRand D`, `lweAdvantage χ D`: the decision problem (Peikert,
  Definition 4.2.3): the distinguisher `D` gets `(A, A *ᵥ s + e)` in the real experiment and
  `(A, u)` for a uniform `u` in the random one, and its advantage is
  `|Pr[D = 1 | real] - Pr[D = 1 | random]|`.
* `DecisionLWE`: the decision LWE assumption for parameter families `m q : ℕ → ℕ` and `χ`
  indexed by the dimension `n`, with `m n` and `q n` bounded by polynomials in `n`: every
  admissible distinguisher family has negligible advantage, an instance of
  `Framework.AsymptoticallySecure`. The polynomial bounds are arguments that the definition does
  not use: they restrict it to the parameter families of Regev, Section 1.

**Efficiency.** As in `CSLibExt.Crypto.Framework.Asymptotic`, there is no model of probabilistic
polynomial-time algorithms on these types: the class `Admissible` of distinguisher families is a
parameter of `DecisionLWE`, as it is of `Framework.PubCPASecure`. In the sources the admissible
families are those computed by one probabilistic algorithm running in time polynomial in `n`.
`DecisionLWE` holds vacuously when no family is admissible; every distinguisher type is
nonempty (a constant distinguisher), so this depends on `Admissible` only.

## References

* O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*,
  J. ACM 56(6) (2009), Article 34, Sections 1 and 2.
* C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
  (2016), 283–424, Section 4.2.1.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.Assumptions

open Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFintype)
open scoped Matrix

variable {n m q : ℕ} [NeZero q] {S : Type*} [Fintype S] [Nonempty S]

/-- **LWE error distribution.** Let $q \ge 1$ and $m$ be natural numbers and let $\chi$ be a
probability distribution on $\mathbb{Z}_q = \mathbb{Z}/q\mathbb{Z}$. The error distribution
$\chi^m$ is the distribution of a vector $e \in \mathbb{Z}_q^m$ whose $m$ entries are independent
and each distributed according to $\chi$: it gives $e$ the probability
$\chi(e_1) \cdots \chi(e_m)$.

Source: O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*,
J. ACM 56(6) (2009), Article 34, Section 1; C. Peikert, *A decade of lattice cryptography*, Found.
Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Section 4.2.1. -/
noncomputable def lweErrors (χ : PMF (ZMod q)) (m : ℕ) : PMF (Fin m → ZMod q) :=
  PMF.ofFintype (fun e => ∏ i, χ (e i)) (by
    have h : ∑ x, χ x = 1 := by simpa [tsum_fintype] using χ.tsum_coe
    rw [← Fintype.prod_sum fun (_ : Fin m) x => χ x]
    simp [h])

/-- **Search LWE experiment.** Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a solver map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a vector in $\mathbb{Z}_q^n$. The search LWE experiment draws $A \in \mathbb{Z}_q^{m \times n}$,
the secret $s \in \mathbb{Z}_q^n$ and the coins uniformly and the error $e \in \mathbb{Z}_q^m$
from $\chi^m$, all independently, gives the solver $(A, As + e)$ and the coins, and outputs $1$
when the solver's output equals $s$.

Source: C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
(2016), 283–424, Definition 4.2.2, with the $m$ samples as the rows of $A$; O. Regev, *On
lattices, learning with errors, random linear codes, and cryptography*, J. ACM 56(6) (2009),
Article 34, Section 1. -/
noncomputable def lweSearchGame (χ : PMF (ZMod q))
    (F : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Fin n → ZMod q) : PMF Bool :=
  (uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q) × (Fin n → ZMod q) × S)).bind fun ω =>
    (lweErrors χ m).map fun e => decide (F ω.1 (ω.1 *ᵥ ω.2.1 + e) ω.2.2 = ω.2.1)

/-- **Search LWE advantage.** The search LWE advantage of a solver is its probability of
winning the search LWE experiment.

Source: C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
(2016), 283–424, Definition 4.2.2. -/
noncomputable def lweSearchAdvantage (χ : PMF (ZMod q))
    (F : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Fin n → ZMod q) : ℝ :=
  winProb (lweSearchGame χ F)

/-- **Real LWE experiment.** Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a distinguisher map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a bit. The real LWE experiment draws $A \in \mathbb{Z}_q^{m \times n}$, the secret
$s \in \mathbb{Z}_q^n$ and the coins uniformly and the error $e \in \mathbb{Z}_q^m$ from
$\chi^m$, all independently, and outputs the distinguisher's bit on $(A, As + e)$ and the coins.

Source: C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
(2016), 283–424, Definition 4.2.3, case (1). -/
noncomputable def lweReal (χ : PMF (ZMod q))
    (D : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Bool) : PMF Bool :=
  (uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q) × (Fin n → ZMod q) × S)).bind fun ω =>
    (lweErrors χ m).map fun e => D ω.1 (ω.1 *ᵥ ω.2.1 + e) ω.2.2

/-- **Random LWE experiment.** Let $n$ and $m$ be natural numbers and $q \ge 1$, and let a
distinguisher map a matrix in $\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins
in a finite nonempty set $S$ to a bit. The random LWE experiment draws
$A \in \mathbb{Z}_q^{m \times n}$, $u \in \mathbb{Z}_q^m$ and the coins uniformly and
independently, and outputs the distinguisher's bit on $(A, u)$ and the coins.

Source: C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
(2016), 283–424, Definition 4.2.3, case (2). -/
noncomputable def lweRand (D : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Bool) :
    PMF Bool :=
  (uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q) × S)).map fun ω =>
    D ω.1 ω.2.1 ω.2.2

/-- **Decision LWE advantage.** Let $n$ and $m$ be natural numbers, $q \ge 1$, and $\chi$ a
probability distribution on $\mathbb{Z}_q$, and let a distinguisher $D$ map a matrix in
$\mathbb{Z}_q^{m \times n}$, a vector in $\mathbb{Z}_q^m$ and coins in a finite nonempty set $S$
to a bit. Its decision LWE advantage is the real number
$|p_{\mathrm{real}} - p_{\mathrm{rand}}|$, where $p_{\mathrm{real}}$ and $p_{\mathrm{rand}}$ are
the probabilities that $D$ outputs $1$ in the real and in the random LWE experiment.

Source: C. Peikert, *A decade of lattice cryptography*, Found. Trends Theor. Comput. Sci. 10(4)
(2016), 283–424, Definition 4.2.3; O. Regev, *On lattices, learning with errors, random linear
codes, and cryptography*, J. ACM 56(6) (2009), Article 34, Section 2. -/
noncomputable def lweAdvantage (χ : PMF (ZMod q))
    (D : Matrix (Fin m) (Fin n) (ZMod q) → (Fin m → ZMod q) → S → Bool) : ℝ :=
  advantage (lweReal χ D) (lweRand D)

/-- **Decision learning-with-errors assumption.** Let $m$ and $q$ be functions of the dimension
$n$ bounded by polynomials in $n$, with $q(n) \ge 1$, and let $\chi_n$ be a probability
distribution on $\mathbb{Z}_{q(n)}$ for every $n$. A distinguisher $D$ in dimension $n$ maps a
matrix in $\mathbb{Z}_{q(n)}^{m(n) \times n}$, a vector in $\mathbb{Z}_{q(n)}^{m(n)}$ and coins in
a finite nonempty set $S_n$ to a bit, and its decision LWE advantage is
$|\Pr[D(A, As + e, c) = 1] - \Pr[D(A, u, c) = 1]|$, where $A \in \mathbb{Z}_{q(n)}^{m(n) \times n}$,
$s \in \mathbb{Z}_{q(n)}^n$, $u \in \mathbb{Z}_{q(n)}^{m(n)}$ and the coins $c \in S_n$ are uniform
and $e \in \mathbb{Z}_{q(n)}^{m(n)}$ is drawn from $\chi_n^{m(n)}$, all independently. Fix a class
of admissible distinguisher families, each giving one distinguisher $D_n$ for every $n$. The
decision LWE assumption holds for these parameters and this class when every admissible family
has negligible advantage $n \mapsto \mathrm{adv}(D_n)$. In the sources the admissible families
are those computed by one probabilistic algorithm running in time polynomial in $n$. The
assumption holds vacuously when no family is admissible.

Source: O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*,
J. ACM 56(6) (2009), Article 34, Sections 1 and 2; C. Peikert, *A decade of lattice
cryptography*, Found. Trends Theor. Comput. Sci. 10(4) (2016), 283–424, Definition 4.2.3. -/
@[nolint unusedArguments]
def DecisionLWE (m q : ℕ → ℕ) [∀ n, NeZero (q n)]
    (_hm : ∃ p : Polynomial ℕ, ∀ n, m n ≤ p.eval n) (_hq : ∃ p : Polynomial ℕ, ∀ n, q n ≤ p.eval n)
    (χ : (n : ℕ) → PMF (ZMod (q n))) (S : ℕ → Type*) [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    (Admissible : ((n : ℕ) → Matrix (Fin (m n)) (Fin n) (ZMod (q n)) → (Fin (m n) → ZMod (q n)) →
      S n → Bool) → Prop) : Prop :=
  AsymptoticallySecure (fun n D => lweAdvantage (χ n) D) Admissible

end Cslib.Crypto.PublicKey.Assumptions
