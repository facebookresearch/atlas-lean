/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Razborov-Rudich: the natural proofs barrier

Source:
A. A. Razborov and S. Rudich, "Natural proofs", Journal of Computer and System Sciences 55
(1997), 24-35 (Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing,
STOC 1994, 18-27).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Razborov-Rudich: the natural proofs barrier

A *natural property* is a property of Boolean functions that is constructive (decidable by
polynomial-size circuits given the truth table) and large (holding for at least a
`2 ^ (-c * n)` fraction of all `n`-bit functions). It is *useful* against `P/poly` if
every function family satisfying it infinitely often lies outside `P/poly`:
a family satisfying the property at infinitely many lengths but lying in
`P/poly` would contradict usefulness. Mere all-lengths usefulness would
not suffice for the Razborov-Rudich argument: a `P/poly` family could
satisfy the property at every sufficiently large length and fail once,
giving no contradiction with the asymptotic `PRFSecure` condition. A natural proof
of `P ≠ NP` would be a natural property useful against `P/poly` (in particular, one that
holds of an NP function). Razborov and Rudich showed that if pseudorandom function families
secure against polynomial-size truth-table distinguishers exist in `P/poly`, then no
natural property is useful against `P/poly`: the constructivity decider would
distinguish the pseudorandom family (none of whose members satisfies the property, by
usefulness) from a random function (which satisfies it with probability at least the
largeness density). So no natural proof can show `P ≠ NP`, or even superpolynomial
circuit lower bounds for a function in `P/poly`. The PRF here has key length `n ^ 2`,
quadratic in the input length `n`: with an `n`-bit key there are only `N = 2 ^ n`
functions in the family, and a nonuniform truth-table distinguisher of size `O(N ^ 2)`
could hardcode all of them and distinguish perfectly, so the assumption would be
impossible. With key length `n ^ 2` the family has `2 ^ (n ^ 2)` members, superpolynomial
in the truth-table size `2 ^ n`, and the assumption is the standard sufficiently strong
PRF assumption (it follows from subexponentially secure one-way functions).
-/

/-- **Encoded gates.** An encoded gate of a flat Boolean circuit is a pair $(k, r)$ of a natural
number $k$ (its kind) and a list $r$ of natural numbers (its references), in the shared encoding
of gates as (kind, references) pairs. -/
abbrev NPGate := ℕ × List ℕ

/-- **Evaluation of an encoded circuit.** Given a list of encoded gates $g_0, \dots, g_{m-1}$,
each a (kind, references) pair, and a list of Booleans $a = (a_0, \dots, a_{n-1})$, this is the
list of the values of all $m$ gates, in order: each pair is decoded to a gate of a flat Boolean
circuit on $n$ inputs, and the resulting circuit is evaluated with input $i$ set to $a_i$. An
input pair $(0, [i])$ with $i \ge n$ decodes to the constant false, so it reads as false. -/
def npCircuitEval (C : List NPGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Truth table.** The truth table of a Boolean function $g$ on $n$ bits is the list of the
$2^n$ values $g(x^{(0)}), g(x^{(1)}), \dots, g(x^{(2^n - 1)})$, where for $i < 2^n$ the input
$x^{(i)}$ has bit $j$ equal to the $j$-th binary digit $\lfloor i / 2^j \rfloor \bmod 2$ of $i$
(bit $0$ being the least significant), for every $j < n$. -/
def truthTable {n : ℕ} (g : (Fin n → Bool) → Bool) : List Bool :=
  List.ofFn (fun i : Fin (2 ^ n) =>
    g (fun j => decide ((i.val / 2 ^ j.val) % 2 = 1)))

/-- **Natural property.** Let $C = (C_n)_{n \in \mathbb{N}}$, where $C_n$ is a set of Boolean
functions on $n$ bits. Then $C$ is natural when it is constructive and large. Constructive: there
are a polynomial $q$ with natural-number coefficients and, for every $n$, a circuit given as a
list of at most $q(2^n)$ encoded gates, such that a Boolean function $g$ on $n$ bits lies in $C_n$
if and only if the evaluation of the circuit on the truth table of $g$ has last gate value true.
Large: there is a natural number $c$ such that $|C_n| \ge 2^{2^n} / 2^{cn}$ for every $n$, that is,
$C_n$ contains at least a $2^{-cn}$ fraction of the $2^{2^n}$ Boolean functions on $n$ bits. -/
def NaturalProperty (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  (∃ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) ∧
    ∀ n g, g ∈ C n ↔ D n (truthTable g) = true) ∧
  ∃ c : ℕ, ∀ n, ((2 ^ (2 ^ n) : ℕ) : ℚ) / (2 : ℚ) ^ (c * n) ≤ (Set.ncard (C n) : ℚ)

/-- **The decision problem of a family of Boolean functions.** For a family
$f = (f_n)_{n \in \mathbb{N}}$, where $f_n$ is a Boolean function on $n$ bits, this is the decision
problem that maps a bitstring $x = x_0 x_1 \cdots x_{n-1}$ of length $n$ to
$f_n(x_0, \dots, x_{n-1})$. -/
def langOfFamily (f : (n : ℕ) → (Fin n → Bool) → Bool) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => f x.length (fun i => x.getD i.val false)

/-- **Usefulness against P/poly.** Let $C = (C_n)_{n \in \mathbb{N}}$, where $C_n$ is a set of
Boolean functions on $n$ bits. Then $C$ is useful against P/poly when, for every family
$f = (f_n)_{n \in \mathbb{N}}$ of Boolean functions $f_n$ on $n$ bits such that $f_n \in C_n$ for
infinitely many $n$, the decision problem of $f$ is not in P/poly. Equivalently, if the decision
problem of a family $f$ is in P/poly, then $f_n \in C_n$ for only finitely many $n$. -/
def UsefulAgainstPPoly (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  ∀ f : (n : ℕ) → (Fin n → Bool) → Bool,
    Set.Infinite {n | f n ∈ C n} → langOfFamily f ∉ PPoly

/-- **Keyed function families in P/poly.** Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of
Boolean functions: $F_n(k, x)$ is a Boolean value for every key $k \in \{0,1\}^{n^2}$ and every
input $x \in \{0,1\}^n$. Then $F$ is in P/poly when there is a polynomial $p$ with natural-number
coefficients such that for every $n$ some circuit, given as a list of at most $p(n)$ encoded
gates, computes $F_n$: for all $k$ and $x$, the evaluation of the circuit on the bitstring $kx$ of
length $n^2 + n$ (the bits of $k$ followed by the bits of $x$) has last gate value $F_n(k, x)$. -/
def PRFInPPoly (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, ∃ Circ : List NPGate, Circ.length ≤ p.eval n ∧
    ∀ key input, (npCircuitEval Circ (List.ofFn key ++ List.ofFn input)).getLast? =
      some (F n key input)

/-- **Security of a keyed function family against truth-table distinguishers.** Let
$F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of Boolean functions: $F_n(k, x)$ is a Boolean
value for every key $k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. Write $F_{n,k}$ for the
Boolean function $x \mapsto F_n(k, x)$ on $n$ bits and $T(g)$ for the truth table of a Boolean
function $g$. Then $F$ is secure when the following holds for every polynomial $q$ with
natural-number coefficients and every sequence $(D_n)_{n \in \mathbb{N}}$ of functions from
bitstrings to Booleans such that, for each $n$, some circuit given as a list of at most $q(2^n)$
encoded gates has last gate value $D_n(t)$ on every bitstring $t$: for every natural number $c$
there is a natural number $N$ such that for every $n \ge N$

$$\left| \frac{|\{k \in \{0,1\}^{n^2} : D_n(T(F_{n,k})) = \mathrm{true}\}|}{2^{n^2}} -
\frac{|\{g : D_n(T(g)) = \mathrm{true}\}|}{2^{2^n}} \right| \le \frac{1}{2^{nc}},$$

where $g$ ranges over all $2^{2^n}$ Boolean functions on $n$ bits. That is, a distinguisher
computed by circuits of size polynomial in the truth-table size $2^n$ tells a uniformly random
member of the family from a uniformly random Boolean function with advantage at most $2^{-cn}$
for all large $n$, for every $c$. -/
def PRFSecure (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∀ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) →
    ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(Set.ncard {k : Fin (n ^ 2) → Bool | D n (truthTable (F n k)) = true} : ℚ) /
          (2 : ℚ) ^ (n ^ 2) -
        (Set.ncard {g : (Fin n → Bool) → Bool | D n (truthTable g) = true} : ℚ) /
          (2 : ℚ) ^ (2 ^ n)| ≤ 1 / (2 : ℚ) ^ (n * c)

/-- **Razborov-Rudich: the natural proofs barrier.** Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed
family of Boolean functions, where $F_n(k, x)$ is a Boolean value for every key
$k \in \{0,1\}^{n^2}$ and every input $x \in \{0,1\}^n$. If $F$ is in P/poly (computed by circuits
of size polynomial in $n$) and is secure against truth-table distinguishers, then there is no
property $C = (C_n)_{n \in \mathbb{N}}$, with $C_n$ a set of Boolean functions on $n$ bits, that
is both natural and useful against P/poly.

Source: A. A. Razborov and S. Rudich,
"Natural proofs", Journal of Computer and System Sciences 55 (1997), 24-35 (Proceedings of
the Twenty-Sixth Annual ACM Symposium on Theory of Computing, STOC 1994, 18-27). -/
public theorem_wanted razborov_rudich_natural_proofs :
    ∀ F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool,
      PRFInPPoly F → PRFSecure F →
        ¬ ∃ C : (n : ℕ) → Set ((Fin n → Bool) → Bool),
          NaturalProperty C ∧ UsefulAgainstPPoly C

end MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs
