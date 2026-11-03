/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Goldreich-Levin: hardcore predicate from one-way permutations

Source:
O. Goldreich and L. A. Levin, "A hard-core predicate for all one-way functions",
Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989),
25-32.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevin

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Goldreich-Levin: hardcore predicate from one-way permutations

For a one-way permutation `π`, the inner product `⟨x, r⟩ = Σᵢ xᵢ · rᵢ (mod 2)` is a
*hardcore predicate* for the function `(x, r) ↦ (π x, r)`: no polynomial-size circuit can
predict `⟨x, r⟩` from `(π x, r)` with non-negligible advantage over `1 / 2`. Equivalently,
every one-way permutation has a hardcore bit, and one-way functions have hardcore
predicates. Circuits are non-uniform gate lists, as in the CVP file; the one-wayness
hypothesis is that every polynomial-size inverter family succeeds with negligible
probability (the canonical `Negligible` of the `Classes` file), and `π` itself is
computable by polynomial-size circuits (needed to test guesses inside the
Goldreich-Levin inverter).
-/

/-- **Serialized circuit gates.** A serialized gate is a pair $(k, r)$ of a natural number $k$, the
kind of the gate, and a list $r$ of natural numbers, its references.

These pairs are read through the shared (kind, references) encoding of gates of flat Boolean
circuits. -/
abbrev GLGate := ℕ × List ℕ

/-- **Gate values of a serialized circuit.** For a list $C = (g_0, \dots, g_{m-1})$ of serialized
gates and a list $a = (a_0, \dots, a_{n-1})$ of Booleans, the gate values of $C$ on $a$ are the
list of gate values of the flat Boolean circuit on $n$ inputs whose $j$-th gate is decoded from the
(kind, references) pair $g_j$, evaluated on the assignment that gives input $i$ the value $a_i$.

A pair $(0, [i])$ with $i \ge n$ decodes to the constant false, so an input index out of range
reads as false. -/
def glCircuitEval (C : List GLGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Outputs of a serialized circuit.** For a list $C$ of serialized gates, a list $a$ of Booleans
and a natural number $k$, the outputs of $C$ on $a$ are the last $k$ entries of the gate values of
$C$ on $a$, or all of them when $C$ has fewer than $k$ gates. -/
def glCircuitOutputs (C : List GLGate) (assign : List Bool) (k : ℕ) : List Bool :=
  let vals := glCircuitEval C assign
  vals.drop (vals.length - k)

/-- **Inversion success probability of a circuit.** For a list $C$ of serialized gates and a map
$\pi$ from $n$-bit strings to $n$-bit strings, the inversion success probability of $C$ against
$\pi$ is the rational number $N / 2^n$, where $N$ is the number of $n$-bit strings $x$ such that
the outputs of $C$ on input $\pi(x)$, taken as its last $n$ gate values, are exactly $x$. -/
noncomputable def invertSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {x | glCircuitOutputs C (List.ofFn (π x)) n = List.ofFn x} : ℚ) /
    (2 : ℚ) ^ n

/-- **Inner product modulo 2.** For $n$-bit strings $x$ and $r$, their inner product modulo 2 is
true if and only if the number of indices $i < n$ with $x_i$ and $r_i$ both true is odd, that is,
$\langle x, r \rangle = \sum_{i < n} x_i r_i \bmod 2$. -/
def xorDot {n : ℕ} (x r : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => x i && r i)).card % 2 = 1)

/-- **Concatenation of two bitstrings.** For $n$-bit strings $y$ and $r$, their concatenation is the
$2n$-bit string whose bit $i$ is $y_i$ for $i < n$ and $r_{i - n}$ for $n \le i < 2n$. -/
def glPair {n : ℕ} (y r : Fin n → Bool) : Fin (2 * n) → Bool :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩
    else r ⟨i.val - n, by
      have hi := i.isLt
      omega⟩

/-- **Prediction success probability for the inner-product bit.** For a list $C$ of serialized
gates and a map $\pi$ from $n$-bit strings to $n$-bit strings, the prediction success probability
of $C$ against $\pi$ is the rational number $N / 2^{2n}$, where $N$ is the number of pairs
$(x, r)$ of $n$-bit strings such that $C$ has at least one gate and the value of its last gate on
the concatenation of $\pi(x)$ and $r$, a $2n$-bit input, equals the inner product of $x$ and $r$
modulo 2. -/
noncomputable def predictSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin n → Bool) |
    (glCircuitEval C (List.ofFn (glPair (π p.1) p.2))).getLast? =
      some (xorDot p.1 p.2)} : ℚ) / (2 : ℚ) ^ (2 * n)

/-- **Goldreich-Levin: hardcore predicate from one-way permutations.** Let $\pi$ be a family of
bijections $\pi_n$ of the set of $n$-bit strings, one for each natural number $n$. Suppose that
$\pi$ is computable by polynomial-size circuits: there is a polynomial $q$ with natural number
coefficients such that for every $n$ some list of at most $q(n)$ serialized gates has, on every
$n$-bit string $x$, outputs (its last $n$ gate values) equal to $\pi_n(x)$. Suppose also that $\pi$
is one-way: for every polynomial $p$ with natural number coefficients and every family $(C_n)$ of
lists of serialized gates with at most $p(n)$ gates in $C_n$ for all $n$, the inversion success
probability of $C_n$ against $\pi_n$ is a negligible function of $n$. Then for every polynomial
$p$ with natural number coefficients and every family $(C'_n)$ of lists of serialized gates with
at most $p(n)$ gates in $C'_n$ for all $n$, the function $n \mapsto \max(0, s_n - 1/2)$ is
negligible, where $s_n$ is the prediction success probability of $C'_n$ against $\pi_n$ for the
inner product modulo 2.

Source: O.
Goldreich and L. A. Levin, "A hard-core predicate for all one-way functions",
Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989),
25-32. -/
public theorem_wanted goldreich_levin :
    ∀ (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool)),
    (∀ n, Function.Bijective (π n)) →
    (∃ pπ : Polynomial ℕ, ∀ n, ∃ Cπ : List GLGate, Cπ.length ≤ pπ.eval n ∧
      ∀ x, glCircuitOutputs Cπ (List.ofFn x) n = List.ofFn (π n x)) →
    (∀ (C : (n : ℕ) → List GLGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        Negligible (fun n => invertSucc (C n) (π n))) →
    ∀ (C' : (n : ℕ) → List GLGate) (p : Polynomial ℕ),
      (∀ n, (C' n).length ≤ p.eval n) →
        Negligible (fun n => max 0 (predictSucc (C' n) (π n) - 1 / 2))

end MetaMathlibExt.Complexity.KeyTheorems.GoldreichLevin
