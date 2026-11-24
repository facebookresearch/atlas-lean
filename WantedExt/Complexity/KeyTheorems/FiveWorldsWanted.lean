/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Impagliazzo's five worlds

Source:
R. Impagliazzo, "A personal view of average-case complexity", Proceedings of the Tenth
Annual Structure in Complexities Theory Conference (1995), 134-147.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.FiveWorlds

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Impagliazzo's five worlds

Impagliazzo's taxonomy of possible worlds, by which cryptographic and average-case
assumptions hold:

* Algorithmica: `P = NP`.
* Heuristica: `P ≠ NP`, but every NP problem is easy on average for every samplable
  distribution.
* Pessiland: `P ≠ NP`, no one-way functions exist, but some NP problem is hard on average
  for a samplable distribution.
* Minicrypt: one-way functions exist, but public-key cryptography does not.
* Cryptomania: public-key cryptography exists.

The five worlds are exactly one of them holds, and they are ordered by the implications
public-key cryptography ⇒ one-way functions ⇒ average-case-hard NP ⇒ `P ≠ NP`.
Public-key cryptography is formalized as eavesdropper-secure public-key encryption with
all keys, ciphertexts and randomness padded to a common polynomial length, secure
against nonuniform polynomial-size circuit adversaries, the same adversary model as
the OWF inverter; average-case hardness/easiness is against uniform polynomial-time
algorithms, with asymptotic gaps: hardness is an inverse-polynomial error lower
bound, easiness is success `1 - 1 / (n ^ c + 1)` for every `c`. A samplable
ensemble at length `n` may use `p(n)` random coins for a polynomial `p`
(`Samplable p S`, with coin count `p.eval n` and success probabilities over
`2 ^ (p.eval n)` coin strings): restricting samplers to exactly `n` coins
would be strictly narrower, since e.g. a distribution assigning probability
`2 ^ -(n + 1)` to one output is samplable with `n + 1` coins but not from
`n` uniform coins, whose event probabilities are multiples of `2 ^ -n`.
Negligibility (`Negligible`) is the canonical predicate of the `Classes` file.
-/

/-- **Serialized gates of five-worlds circuits.** A serialized gate of a flat Boolean circuit is a
pair $(k, r)$ of a natural number $k$ (the gate kind) and a list $r$ of natural numbers (its
references, depending on the kind: an input index, a constant bit, or indices of other gates), in
the shared encoding of gates as (kind, references) pairs. -/
abbrev FWGate := ℕ × List ℕ

/-- **Evaluation of an encoded flat circuit.** Let $C$ be a flat Boolean circuit given as a list
of gates, each encoded as a (kind, references) pair, and let $a = (a_0, \dots, a_{k-1})$ be a
list of booleans. The gate values of $C$ on $a$ are the gate values, in order, of the circuit on
$k$ inputs obtained by decoding each gate of $C$, evaluated on the assignment that sends input
$i$ to $a_i$.

Decoding turns an input variable $x_i$ with $i \ge k$ into the constant false. -/
def fwCircuitEval (C : List FWGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Outputs of an encoded flat circuit.** For an encoded flat Boolean circuit $C$, a list of
booleans $a$ and a natural number $k$, the outputs of $C$ on $a$ are the last $k$ entries of the
list of gate values of $C$ on $a$, or the whole list if $C$ has fewer than $k$ gates. -/
def fwCircuitOutputs (C : List FWGate) (assign : List Bool) (k : ℕ) : List Bool :=
  let vals := fwCircuitEval C assign
  vals.drop (vals.length - k)

/-- **Inversion success probability of a circuit.** Let $f$ map $n$-bit strings to bitstrings
and let $C$ be an encoded flat Boolean circuit. For an $n$-bit string $x$, the candidate preimage
$x'$ consists of the last $n$ gate values of $C$ on input $f(x)$ (all of them if $C$ has fewer
than $n$ gates), padded with false to length $n$. The inversion success probability of $C$
against $f$ is the fraction of the $2^n$ strings $x$ for which $f(x') = f(x)$. -/
noncomputable def fwInvertSucc {n : ℕ} (C : List FWGate)
    (f : (Fin n → Bool) → List Bool) : ℚ :=
  (Set.ncard {x | f (fun i => (fwCircuitOutputs C (f x) n).getD i.val false) = f x} : ℚ) /
    (2 : ℚ) ^ n

/-- **One-way functions exist.** There are a family of functions $f_n$, each mapping $n$-bit strings
to bitstrings, and a polynomial $q$ with natural-number coefficients such that the following hold:
$|f_n(x)| \le q(n)$ for every $n$ and every $n$-bit string $x$; some polynomial-time computable
function on bitstrings maps the canonical bitstring encoding of every pair $(n, x)$ to $f_n(x)$;
and for every family of flat Boolean circuits $C_n$, given as lists of serialized gates, with at
most $p(n)$ gates for some polynomial $p$ with natural-number coefficients, the fraction of
$n$-bit strings $x$ with $f_n(x') = f_n(x)$ is a negligible function of $n$. Here $x'$ is the
$n$-bit string whose $i$-th bit is the $i$-th of the last $n$ gate values of $C_n$ on input
$f_n(x)$, or false when there is no such value.

The functions need not be injective, and they are computed by a single uniform polynomial-time
algorithm: per-length polynomial-size circuits would admit noncomputable $\mathsf{P/poly}$
families. -/
def OWFExists : Prop :=
  ∃ f : (n : ℕ) → (Fin n → Bool) → List Bool, ∃ pOut : Polynomial ℕ,
  ∃ evalf : List Bool → List Bool, IsPolyTime evalf ∧
    (∀ n, ∀ x : Fin n → Bool, (f n x).length ≤ pOut.eval n) ∧
    (∀ n, ∀ x : Fin n → Bool,
      evalf (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn x)) = f n x) ∧
    ∀ (C : (n : ℕ) → List FWGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        Negligible (fun n => fwInvertSucc (C n) (f n))

/-- **Samplable distributions.** Let $p$ be a polynomial with natural-number coefficients and let
$S$ be a family of maps $S_n$ from $p(n)$-bit coin strings to bitstrings. The pair $(p, S)$ is
samplable when every $S_n(r)$ has length exactly $n$ and some polynomial-time computable function
on bitstrings maps the canonical bitstring encoding of every pair $(n, r)$ to $S_n(r)$.

The distribution sampled at length $n$ is that of $S_n(r)$ for a uniformly random coin string
$r$. The sampler is a single uniform polynomial-time algorithm: per-length circuits would admit
noncomputable $\mathsf{P/poly}$ samplers. The coin count is a polynomial rather than $n$: a
distribution giving probability $2^{-(n+1)}$ to one output is samplable with $n + 1$ coins but
not from $n$ uniform coins. -/
def Samplable (p : Polynomial ℕ)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  (∀ n r, (S n r).length = n) ∧
  ∃ samp : List Bool → List Bool, IsPolyTime samp ∧
    ∀ n r, samp (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn r)) = S n r

/-- **Easy on average.** Let $p$ be a polynomial with natural-number coefficients, $L$ a
decision problem, and $S$ a family of samplers, where $S_n$ sends each string $r$ of $p(n)$
random bits to a bitstring $S_n(r)$. The pair $(L, S)$ is easy on average when there is a
polynomial-time computable function $A$ from bitstrings to booleans such that for every natural
number $c$ there is $N$ such that for all $n \ge N$
$$1 - \frac{1}{n^c + 1} \le \frac{\#\{r \in \{0,1\}^{p(n)} : A(S_n(r)) = L(S_n(r))\}}{2^{p(n)}},$$
that is, $A$ agrees with $L$ on $S_n(r)$ for at least a fraction $1 - 1/(n^c + 1)$ of the
coin strings $r$.

The algorithm $A$ does not depend on $c$, so its error is negligible. Requiring the bound
$1 - 1/(q(n) + 1)$ for a single polynomial $q$ instead would be vacuous: the zero polynomial
gives the lower bound $0$, which every algorithm meets. -/
def AvgEasy (p : Polynomial ℕ) (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  ∃ A : List Bool → Bool, IsPolyTime A ∧ ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 - 1 / ((n : ℚ) ^ c + 1) ≤
        (Set.ncard {r : Fin (p.eval n) → Bool | A (S n r) = L (S n r)} : ℚ) /
          (2 : ℚ) ^ (p.eval n)

/-- **Hard on average.** Let $p$ be a polynomial with natural-number coefficients, $L$ a
decision problem, and $S$ a family of samplers, where $S_n$ sends each string $r$ of $p(n)$
random bits to a bitstring $S_n(r)$. The pair $(L, S)$ is hard on average when it is not easy
on average: there is no polynomial-time computable function $A$ from bitstrings to booleans
such that for every natural number $c$ and all sufficiently large $n$, $A$ agrees with $L$ on
$S_n(r)$ for at least a fraction $1 - 1/(n^c + 1)$ of the $2^{p(n)}$ coin strings $r$.

Since hardness is the logical complement of easiness, if $\mathrm{P} \ne \mathrm{NP}$ and
Heuristica fails, then some NP problem is hard on average for some samplable ensemble. -/
def AvgHard (p : Polynomial ℕ) (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  ¬ AvgEasy p L S


/-- **Key pair produced by a key generator.** For a map $G$ from bitstrings to bitstrings (the key
generator) and a bitstring $r$ of coins, the key pair of $G$ on $r$ is the pair of bitstrings
obtained by decoding $G(r)$ with the canonical bitstring encoding of pairs of bitstrings, or the
pair of empty bitstrings if this decoding fails. -/
def fwKeyPair (keyGen : List Bool → List Bool) (coins : List Bool) :
    List Bool × List Bool :=
  (MetaMathlibExt.BitstringEncoding.bitDecode
    (α := List Bool × List Bool) (keyGen coins)).getD ([], [])

/-- **Eavesdropping advantage against a public-key scheme.** Let $G$ (key generation) and $E$
(encryption) be maps from bitstrings to bitstrings, let $C$ be an encoded flat Boolean circuit,
let $\ell$ be a polynomial with natural-number coefficients and let $n$ be a natural number. For
key coins $r$ and encryption coins $s$, each a string of $\ell(n)$ bits, and a bit $b$, let $pk$
be the first component of the key pair of $G$ on $r$, and let the ciphertext $e$ be $E$ applied
to the bitstring encoding of the triple $(pk, (b), s)$, where $(b)$ is the one-bit list. The
circuit $C$ succeeds on $(r, s, b)$ when it has a last gate value on the bitstring encoding of
the pair $(pk, e)$ and that value equals $b$. If $N$ is the number of triples $(r, s, b)$ on
which $C$ succeeds, the advantage of $C$ at length $n$ is $|N / 2^{2\ell(n) + 1} - 1/2|$. -/
noncomputable def fwPKAdv (keyGen enc : List Bool → List Bool)
    (C : List FWGate) (ℓ : Polynomial ℕ) (n : ℕ) : ℚ :=
  |(Set.ncard
      {q : (Fin (ℓ.eval n) → Bool) × (Fin (ℓ.eval n) → Bool) × Bool |
        (fwCircuitEval C (MetaMathlibExt.BitstringEncoding.bitEncode
          ((fwKeyPair keyGen (List.ofFn q.1)).1,
            enc (MetaMathlibExt.BitstringEncoding.bitEncode
              ((fwKeyPair keyGen (List.ofFn q.1)).1, [q.2.2], List.ofFn q.2.1))))).getLast? =
          some q.2.2} : ℚ) / (2 : ℚ) ^ (2 * ℓ.eval n + 1) - 1 / 2|

/-- **Public-key encryption exists.** There are a polynomial $\ell$ with natural-number
coefficients and polynomial-time computable functions $G$ (key generation), $E$ (encryption) and
$D$ (decryption) on bitstrings with the following two properties. Here tuples are passed to
these functions and to circuits through their canonical bitstring encodings, and for a bitstring
$r$ the keys $(\mathit{pk}, \mathit{sk})$ are the decoding of $G(r)$ as a pair of bitstrings,
both empty when decoding fails. Correctness: for every $n$, all bitstrings $r$ and $s$ of length
$\ell(n)$ and every bit $b$, $D(\mathit{sk}, E(\mathit{pk}, [b], s)) = [b]$. Security: for every
family of flat Boolean circuits $C_n$, given as lists of serialized gates, with at most $p(n)$
gates for some polynomial $p$ with natural-number coefficients, and for every natural number
$c$, the advantage of $C_n$ is at most $1 / n^c$ for all sufficiently large $n$. The advantage
of $C_n$ is $|P_n - 1/2|$, where $P_n$ is the fraction of triples $(r, s, b)$ of bitstrings $r$
and $s$ of length $\ell(n)$ and a bit $b$ for which the last gate value of $C_n$ on input
$(\mathit{pk}, E(\mathit{pk}, [b], s))$ is $b$. -/
def PKExists : Prop :=
  ∃ (ℓ : Polynomial ℕ) (keyGen enc dec : List Bool → List Bool),
    IsPolyTime keyGen ∧ IsPolyTime enc ∧ IsPolyTime dec ∧
    (∀ n (keyCoins : List Bool), keyCoins.length = ℓ.eval n →
      ∀ (b : Bool) (encCoins : List Bool), encCoins.length = ℓ.eval n →
        dec (MetaMathlibExt.BitstringEncoding.bitEncode
          ((fwKeyPair keyGen keyCoins).2,
            enc (MetaMathlibExt.BitstringEncoding.bitEncode
              ((fwKeyPair keyGen keyCoins).1, [b], encCoins)))) = [b]) ∧
    ∀ (C : (n : ℕ) → List FWGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ,
          N ≤ n → fwPKAdv keyGen enc (C n) ℓ n ≤ 1 / (n : ℚ) ^ c

/-- **Algorithmica.** Algorithmica is the statement that the complexity classes $\mathrm{P}$ and
$\mathrm{NP}$ are equal. -/
def Algorithmica : Prop :=
  MetaMathlibExt.ComplexityTheory.P = MetaMathlibExt.ComplexityTheory.NP

/-- Heuristica: `P ≠ NP`, but every NP problem is easy on average for every samplable
distribution. -/
def Heuristica : Prop :=
  MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP ∧
    ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ MetaMathlibExt.ComplexityTheory.NP →
        ∀ (p : Polynomial ℕ) (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool),
          Samplable p S → AvgEasy p L S

/-- **Pessiland.** Pessiland is the statement that $\mathsf{P} \ne \mathsf{NP}$, that one-way
functions do not exist, and that some decision problem $L$ in NP is hard on average for some
samplable distribution: there are a polynomial $p$ with natural-number coefficients and a family
$S$ of maps $S_n$ from $p(n)$-bit coin strings to bitstrings such that $(p, S)$ is samplable and
$L$ is hard on average with respect to $S$. -/
def Pessiland : Prop :=
  MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP ∧ ¬ OWFExists ∧
    ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      ∃ (p : Polynomial ℕ) (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool),
        L ∈ MetaMathlibExt.ComplexityTheory.NP ∧ Samplable p S ∧ AvgHard p L S

/-- Minicrypt: one-way functions exist, but public-key cryptography does not. -/
def Minicrypt : Prop := OWFExists ∧ ¬ PKExists

/-- **Cryptomania.** Cryptomania is the statement that public-key cryptography exists: there
are a polynomial $\ell$ with natural-number coefficients and polynomial-time computable maps
$G$ (key generation), $E$ (encryption) and $D$ (decryption) from bitstrings to bitstrings with
the following two properties. First, decryption is correct: for every natural number $n$, all
key coins $r$ and encryption coins $s$ that are bitstrings of length $\ell(n)$, and every bit
$b$, if $(pk, sk)$ is the key pair of $G$ on $r$ and the ciphertext $e$ is $E$ applied to the
bitstring encoding of the triple $(pk, (b), s)$, where $(b)$ is the one-bit list, then $D$
applied to the bitstring encoding of the pair $(sk, e)$ is $(b)$. Second, the scheme is secure:
for every family $(C_n)$ of encoded flat Boolean circuits and every polynomial $q$ with
natural-number coefficients such that each $C_n$ has at most $q(n)$ gates, and for every natural
number $c$, there is $N$ such that for all $n \ge N$ the eavesdropping advantage of $C_n$
against $(G, E)$ with polynomial $\ell$ at length $n$ is at most $1/n^c$. -/
def Cryptomania : Prop := PKExists

/-- **Exactly one of Impagliazzo's five worlds holds.** Exactly one of the statements
Algorithmica, Heuristica, Pessiland, Minicrypt and Cryptomania is true: one of them holds and
the other four fail. -/
def ExactlyOneWorld : Prop :=
  (Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ Cryptomania)

/-- **Impagliazzo's five worlds.** The following four statements hold. First, if public-key
encryption exists, then one-way functions exist. Second, if one-way functions exist, then some
decision problem $L$ in NP is hard on average for some samplable distribution: there are a
polynomial $p$ with natural-number coefficients and a family $S$ of maps $S_n$ from $p(n)$-bit
coin strings to bitstrings such that $(p, S)$ is samplable and $L$ is hard on average with
respect to $S$. Third, if some decision problem in NP is hard on average for some samplable
distribution in this sense, then $\mathsf{P} \ne \mathsf{NP}$. Fourth, exactly one of the five
worlds Algorithmica, Heuristica, Pessiland, Minicrypt and Cryptomania holds.

Source: R. Impagliazzo, "A personal view of
average-case complexity", Proceedings of the Tenth Annual Structure in Complexities
Theory Conference (1995), 134-147. -/
public theorem_wanted impagliazzo_five_worlds :
    (PKExists → OWFExists) ∧
    (OWFExists → ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      ∃ (p : Polynomial ℕ) (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool),
        L ∈ MetaMathlibExt.ComplexityTheory.NP ∧ Samplable p S ∧ AvgHard p L S) ∧
    ((∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      ∃ (p : Polynomial ℕ) (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool),
        L ∈ MetaMathlibExt.ComplexityTheory.NP ∧ Samplable p S ∧ AvgHard p L S) →
      MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP) ∧
    ExactlyOneWorld

end MetaMathlibExt.Complexity.KeyTheorems.FiveWorlds
