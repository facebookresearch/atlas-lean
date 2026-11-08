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

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev FWGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with input count `assign.length`.
The decode is semantics-preserving: out-of-range input indices read as `false`,
as in the previous local evaluator. -/
def fwCircuitEval (C : List FWGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- The last `k` gate values of an encoded circuit on an assignment (its outputs). -/
def fwCircuitOutputs (C : List FWGate) (assign : List Bool) (k : ℕ) : List Bool :=
  let vals := fwCircuitEval C assign
  vals.drop (vals.length - k)

/-- Inversion success probability of a circuit `C` against a general one-way function
`f` with `n`-bit inputs: the fraction of inputs `x` for which the candidate preimage
`C (f x)` (read as an `n`-bit string) is a genuine preimage of `f x`. -/
noncomputable def fwInvertSucc {n : ℕ} (C : List FWGate)
    (f : (Fin n → Bool) → List Bool) : ℚ :=
  (Set.ncard {x | f (fun i => (fwCircuitOutputs C (f x) n).getD i.val false) = f x} : ℚ) /
    (2 : ℚ) ^ n

/-- One-way functions exist: a polynomially balanced family (`|f x| ≤ pOut n`), not
assumed injective and not assumed to land in `n`-bit strings, computed by a single
uniform polynomial-time evaluator on the encoded pair `(n, x)`, that no
polynomial-size inverter family inverts with non-negligible probability. The
uniform evaluator is essential: existential per-length polynomial-size circuits
would admit arbitrary noncomputable `P/poly` families, while the claimed implication
produces a language in the uniform class `NP`. The previous permutation-only version
(injective maps `Fin n → Bool` to itself) would have made `PKExists → OWFExists`
stronger than Impagliazzo's taxonomy. -/
def OWFExists : Prop :=
  ∃ f : (n : ℕ) → (Fin n → Bool) → List Bool, ∃ pOut : Polynomial ℕ,
  ∃ evalf : List Bool → List Bool, IsPolyTime evalf ∧
    (∀ n, ∀ x : Fin n → Bool, (f n x).length ≤ pOut.eval n) ∧
    (∀ n, ∀ x : Fin n → Bool,
      evalf (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn x)) = f n x) ∧
    ∀ (C : (n : ℕ) → List FWGate) (p : Polynomial ℕ),
      (∀ n, (C n).length ≤ p.eval n) →
        Negligible (fun n => fwInvertSucc (C n) (f n))

/-- A samplable distribution with polynomial coin count `p`: a sampler taking
`p.eval n` coins to an `n`-bit instance, computed by a single uniform
polynomial-time sampler on the encoded pair `(n, coins)`. The uniform sampler
is essential, as in `OWFExists`: per-length circuits would admit noncomputable
`P/poly` samplers. The coin count is a polynomial, not fixed at `n`: a
distribution assigning probability `2 ^ -(n + 1)` to one output is samplable
with `n + 1` coins but not from `n` uniform coins. -/
def Samplable (p : Polynomial ℕ)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  (∀ n r, (S n r).length = n) ∧
  ∃ samp : List Bool → List Bool, IsPolyTime samp ∧
    ∀ n r, samp (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn r)) = S n r

/-- `(L, S)` is easy on average: some polynomial-time algorithm's success probability
is at least `1 - 1 / (n ^ c + 1)` for every `c`, eventually (for all `n ≥ N`,
depending on `c`). The error bound must genuinely vanish: a single existential
polynomial `p` would be vacuous, since the zero polynomial gives the lower bound
`1 - 1 / (0 + 1) = 0`, which any algorithm meets. -/
def AvgEasy (p : Polynomial ℕ) (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  ∃ A : List Bool → Bool, IsPolyTime A ∧ ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 - 1 / ((n : ℚ) ^ c + 1) ≤
        (Set.ncard {r : Fin (p.eval n) → Bool | A (S n r) = L (S n r)} : ℚ) /
          (2 : ℚ) ^ (p.eval n)

/-- `(L, S)` is hard on average: it is *not* easy on average, in the sense of
`AvgEasy` above: no polynomial-time algorithm achieves negligible error. Hardness is defined as the logical
complement of easiness, with matching infinitely-often quantifiers: an error profile
that is zero on infinitely many lengths and inverse-polynomial on infinitely many
others satisfies neither an all-but-finitely-many inverse-polynomial bound nor
negligible error, so `¬ AvgEasy` is the faithful hardness notion, and failure of
Heuristica implies the Pessiland hard-on-average claim. -/
def AvgHard (p : Polynomial ℕ) (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool) : Prop :=
  ¬ AvgEasy p L S


/-- The key pair output by `keyGen` on coins, decoded from its bitstring encoding. -/
def fwKeyPair (keyGen : List Bool → List Bool) (coins : List Bool) :
    List Bool × List Bool :=
  (MetaMathlibExt.BitstringEncoding.bitDecode
    (α := List Bool × List Bool) (keyGen coins)).getD ([], [])

/-- Eavesdropper advantage of a nonuniform circuit adversary `C` against a public-key
scheme at length `n`: `|Pr[C(pk, Enc(pk, b)) = b] - 1/2|`, where `C`'s output bit is
its last gate value. The adversary model is the same nonuniform polynomial-size
circuit-family model as the OWF inverter in `OWFExists`: a uniform `IsPolyTime`
adversary for PK would not imply OWF security against nonuniform inverters. -/
noncomputable def fwPKAdv (keyGen enc : List Bool → List Bool)
    (C : List FWGate) (ℓ : Polynomial ℕ) (n : ℕ) : ℚ :=
  |(Set.ncard
      {q : (Fin (ℓ.eval n) → Bool) × (Fin (ℓ.eval n) → Bool) × Bool |
        (fwCircuitEval C (MetaMathlibExt.BitstringEncoding.bitEncode
          ((fwKeyPair keyGen (List.ofFn q.1)).1,
            enc (MetaMathlibExt.BitstringEncoding.bitEncode
              ((fwKeyPair keyGen (List.ofFn q.1)).1, [q.2.2], List.ofFn q.2.1))))).getLast? =
          some q.2.2} : ℚ) / (2 : ℚ) ^ (2 * ℓ.eval n + 1) - 1 / 2|

/-- Public-key cryptography exists: an eavesdropper-secure public-key encryption scheme
with all quantities padded to a common polynomial length. Security is negligible
advantage: for every inverse-polynomial bound `1 / n ^ c` the advantage is eventually
below it (a single existential polynomial bound would be vacuous, since the zero
polynomial gives the bound `1`, which every advantage satisfies). -/
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

/-- Algorithmica: `P = NP`. -/
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

/-- Pessiland: `P ≠ NP`, no one-way functions, but some NP problem is hard on average. -/
def Pessiland : Prop :=
  MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP ∧ ¬ OWFExists ∧
    ∃ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      ∃ (p : Polynomial ℕ) (S : (n : ℕ) → (Fin (p.eval n) → Bool) → List Bool),
        L ∈ MetaMathlibExt.ComplexityTheory.NP ∧ Samplable p S ∧ AvgHard p L S

/-- Minicrypt: one-way functions exist, but public-key cryptography does not. -/
def Minicrypt : Prop := OWFExists ∧ ¬ PKExists

/-- Cryptomania: public-key cryptography exists. -/
def Cryptomania : Prop := PKExists

/-- Exactly one of the five worlds holds. -/
def ExactlyOneWorld : Prop :=
  (Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ Pessiland ∧ ¬ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ Minicrypt ∧ ¬ Cryptomania) ∨
  (¬ Algorithmica ∧ ¬ Heuristica ∧ ¬ Pessiland ∧ ¬ Minicrypt ∧ Cryptomania)

/-- **Impagliazzo's five worlds.** Source: R. Impagliazzo, "A personal view of
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
