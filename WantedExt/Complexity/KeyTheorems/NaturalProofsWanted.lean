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

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev NPGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with input count `assign.length`.
The decode is semantics-preserving: out-of-range input indices read as `false`,
as in the previous local evaluator. -/
def npCircuitEval (C : List NPGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- The truth table of a Boolean function on `n` bits, indexed by binary counting. -/
def truthTable {n : ℕ} (g : (Fin n → Bool) → Bool) : List Bool :=
  List.ofFn (fun i : Fin (2 ^ n) =>
    g (fun j => decide ((i.val / 2 ^ j.val) % 2 = 1)))

/-- A natural property: constructive (decidable by polynomial-size circuits on truth
tables) and large (density at least `2 ^ (-c * n)`). -/
def NaturalProperty (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  (∃ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) ∧
    ∀ n g, g ∈ C n ↔ D n (truthTable g) = true) ∧
  ∃ c : ℕ, ∀ n, ((2 ^ (2 ^ n) : ℕ) : ℚ) / (2 : ℚ) ^ (c * n) ≤ (Set.ncard (C n) : ℚ)

/-- The decision problem of a family of Boolean functions, on bitstring inputs. -/
def langOfFamily (f : (n : ℕ) → (Fin n → Bool) → Bool) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x => f x.length (fun i => x.getD i.val false)

/-- A property is useful against `P/poly` if every family satisfying it
infinitely often lies outside `P/poly`: `Set.Infinite {n | f n ∈ C n}`
implies the family's language is not in `P/poly`. Equivalently, a `P/poly`
family can satisfy a useful property at only finitely many lengths. -/
def UsefulAgainstPPoly (C : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Prop :=
  ∀ f : (n : ℕ) → (Fin n → Bool) → Bool,
    Set.Infinite {n | f n ∈ C n} → langOfFamily f ∉ PPoly

/-- A pseudorandom function family in `P/poly`: a keyed family computable by
polynomial-size circuits. The key has `n ^ 2` bits and the input `n` bits. -/
def PRFInPPoly (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, ∃ Circ : List NPGate, Circ.length ≤ p.eval n ∧
    ∀ key input, (npCircuitEval Circ (List.ofFn key ++ List.ofFn input)).getLast? =
      some (F n key input)

/-- A pseudorandom function family secure against polynomial-size truth-table
distinguishers: no such distinguisher separates the family from a random function by a
non-negligible advantage (negligible in the input length `n`). Keys are drawn from
`Fin (n ^ 2) → Bool`, so the first fraction is over `2 ^ (n ^ 2)` keys. -/
def PRFSecure (F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool) : Prop :=
  ∀ (D : (n : ℕ) → List Bool → Bool) (q : Polynomial ℕ),
    (∀ n, ∃ Circ : List NPGate, Circ.length ≤ q.eval (2 ^ n) ∧
      ∀ t, (npCircuitEval Circ t).getLast? = some (D n t)) →
    ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(Set.ncard {k : Fin (n ^ 2) → Bool | D n (truthTable (F n k)) = true} : ℚ) /
          (2 : ℚ) ^ (n ^ 2) -
        (Set.ncard {g : (Fin n → Bool) → Bool | D n (truthTable g) = true} : ℚ) /
          (2 : ℚ) ^ (2 ^ n)| ≤ 1 / (2 : ℚ) ^ (n * c)

/-- **Razborov-Rudich: the natural proofs barrier.** Source: A. A. Razborov and S. Rudich,
"Natural proofs", Journal of Computer and System Sciences 55 (1997), 24-35 (Proceedings of
the Twenty-Sixth Annual ACM Symposium on Theory of Computing, STOC 1994, 18-27). -/
public theorem_wanted razborov_rudich_natural_proofs :
    ∀ F : (n : ℕ) → (Fin (n ^ 2) → Bool) → (Fin n → Bool) → Bool,
      PRFInPPoly F → PRFSecure F →
        ¬ ∃ C : (n : ℕ) → Set ((Fin n → Bool) → Bool),
          NaturalProperty C ∧ UsefulAgainstPPoly C

end MetaMathlibExt.Complexity.KeyTheorems.NaturalProofs
