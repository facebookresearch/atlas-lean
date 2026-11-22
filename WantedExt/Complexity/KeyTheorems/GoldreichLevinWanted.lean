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

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev GLGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with input count `assign.length`.
The decode is semantics-preserving: out-of-range input indices read as `false`,
as in the previous local evaluator. -/
def glCircuitEval (C : List GLGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- The last `k` gate values of an encoded circuit on an assignment (its outputs). -/
def glCircuitOutputs (C : List GLGate) (assign : List Bool) (k : ℕ) : List Bool :=
  let vals := glCircuitEval C assign
  vals.drop (vals.length - k)

/-- Inversion success probability of a circuit `C` against a permutation `π`:
the fraction of `x` for which `C` recovers `x` from `π x`. -/
noncomputable def invertSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {x | glCircuitOutputs C (List.ofFn (π x)) n = List.ofFn x} : ℚ) /
    (2 : ℚ) ^ n

/-- Inner product mod 2 of two bitstrings. -/
def xorDot {n : ℕ} (x r : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => x i && r i)).card % 2 = 1)

/-- Pair two `n`-bit strings into one `2 * n`-bit string. -/
def glPair {n : ℕ} (y r : Fin n → Bool) : Fin (2 * n) → Bool :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩
    else r ⟨i.val - n, by
      have hi := i.isLt
      omega⟩

/-- Prediction success probability of a circuit `C` for the inner-product predicate
`⟨x, r⟩` given `(π x, r)`. -/
noncomputable def predictSucc {n : ℕ} (C : List GLGate)
    (π : (Fin n → Bool) → (Fin n → Bool)) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin n → Bool) |
    (glCircuitEval C (List.ofFn (glPair (π p.1) p.2))).getLast? =
      some (xorDot p.1 p.2)} : ℚ) / (2 : ℚ) ^ (2 * n)

/-- **Goldreich-Levin: hardcore predicate from one-way permutations.** Source: O.
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
