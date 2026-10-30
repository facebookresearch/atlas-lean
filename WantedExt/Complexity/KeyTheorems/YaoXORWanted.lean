/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Yao's XOR lemma: hardness amplification by XOR

Source:
A. C. Yao, "Theory and applications of trapdoor functions", Proceedings of the Twenty-Third
Annual Symposium on Foundations of Computer Science (FOCS 1982), 80-91.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.YaoXOR

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Yao's XOR lemma: hardness amplification by XOR

If a Boolean function `f` on `n` bits is mildly hard for circuits of size `s` (no such
circuit agrees with `f` on more than a `1 - δ` fraction of inputs), then the XOR of `k`
independent copies of `f` is strongly hard: no circuit of size `s / (k + 1) ^ c` (for some
constant `c`, i.e. polynomial loss in `k`) agrees with `f ^ ⊕k` on more than
`1 / 2 + (1 - 2δ) ^ k / 2 + 1 / (k + 1)` of inputs. As `k` grows the advantage over
`1 / 2` decays like `(1 - 2δ) ^ k`. Circuits are non-uniform gate lists, as in the CVP
file; agreement is the fraction of inputs on which the circuit's last gate value equals
the function.
-/

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev XORGate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with input count `assign.length`.
The decode is semantics-preserving: out-of-range input indices read as `false`,
as in the previous local evaluator. -/
def xorCircuitEval (C : List XORGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- Flatten `k` blocks of `n` bits into one `n * k`-bit string. -/
def xorFlat {n k : ℕ} (hn : 0 < n) (xs : Fin k → Fin n → Bool) : Fin (n * k) → Bool :=
  fun i => xs ⟨i.val / n, by
      rw [Nat.div_lt_iff_lt_mul hn]
      calc i.val < n * k := i.isLt
        _ = k * n := by rw [Nat.mul_comm]⟩
    ⟨i.val % n, Nat.mod_lt _ hn⟩

/-- XOR of `k` bits: `true` iff an odd number are `true`. -/
def xorFold {k : ℕ} (b : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => b i)).card % 2 = 1)

/-- The XOR of `k` independent copies of `f`. -/
def xorOf {n k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin k → Fin n → Bool) : Bool :=
  xorFold (fun i => f (xs i))

/-- Agreement of a circuit with a function `g` on inputs encoded by `enc`: the fraction
of inputs on which the circuit's last gate value equals `g`. -/
noncomputable def agreement {α : Type*} [Fintype α]
    (C : List XORGate) (g : α → Bool) (enc : α → List Bool) : ℚ :=
  (Set.ncard {a | (xorCircuitEval C (enc a)).getLast? = some (g a)} : ℚ) /
    (Fintype.card α : ℚ)

/-- **Yao's XOR lemma: hardness amplification by XOR.** Source: A. C. Yao, "Theory and
applications of trapdoor functions", Proceedings of the Twenty-Third Annual Symposium on
Foundations of Computer Science (FOCS 1982), 80-91. -/
public theorem_wanted yao_xor_lemma :
    ∃ c : ℕ, ∀ (n k : ℕ) (hn : 1 ≤ n), ∀ (δ : ℚ), 0 < δ → δ ≤ 1 / 2 →
      ∀ f : (Fin n → Bool) → Bool, ∀ s : ℕ,
      (∀ C : List XORGate, C.length ≤ s →
        agreement C f List.ofFn ≤ 1 - δ) →
      ∀ C : List XORGate, C.length * (k + 1) ^ c ≤ s →
        agreement C (xorOf (k := k) f)
          (fun xs : Fin k → Fin n → Bool => List.ofFn (xorFlat (k := k) hn xs)) ≤
          1 / 2 + (1 - 2 * δ) ^ k / 2 + 1 / (k + 1 : ℚ)

end MetaMathlibExt.Complexity.KeyTheorems.YaoXOR
