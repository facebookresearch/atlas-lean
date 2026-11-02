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

/-- **Encoded gates.** An encoded gate is a pair $(k, r)$ of a natural number $k$ (the gate kind)
and a list $r$ of natural numbers (its references), the shared (kind, references) encoding of
gates of flat Boolean circuits. -/
abbrev XORGate := ℕ × List ℕ

/-- **Gate values of an encoded circuit.** For a list $C$ of encoded gates and a list $x$ of
Booleans of length $\ell$, the gate values of $C$ on $x$ are obtained by decoding each pair of $C$
to a gate of a flat Boolean circuit on $\ell$ inputs and evaluating the decoded circuit with the
assignment that gives input $i$ the value $x_i$; the result lists the values of all gates in
order. A pair referring to an input index $i \ge \ell$ decodes to the constant false. -/
def xorCircuitEval (C : List XORGate) (assign : List Bool) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := assign.length)))
    (fun i => assign.getD i.val false)

/-- **Flattening blocks of bits.** For $n > 0$ and $k$ blocks $x_0, \dots, x_{k-1}$ of $n$ bits
each, the flattened string has $nk$ bits, and its bit $i$ is bit $i \bmod n$ of the block
$x_{\lfloor i/n \rfloor}$. -/
def xorFlat {n k : ℕ} (hn : 0 < n) (xs : Fin k → Fin n → Bool) : Fin (n * k) → Bool :=
  fun i => xs ⟨i.val / n, by
      rw [Nat.div_lt_iff_lt_mul hn]
      calc i.val < n * k := i.isLt
        _ = k * n := by rw [Nat.mul_comm]⟩
    ⟨i.val % n, Nat.mod_lt _ hn⟩

/-- **XOR of finitely many bits.** For $k$ bits $b_0, \dots, b_{k-1}$, their XOR is true if and
only if an odd number of the $b_i$ are true. -/
def xorFold {k : ℕ} (b : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => b i)).card % 2 = 1)

/-- **XOR of independent copies of a function.** For natural numbers $n$ and $k$ and a Boolean
function $f$ on $n$ bits, the function $f^{\oplus k}$ takes $k$ blocks $x_0, \dots, x_{k-1}$
of $n$ bits each to $f(x_0) \oplus \cdots \oplus f(x_{k-1})$, which is true if and only if an
odd number of the values $f(x_i)$ are true. -/
def xorOf {n k : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin k → Fin n → Bool) : Bool :=
  xorFold (fun i => f (xs i))

/-- **Agreement of a circuit with a Boolean function.** Let $\alpha$ be a finite type, let $C$
be a circuit given as a list of encoded gates, let $g$ assign a Boolean to each $a \in \alpha$,
and let $\mathrm{enc}$ encode each $a \in \alpha$ as a list of Booleans. The agreement of $C$
with $g$ is the rational number $N / |\alpha|$ (which is $0$ when $\alpha$ is empty), where $N$
is the number of $a \in \alpha$ such that $C$ has at least one gate and the value of its last
gate, when $C$ is evaluated on the input list $\mathrm{enc}(a)$, equals $g(a)$. -/
noncomputable def agreement {α : Type*} [Fintype α]
    (C : List XORGate) (g : α → Bool) (enc : α → List Bool) : ℚ :=
  (Set.ncard {a | (xorCircuitEval C (enc a)).getLast? = some (g a)} : ℚ) /
    (Fintype.card α : ℚ)

/-- **Yao's XOR lemma: hardness amplification by XOR.** There is a natural number $c$ such that
the following holds for all natural numbers $n \ge 1$ and $k$, every rational $\delta$ with
$0 < \delta \le 1/2$, every Boolean function $f$ on $n$ bits and every natural number $s$.
Suppose every circuit given as a list of at most $s$ encoded gates has agreement at most
$1 - \delta$ with $f$, where an input $x \in \{0,1\}^n$ is given to the circuit as its $n$ bits.
Then every circuit $C$ given as a list of encoded gates, whose number of gates $|C|$ satisfies
$|C| \cdot (k + 1)^c \le s$, has agreement at most $1/2 + (1 - 2\delta)^k / 2 + 1/(k + 1)$ with
the XOR $f^{\oplus k}$ of $k$ independent copies of $f$, where a $k$-tuple of $n$-bit blocks is
given to the circuit as its $nk$-bit flattening.

Source: A. C. Yao, "Theory and
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
