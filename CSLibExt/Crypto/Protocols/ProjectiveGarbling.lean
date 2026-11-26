/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Cslib.Probability.PMF

/-!
# Projective garbling and the correctness of Yao's four-row construction

`Scheme.Correct` specifies functional correctness on every supported garbling and every input.
`yao` instantiates this interface on CSLib circuits with arbitrary two-input Boolean gates. The
clear and garbled circuits use the same `Circuit.eval` with different signatures and
interpretations. Unlike the De Morgan `Boolean.signature` (which has unary NOT and nullary
constants) and `fullSignature 2 Bool` (which also has nullary constants), all our gate symbols
have arity exactly two. Each public gate stores four ciphertexts in place of the clear gate
function. The garbler computes these ciphertexts from the function and the wire labels; each
line refers only to inputs or earlier gates. `trace_garbleProgram` identifies the active label at
*every* wire, including one read many times or designated directly as an output.

Bellare, Hoang and Rogaway, *Foundations of Garbled Circuits* (ACM CCS 2012, pp. 784–796),
separate garbling, encoding, decoding, garbled evaluation and clear evaluation. In the
[full version of 1 October 2012](https://eprint.iacr.org/2012/265), §3.1 requires correctness
for every supported garbling and every input; §3.2 describes projective encoding: for fixed
encoding data the label at each position depends only on the bit at that position. `select` and
`Scheme.Correct` express these functional conditions with typed data and fixed input and output
counts, without the paper's requirements on string encodings.

The same full version introduces tweakable dual-key ciphers in §5. In Garble1 (§5.1, Fig. 7),
the two incoming token types select the row, and an output token's type is its semantic bit,
so the decoding data is empty. Here `RowCipher` takes no tweak and requires only right-key
decryption. Output wires, like other wires, have random pointer masks; the decoder cancels the
mask at each designated output.

Pass and shelat, *A Course in Cryptography* (2010), §§6.2.1–6.2.3, describe the wire keys,
fan-in two with unbounded fan-out, and four encrypted rows; they shuffle and try the rows.
The complementary pointers and direct row lookup here are the point-and-permute variant of
Evans, Kolesnikov and Rosulek, *A Pragmatic Introduction to Secure Multi-Party Computation*
(2018), §3.1.1. We decode with each designated output's zero-label pointer rather than an
encrypted output table. We assume only right-key decryption, not privacy or wrong-key rejection.
There is no time bound, key-transfer protocol or security assertion.
-/

@[expose] public section

namespace Cslib.Crypto.ProjectiveGarbling

open Cslib.Circuits

variable {n m g : ℕ} {K C : Type*}

/-- **Garbling data.** For an $n$-input circuit, one garbling consists of a public garbled
circuit, two input labels per input wire, and output decoding information. Only the selected
input labels, not the family of pairs, are supplied to evaluation. -/
structure Garbling (n : ℕ) (Public Label Decoder : Type*) where
  circuit : Public
  labels : Fin n → Bool → Label
  decoder : Decoder

/-- **Projective selection.** At input wire $i$ the encoding of $x$ is the label indexed by
$x_i$ in that wire's pair. It uses no other coordinate of the input and takes no random coins. -/
def select {L : Type*} (labels : Fin n → Bool → L) (x : Fin n → Bool) : Fin n → L :=
  fun i => labels i (x i)

/-- **Projective garbling scheme.** For fixed input and output counts, garbling a clear circuit
samples a public circuit, an input label pair on each input wire, and a decoder. Evaluation is
a deterministic function of just the public circuit and one label per input; decoding converts
its result, using the decoding information, to the output bits. -/
structure Scheme (n m : ℕ) (Clear Public Label Encoded Decoder : Type*) where
  garble : Clear → PMF (Garbling n Public Label Decoder)
  eval : Public → (Fin n → Label) → Encoded
  decode : Decoder → Encoded → Fin m → Bool

/-- **Perfect functional correctness of a projective garbling scheme.** For every circuit, for
every sampled garbling in its support, and for every clear input, selecting the input labels,
evaluating the public garbled circuit and decoding must give the clear circuit's output. -/
def Scheme.Correct {Clear Public Label Encoded Decoder : Type*}
    (S : Scheme n m Clear Public Label Encoded Decoder)
    (sem : Clear → (Fin n → Bool) → Fin m → Bool) : Prop :=
  ∀ c, ∀ d ∈ (S.garble c).support, ∀ x,
    S.decode d.decoder (S.eval d.circuit (select d.labels x)) = sem c x

/-- **Binary circuit basis.** For a given type of operation symbols, each operation takes exactly
 two ordered wires. Clear circuits use Boolean functions as symbols; garbled circuits use tables
 of four ciphertexts instead. -/
abbrev binaryBasis (Op : Type*) : Signature where
  Op := Op
  Arity _ := 2

/-- **Clear binary gate interpretation.** A gate specified by a Boolean function applies that
function to the values on its first and second incoming wires, in that order. -/
def clearEval : Interpretation (binaryBasis (Bool → Bool → Bool)) Bool :=
  fun f x => f (x 0) (x 1)

/-- **Wire coins.** For one wire the coins consist of two key payloads, indexed by the clear
bit, and one bit specifying the pointer of the zero label. Equal payloads are allowed. -/
abbrev WireCoins (K : Type*) := (Bool → K) × Bool

/-- **Wire labels with complementary pointers.** For wire coins $(k,r)$ the label of $b$ is
$(k(b), b \mathbin{\mathrm{xor}} r)$. Its pointer distinguishes the two labels even when the
key payloads coincide. -/
def WireCoins.label (s : WireCoins K) (b : Bool) : K × Bool := (s.1 b, b ^^ s.2)

/-- **Dual-key row cipher.** For two ordered key payloads there is a deterministic encryption
of a wire label and a decryption of a ciphertext. Decrypting an encryption with those same
keys must recover the label. No behaviour is prescribed for a different key pair. -/
structure RowCipher (K C : Type*) where
  enc : K → K → K × Bool → C
  dec : K → K → C → K × Bool
  dec_enc : ∀ k l z, dec k l (enc k l z) = z

/-- **Four ciphertext rows.** A public gate stores exactly one ciphertext for each ordered pair
of pointer bits, in order 00, 01, 10, 11. -/
structure Table (C : Type*) where
  row00 : C
  row01 : C
  row10 : C
  row11 : C

variable (E : RowCipher K C)

/-- **Point-and-permute gate construction.** In the row addressed by the pointers for clear
bits $a,b$, encrypt the output label for $f(a,b)$ with the corresponding two input keys.
Every row is filled because each wire's pointer permutation is an involution. -/
def garbleGate (f : Bool → Bool → Bool) (u v w : WireCoins K) : Table C :=
  let row p q :=
    let a := p ^^ u.2
    let b := q ^^ v.2
    E.enc (u.1 a) (v.1 b) (w.label (f a b))
  ⟨row false false, row false true, row true false, row true true⟩

/-- **Point-and-permute gate evaluation.** Given a decryption operation, four ciphertexts and
two active labels, use the pointers to select one row and decrypt it with the two key payloads. -/
def evalGate (dec : K → K → C → K × Bool) : Interpretation (binaryBasis (Table C)) (K × Bool) :=
  fun t x =>
    let u := x 0
    let v := x 1
    let row := if u.2 then (if v.2 then t.row11 else t.row10)
               else (if v.2 then t.row01 else t.row00)
    dec u.1 v.1 row

/-- **Selected-row correctness.** At the active labels for $a,b$, decrypting the single row
addressed by their pointers returns the complete active output label for $f(a,b)$. This holds
for every choice of wire coins and every row cipher satisfying right-key decryption. -/
theorem evalGate_garbleGate (f : Bool → Bool → Bool) (u v w : WireCoins K)
    (x : Fin 2 → K × Bool) (a b : Bool) (ha : x 0 = u.label a) (hb : x 1 = v.label b) :
    evalGate E.dec (garbleGate E f u v w) x = w.label (f a b) := by
  simp only [evalGate, ha, hb]
  obtain ⟨ku, ru⟩ := u
  obtain ⟨kv, rv⟩ := v
  cases ru <;> cases rv <;> cases a <;> cases b <;> exact E.dec_enc ..

/-- **Garbling a straight-line program.** Replace each binary truth table by four ciphertexts
using the input and gate wire coins. Leave the ordered predecessor wires of each line unchanged. -/
def garbleProgram (si : Fin n → WireCoins K) : {g : ℕ} →
    Program (binaryBasis (Bool → Bool → Bool)) n g → (Fin g → WireCoins K) →
    Program (binaryBasis (Table C)) n g
  | _, .empty, _ => .empty
  | g + 1, .gate p line, sg =>
    let prior := fun i : Fin g => sg i.castSucc
    let wires := Wire.elim si prior
    (garbleProgram si p prior).gate
      ⟨garbleGate E line.op (wires (line.wires 0)) (wires (line.wires 1)) (sg (Fin.last g)),
       line.wires⟩

/-- **Active-label invariant.** On every input, at each input or gate wire of a binary
straight-line program the trace of its garbling equals that wire's label for the value in the
clear trace. The statement holds for every assignment of wire coins, with arbitrary fan-out. -/
theorem trace_garbleProgram (p : Program (binaryBasis (Bool → Bool → Bool)) n g)
    (si : Fin n → WireCoins K) (sg : Fin g → WireCoins K) (x : Fin n → Bool) (w : Wire n g) :
    (garbleProgram E si p sg).trace (evalGate E.dec) (select (fun i => (si i).label) x) w =
      (Wire.elim si sg w).label (p.trace clearEval x w) := by
  induction p with
  | empty => cases w with
    | input i => rfl
    | gate i => exact Fin.elim0 i
  | @gate g p line ih =>
    cases w with
    | input i => rfl
    | gate i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [garbleProgram, Program.trace, Wire.elim, Program.eval_gate_last]
        apply evalGate_garbleGate
        · exact ih _ (line.wires 0)
        · exact ih _ (line.wires 1)
      · simp only [garbleProgram, Program.trace, Wire.elim, Program.eval_gate_castSucc]
        exact ih _ (.gate j)

/-- **Garbling with fixed wire coins.** Publish the four-row program with the same output wires
as the clear circuit, retain the input label pairs for selection, and give the zero-label pointer
of each designated output as decoding information. -/
def fromCoins (c : Circuit (binaryBasis (Bool → Bool → Bool)) n m)
    (coins : (Fin n → WireCoins K) × (Fin c.size → WireCoins K)) :
    Garbling n (Circuit (binaryBasis (Table C)) n m) (K × Bool) (Fin m → Bool) where
  circuit := ⟨garbleProgram E coins.1 c.program coins.2, c.outputs⟩
  labels i := (coins.1 i).label
  decoder j := (Wire.elim coins.1 coins.2 (c.outputs j)).2

/-- **Yao's four-row projective garbling.** For a topologically ordered circuit on $n$ inputs
and $m$ designated outputs with arbitrary binary Boolean gates, sample all wire coins uniformly:
two independent payloads from a finite nonempty key space and one independent bit per wire.
Publish the point-and-permute tables and original wiring. Select one input label per coordinate,
evaluate the tables with those active labels, then XOR each active output pointer with the
corresponding zero-label pointer to decode. Only right-key cipher correctness is required. -/
noncomputable def yao [Fintype K] [Nonempty K] (n m : ℕ) :
    Scheme n m (Circuit (binaryBasis (Bool → Bool → Bool)) n m)
      (Circuit (binaryBasis (Table C)) n m) (K × Bool) (Fin m → K × Bool) (Fin m → Bool) where
  garble c := (Cslib.Probability.PMF.uniformOfFintype _).map (fromCoins E c)
  eval c := c.eval (evalGate E.dec)
  decode d y j := (y j).2 ^^ d j

/-- **Support of four-row garbling.** A garbling of a given circuit has positive probability
exactly when it is obtained by some assignment of wire coins. No distinctness conditions on the
key payloads, and no additional restrictions on the pointer masks, are needed. -/
theorem mem_support_yao_iff [Fintype K] [Nonempty K]
    (c : Circuit (binaryBasis (Bool → Bool → Bool)) n m) (d) :
    d ∈ ((yao E n m).garble c).support ↔ ∃ coins, fromCoins E c coins = d := by
  change d ∈ (PMF.map (fromCoins E c) _).support ↔ _
  simp only [PMF.mem_support_map_iff, Cslib.Probability.PMF.uniformOfFintype,
    Cslib.Probability.PMF.mem_support_uniformOfFinset_iff, Finset.mem_univ, true_and]

/-- **Correctness of Yao's four-row construction.** For every binary Boolean circuit, every
garbling in the support of its uniform wire-coin construction, and every input, decoding the
result of evaluating on the projectively selected labels gives exactly all the designated clear
output bits. This is a functional result, not a security claim. -/
theorem yao_correct [Fintype K] [Nonempty K] :
    (yao E n m).Correct (fun c => c.eval clearEval) := by
  intro c d hd x
  obtain ⟨coins, rfl⟩ := (mem_support_yao_iff E c d).mp hd
  funext j
  change (((garbleProgram E coins.1 c.program coins.2).trace (evalGate E.dec)
    (select (fun i => (coins.1 i).label) x) (c.outputs j)).2 ^^
    (Wire.elim coins.1 coins.2 (c.outputs j)).2) = _
  rw [trace_garbleProgram]
  simp [WireCoins.label, Circuit.eval]

end Cslib.Crypto.ProjectiveGarbling
