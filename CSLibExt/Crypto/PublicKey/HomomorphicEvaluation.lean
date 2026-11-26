/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Computability.Encoding
public import Mathlib.Data.PNat.Basic

/-!
# Homomorphic evaluation

Gentry, *A Fully Homomorphic Encryption Scheme* (Stanford, 2009), §2.1, printed pp. 27–29
(PDF pp. 37–39), Definitions 2.1.1–2.1.5. The objects are distributions and single-output
straight-line circuits; these are functionality properties, not security games. Correctness fixes
fresh ciphertexts *before* it measures error. Compactness is a size bound on a Boolean circuit
computing the actual decryption function in the specified representations.

The first four definitions describe functionality relative to a scheme. Section 2.1 assumes
efficient algorithms as background; the additional **uniform** running-time requirement in the
leveled definition is made explicit using fair random tapes and finite-state Turing machines.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Cslib.Circuits Cslib.Crypto.Framework Computability

/-- The message algebra over the specified gate signature, secret-key and ciphertext spaces, and
fixed binary representations of all three. These may vary with the security parameter, but the
inputs and outputs of decryption have the same representations at every depth level. -/
structure Spaces (σ : Signature) where
  Message : Type
  SecretKey : Type
  Ciphertext : Type
  gates : Interpretation σ Message
  messageCode : Encoding Message Bool
  secretCode : Encoding SecretKey Bool
  cipherCode : Encoding Ciphertext Bool

/-- At a given parameter, a public-key scheme with perfectly correct fresh decryption, extended
by a public, possibly randomized evaluator. Its input ciphertext tuple has exactly one entry per
input wire. The public-key space and its encoding may change with the level. -/
structure Scheme {σ : Signature} (A : Spaces σ) where
  PublicKey : Type
  publicCode : Encoding PublicKey Bool
  pke : PKEScheme A.Message PublicKey A.SecretKey A.Ciphertext
  fresh_correct : pke.Correct
  evaluate : ∀ {t}, PublicKey → Circuit σ t 1 → (Fin t → A.Ciphertext) → PMF A.Ciphertext

variable {σ : Signature} {A : ℕ → Spaces σ}

/-- Correctness on a circuit class (Gentry, Definition 2.1.1). One negligible bound in the
security parameter works for every generated key pair, input arity, permitted circuit, message
tuple and tuple of supported fresh ciphertexts. With these fixed, the probability that evaluation
decrypts to anything other than the circuit output (including rejection) is at most the bound. -/
def Correct (E : (n : ℕ) → Scheme (A n)) (allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)) : Prop := by
  classical
  exact ∃ ε : ℕ → ℝ, NegligibleAdv ε ∧ ∀ n kp, kp ∈ (E n).pke.gen.support →
    ∀ t (c : Circuit σ t 1), c ∈ allowed n t →
    ∀ (m : Fin t → (A n).Message) (x : Fin t → (A n).Ciphertext),
      (∀ i, x i ∈ ((E n).pke.enc kp.1 (m i)).support) →
      winProb (((E n).evaluate kp.1 c x).map fun y =>
        decide ((E n).pke.dec kp.2 y ≠ some (c.eval (A n).gates m 0))) ≤ ε n

local notation "frame" => MetaMathlibExt.BitstringEncoding.delimit

/-- The word representing a decryption result before framing: the empty word for rejection, or
one followed by the encoded message for success. -/
def answer {M : Type} (enc : Encoding M Bool) : Option M → List Bool
  | none => []
  | some m => true :: enc.encode m

/-- A candidate decryption circuit: a De Morgan circuit with fixed binary input and output
interfaces. Its size bound charges the ports as well as the gates, since a CSLib wiring circuit
with arbitrarily many ports would otherwise have size zero. -/
structure DecryptionCircuit where
  inputs : ℕ
  outputs : ℕ
  circuit : Circuit Boolean.signature inputs outputs

/-- The bit circuit computes decryption on every secret key and ciphertext in the declared
spaces. Its input holds the framed key followed by the framed ciphertext; its output holds the
framed result (empty for rejection, a one followed by the message for success). Both sides must
fit their ports before zero padding. A frame prefixes each data bit by a one and ends in zero. -/
def DecryptionCircuit.Implements {B : Spaces σ} (D : DecryptionCircuit) (S : Scheme B) : Prop :=
  ∀ sk x,
    let input := frame (B.secretCode.encode sk) ++ frame (B.cipherCode.encode x)
    let output := frame (answer B.messageCode (S.pke.dec sk x))
    input.length ≤ D.inputs ∧ output.length ≤ D.outputs ∧
      D.circuit.eval Boolean.interpretation (fun i => input[i.val]?.getD false) =
        fun j => output[j.val]?.getD false

/-- Compactness (Gentry, Definition 2.1.2): one polynomial bounds, at every security parameter,
the input ports, output ports and gate count together of a circuit implementing decryption. The
circuit is chosen without knowledge of the evaluated circuit or its arity, inputs or output. -/
def Compact (E : (n : ℕ) → Scheme (A n)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, ∃ D : DecryptionCircuit,
    D.inputs + D.outputs + D.circuit.size ≤ p.eval n ∧ D.Implements (E n)

/-- A scheme **compactly evaluates** a class of single-output circuits when it is correct for
that class and compact (Gentry, Definition 2.1.3). Correctness bounds only evaluation error on
supported keys and input encryptions; compactness bounds the size of a circuit for decryption
independently of the evaluated circuit. -/
def CompactlyEvaluates (E : (n : ℕ) → Scheme (A n))
    (allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)) : Prop :=
  Correct E allowed ∧ Compact E

/-- Full homomorphism (Gentry, Definition 2.1.4) is compact evaluation of all single-output
circuits over the specified gate signature, with arbitrary arity and no depth bound. -/
def FullyHomomorphic (E : (n : ℕ) → Scheme (A n)) : Prop :=
  CompactlyEvaluates E fun _ _ => Set.univ

local notation "unary" => (fun n : ℕ => unaryEncodeNat n ++ [false])

/-- A binary description of a single-output circuit: unary arity and gate count, topologically
ordered gates (framed operation code and tagged unary predecessor indices), and the designated
output wire. Its length charges the actual syntax, including inputs and wiring. For a fixed finite
basis this length and input-plus-gate count bound each other polynomially. -/
def circuitCode (tag : Encoding σ.Op Bool) {t : ℕ} (c : Circuit σ t 1) : List Bool :=
  unary t ++ unary c.size ++ program c.program ++ wire (c.outputs 0)
where
  wire {g : ℕ} : Wire t g → List Bool
    | .input i => false :: unary i.val
    | .gate j => true :: unary j.val
  program : {g : ℕ} → Program σ t g → List Bool
    | _, .empty => []
    | _, .gate p l => program p ++ frame (tag.encode l.op) ++
        (List.ofFn fun i => wire (l.wires i)).flatten

/-- A finite-state machine realizes a specified law on output words with a fair tape of `coins`
bits and at most `steps` transitions on **every** tape. Its input is the framed argument followed
by the coin bits. The pushforward of the uniform tape law must equal the specified distribution. -/
def SamplesWithin (T : Turing.SingleTapeTM Bool) (coins steps : ℕ)
    (arg : List Bool) (law : PMF (List Bool)) : Prop :=
  ∃ draw : BitString coins → List Bool,
    (Probability.PMF.uniformOfFintype (BitString coins)).map draw = law ∧
    ∀ r, T.OutputsWithinTime (frame arg ++ List.ofFn r) (draw r) steps

/-- Polynomial running time in Gentry's leveled model. Four machines, one coin-length polynomial
and one time polynomial work at every positive level and security parameter. Key generation,
encryption and decryption use a budget in their sum; for evaluation on a permitted circuit its
description length is added. The machines realize the actual output laws or deterministic result
on the fixed bit representations, with no secret key passed to the evaluator. -/
def PolynomialTime (E : ℕ+ → (n : ℕ) → Scheme (A n)) (tag : Encoding σ.Op Bool) : Prop :=
  ∃ (q p : Polynomial ℕ) (gen enc dec ev : Turing.SingleTapeTM Bool), ∀ d n,
    let S := E d n
    let B := A n
    let k := n + d.val
    let param := unary n ++ unary d.val
    SamplesWithin gen (q.eval k) (p.eval k) param
      (S.pke.gen.map fun kp =>
        frame (S.publicCode.encode kp.1) ++ frame (B.secretCode.encode kp.2)) ∧
    (∀ pk m, SamplesWithin enc (q.eval k) (p.eval k)
      (param ++ frame (S.publicCode.encode pk) ++ frame (B.messageCode.encode m))
      ((S.pke.enc pk m).map B.cipherCode.encode)) ∧
    (∀ sk x, dec.OutputsWithinTime
      (unary n ++ frame (B.secretCode.encode sk) ++ frame (B.cipherCode.encode x))
      (answer B.messageCode (S.pke.dec sk x)) (p.eval k)) ∧
    ∀ t (c : Circuit σ t 1), c.depth ≤ d.val → ∀ pk x,
      let code := circuitCode tag c
      let budget := k + code.length
      SamplesWithin ev (q.eval budget) (p.eval budget)
        (param ++ frame (S.publicCode.encode pk) ++ frame code ++
          (List.ofFn fun i => frame (B.cipherCode.encode (x i))).flatten)
        ((S.evaluate pk c x).map B.cipherCode.encode)

/-- Leveled full homomorphism (Gentry, Definition 2.1.5). One polynomially bounded decryption
circuit family, indexed **only** by the security parameter, implements decryption at every
positive level. Each level is correct through its inclusive circuit-depth bound over the fixed
signature. All four algorithms have a uniform polynomial time bound across levels. -/
def LeveledFullyHomomorphic (E : ℕ+ → (n : ℕ) → Scheme (A n)) (tag : Encoding σ.Op Bool) : Prop :=
  (∃ (p : Polynomial ℕ) (D : ℕ → DecryptionCircuit), ∀ n,
    (D n).inputs + (D n).outputs + (D n).circuit.size ≤ p.eval n ∧
    ∀ d, (D n).Implements (E d n)) ∧
  (∀ d, Correct (E d) fun _ _ => {c | c.depth ≤ d.val}) ∧ PolynomialTime E tag

end Cslib.Crypto.Homomorphic
