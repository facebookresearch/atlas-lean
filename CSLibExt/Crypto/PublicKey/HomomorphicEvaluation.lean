/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Complexity
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Computability.Encoding
public import Mathlib.Data.PNat.Basic

/-!
# Homomorphic evaluation

Gentry, *A Fully Homomorphic Encryption Scheme* (Stanford, 2009), §2.1, printed pp. 27–29
(PDF pp. 37–39), Definitions 2.1.1–2.1.5. The objects are distributions and single-output
straight-line circuits; these are functionality properties, not security games. Definition 2.1.1
lists the keys, circuits, messages and supported ciphertexts and specifies the evaluator's coins,
but does not explicitly quantify a negligible majorant. `Correct` uses one bound for all circuits
admitted at each parameter, so the circuit may grow with the parameter. In `FixedCircuitCorrect`
the bound may depend on a fixed circuit; this allows a growing sequence of failing circuits even
if every fixed one eventually succeeds. Definition 5.2.4 (printed p. 60, PDF p. 70) relates arity
to the circuit; it does not settle this quantifier order. Compactness separately bounds a Boolean
circuit computing the actual decryption function in the specified representations.

Gentry allows the public key to determine the message and ciphertext spaces. We specialize to
spaces and encodings common to all legal keys at a given parameter, as in `PKEScheme`. The
functionality predicates do not assert efficiency. Both full notions additionally require actual
polynomial-time machines. Definition 2.1.5 fixes a gate set; Theorem 4.2.1 (printed p. 49,
PDF p. 59) distinguishes bounded-depth evaluation over that set from full homomorphism over a
universal set. Here universality is functional completeness, including nullary constants. The
runtime model is restricted to finite operation types and charges the number of inputs plus gates.
This is a specialization, not a finiteness assumption in §2.1.5; Theorem 4.2.2 (printed p. 49)
explicitly counts wires. The correctness and compact-evaluation predicates need no such restriction.
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic

open Cslib.Circuits Cslib.Crypto.Framework Computability

/-- The message algebra over the specified gate signature, secret-key and ciphertext spaces, and
fixed binary representations of all three. These may vary with the security parameter, but are
common to all public keys at that parameter and to all depth levels. This specializes Gentry's
setup, in which the public key may determine the plaintext and ciphertext spaces. -/
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

/-- At one parameter and circuit, evaluation error is at most `δ` on every generated key pair,
message tuple and tuple of supported fresh ciphertexts. With these fixed, only the evaluator's
coins contribute to the probability of rejection or decryption to a wrong message. -/
def EvaluationErrorAtMost {B : Spaces σ} (S : Scheme B) {t : ℕ} (c : Circuit σ t 1)
    (δ : ℝ) : Prop := by
  classical
  exact ∀ kp ∈ S.pke.gen.support, ∀ (m : Fin t → B.Message) (x : Fin t → B.Ciphertext),
    (∀ i, x i ∈ (S.pke.enc kp.1 (m i)).support) →
    winProb ((S.evaluate kp.1 c x).map fun y =>
      decide (S.pke.dec kp.2 y ≠ some (c.eval B.gates m 0))) ≤ δ

/-- Uniform correctness on a circuit class: one negligible function of the security parameter
bounds evaluation error for all arities and circuits admitted at each parameter. In particular
the circuit may vary with the parameter. This is the convention for compact evaluation and
both full homomorphism predicates. -/
def Correct (E : (n : ℕ) → Scheme (A n)) (allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)) : Prop :=
  ∃ ε : ℕ → ℝ, NegligibleAdv ε ∧ ∀ n t (c : Circuit σ t 1), c ∈ allowed n t →
    EvaluationErrorAtMost (E n) c (ε n)

/-- Fixed-circuit correctness: for each arity and each circuit there is a negligible error bound
that works at every parameter where this circuit is admitted. It is still uniform over generated
keys, messages and supported fresh ciphertexts, but need not work for any other circuit. -/
def FixedCircuitCorrect (E : (n : ℕ) → Scheme (A n))
    (allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)) : Prop :=
  ∀ t (c : Circuit σ t 1), ∃ ε : ℕ → ℝ, NegligibleAdv ε ∧ ∀ n, c ∈ allowed n t →
    EvaluationErrorAtMost (E n) c (ε n)

/-- Uniform correctness implies fixed-circuit correctness for the same scheme and circuit class:
the same negligible bound can be used for every fixed circuit. -/
theorem Correct.toFixedCircuitCorrect {E : (n : ℕ) → Scheme (A n)}
    {allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)} (h : Correct E allowed) :
    FixedCircuitCorrect E allowed := by
  obtain ⟨ε, hε, hb⟩ := h
  exact fun t c => ⟨ε, hε, fun n => hb n t c⟩

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

/-- A scheme **compactly evaluates** a class of single-output circuits when it is uniformly
correct for that class and compact (Definition 2.1.3, using the uniform-error convention).
The error bound is shared by all admitted circuits; the decryption circuit size bound is also
independent of the evaluated circuit. -/
def CompactlyEvaluates (E : (n : ℕ) → Scheme (A n))
    (allowed : ℕ → (t : ℕ) → Set (Circuit σ t 1)) : Prop :=
  Correct E allowed ∧ Compact E

/-- Basis-relative functionality: compact evaluation of all single-output circuits over the given
interpretation, with arbitrary arity and depth. This does not assert universality or efficiency. -/
def EvaluatesBasis (E : (n : ℕ) → Scheme (A n)) : Prop :=
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

/-- A single-tape Turing machine realizes a law on words using a fair tape of `coins` bits
and at most `steps` transitions on **every** tape. Its input is the framed argument followed
by the coin bits. The pushforward of the uniform tape law must equal the specified distribution. -/
def SamplesWithin (T : Turing.SingleTapeTM Bool) (coins steps : ℕ)
    (arg : List Bool) (law : PMF (List Bool)) : Prop :=
  ∃ draw : BitString coins → List Bool,
    (Probability.PMF.uniformOfFintype (BitString coins)).map draw = law ∧
    ∀ r, T.OutputsWithinTime (frame arg ++ List.ofFn r) (draw r) steps

/-- Finite-basis polynomial time: the operation type is finite, and four fixed single-tape Turing
machines realize the algorithms with one pair of polynomials for fair-tape length and worst-case
steps. Encryption runs on every declared public key and message; evaluation on every public key
and ciphertext tuple for each admitted circuit; decryption on every secret key and ciphertext,
not only generated or fresh inputs. Decryption receives the security parameter but no level. The
budget parameter is the security parameter plus the positive level if present. A level imposes
its depth cutoff; no level admits all depths. Only evaluation adds input arity and gate count.
For the fixed finite operation type, both tag length and fan-in are bounded independently of the
circuit. This topology count is not a wire-count convention for arbitrary signatures. -/
def PolynomialTime {ι : Type} (level : ι → Option ℕ+) (E : ι → (n : ℕ) → Scheme (A n))
    (tag : Encoding σ.Op Bool) : Prop :=
  Finite σ.Op ∧ ∃ (q p : Polynomial ℕ) (gen enc dec ev : Turing.SingleTapeTM Bool), ∀ i n,
    let S := E i n
    let B := A n
    let k := n + (level i).elim 0 (·.val)
    let param := unary n ++ (level i).elim [] (fun d => unary d.val)
    SamplesWithin gen (q.eval k) (p.eval k) param
      (S.pke.gen.map fun kp =>
        frame (S.publicCode.encode kp.1) ++ frame (B.secretCode.encode kp.2)) ∧
    (∀ pk m, SamplesWithin enc (q.eval k) (p.eval k)
      (param ++ frame (S.publicCode.encode pk) ++ frame (B.messageCode.encode m))
      ((S.pke.enc pk m).map B.cipherCode.encode)) ∧
    (∀ sk x, dec.OutputsWithinTime
      (unary n ++ frame (B.secretCode.encode sk) ++ frame (B.cipherCode.encode x))
      (answer B.messageCode (S.pke.dec sk x)) (p.eval k)) ∧
    ∀ t (c : Circuit σ t 1), (∀ d ∈ level i, c.depth ≤ d.val) → ∀ pk x,
      let code := circuitCode tag c
      let budget := k + t + c.size
      SamplesWithin ev (q.eval budget) (p.eval budget)
        (param ++ frame (S.publicCode.encode pk) ++ frame code ++
          (List.ofFn fun i => frame (B.cipherCode.encode (x i))).flatten)
        ((S.evaluate pk c x).map B.cipherCode.encode)

/-- Full homomorphism (Gentry, Definition 2.1.4) in the common-space model on a finite basis.
At each parameter every single-output function at every arity is computed by a circuit. The
scheme compactly evaluates all those circuits without a depth cutoff, and the four algorithms
have polynomial-time realizations, with no level parameter. -/
def FullyHomomorphic (E : (n : ℕ) → Scheme (A n)) (tag : Encoding σ.Op Bool) : Prop :=
  (∀ n, (A n).gates.IsComplete) ∧ EvaluatesBasis E ∧
    PolynomialTime (fun _ : Unit => none) (fun _ => E) tag

/-- Leveled evaluation over a specified finite gate basis (a specialization of Definition 2.1.5).
One polynomially bounded decryption circuit at each security parameter implements decryption
at every positive level. Each fixed level `d` has one negligible bound for all arities and circuits
through depth `d` inclusive. The four algorithms have uniform polynomial running time across
levels in the finite-basis model, charging evaluation for input arity and gate count. This does
not require universality. -/
def LeveledOverBasis (E : ℕ+ → (n : ℕ) → Scheme (A n)) (tag : Encoding σ.Op Bool) : Prop :=
  (∃ (p : Polynomial ℕ) (D : ℕ → DecryptionCircuit), ∀ n,
    (D n).inputs + (D n).outputs + (D n).circuit.size ≤ p.eval n ∧
    ∀ d, (D n).Implements (E d n)) ∧
  (∀ d, Correct (E d) fun _ _ => {c | c.depth ≤ d.val}) ∧ PolynomialTime some E tag

/-- Leveled full homomorphism on a finite universal basis: the family satisfies Gentry's
specified-gate conditions (Definition 2.1.5), and the interpretation at each parameter can compute
every single-output function at every arity. The universality qualification distinguishes this
from leveled evaluation on a restricted basis, as in Gentry's Theorem 4.2.1. -/
def LeveledFullyHomomorphic (E : ℕ+ → (n : ℕ) → Scheme (A n)) (tag : Encoding σ.Op Bool) : Prop :=
  (∀ n, (A n).gates.IsComplete) ∧ LeveledOverBasis E tag

end Cslib.Crypto.Homomorphic
