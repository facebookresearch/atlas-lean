/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import MathlibExt.Computability.Complexity
import MathlibExt.Computability.TuringMachine.Composition

/-!
# Interactive proofs and arguments for functions

Justin Thaler, *Proofs, Arguments, and Zero-Knowledge*, manuscript dated July 18, 2023,
§3.1, Definition 3.1, and §3.2, Definition 3.2 (pp. 23–24).

The channel has a polynomial number of slots, each of polynomial bit capacity. A sender
can fill a slot with a shorter word, including the empty word; only the prefix fitting in
the slot goes on the wire. Fixed polynomial schedules include constant schedules and allow
padding. Tags and end markers below are for local computation, not extra messages.
-/

@[expose] public section

namespace Cslib.Crypto.Interaction

open MetaMathlibExt BitstringEncoding Turing Polynomial Framework

/-- Symbols on the local machine input: tagged bits of the common input, initial claim,
private tape and messages. An end marker delimits each message, even an empty one. -/
inductive Symbol where
  | input (b : Bool) | claim (b : Bool) | coin (b : Bool) | payload (b : Bool) | stop
  deriving DecidableEq, Fintype

/-- Local view of an interaction: the bitstring input, encoded claim, tape and chronological
message history. Supplying the empty tape gives precisely the public view. -/
def view (x y r : List Bool) (t : List (List Bool)) : List Symbol :=
  x.map .input ++ y.map .claim ++ r.map .coin ++ t.flatMap (fun m => m.map .payload ++ [.stop])

/-- A deterministic strategy supplies an initial value on the input alone. Its later replies
read only the public view. No running-time condition is imposed by the strategy type. -/
structure Strategy (R : Type) where
  claim : List Bool → R
  reply : List Symbol → List Bool

/-- A uniform verifier: two fixed polynomial-time multi-stack Turing computations, for
sending and deciding. The protocol fixes the first sender, the number of later messages,
the number of private fair bits, and the maximum bits per message as functions of input length
(the three numerical schedules are natural-coefficient polynomials). -/
structure Verifier where
  verifierFirst : Bool
  messages : Polynomial ℕ
  coins : Polynomial ℕ
  width : Polynomial ℕ
  send : List Symbol → List Bool
  accept : List Symbol → Bool
  sendTM : TM2ComputableInPolyTime id id send
  acceptTM : TM2ComputableInPolyTime id bitEncode accept

variable {R : Type} [BitstringEncoding R]

/-- The first `i` messages on a fixed verifier tape. The initial value is separate. A
verifier turn reads the tape; a prover turn receives only the public view, including the
previously transmitted (not merely proposed) words. -/
def Verifier.history (V : Verifier) (P : Strategy R) (x r : List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 =>
    let t := V.history P x r i
    let y := bitEncode (P.claim x)
    let m := if V.verifierFirst = decide (i % 2 = 0) then V.send (view x y r t)
      else P.reply (view x y [] t)
    t ++ [m.take (V.width.eval x.length)]

/-- The history of `i` slots has exactly `i` messages and at most `i` times the slot
capacity in payload bits, regardless of the strategy or the contents of the tape. -/
theorem Verifier.history_bounds (V : Verifier) (P : Strategy R) (x r : List Bool) (i : ℕ) :
    (V.history P x r i).length = i ∧
      (V.history P x r i).flatten.length ≤ i * V.width.eval x.length := by
  induction i with
  | zero => simp [history]
  | succ i ih =>
    simp only [history, List.length_append, List.length_cons, List.length_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_take, ih.1, Nat.succ_mul]
    exact ⟨trivial, Nat.add_le_add ih.2 (min_le_left _ _)⟩

/-- Fix a verifier and a finite range with a fixed bitstring encoding. A single polynomial
in the common input length bounds the encoded initial claim plus the total payload bits of
all scheduled messages, for every input, strategy and tape (of any length). Indeed the
claim length has a uniform upper bound over the range, and each slot holds at most its
scheduled width in bits. -/
theorem Verifier.communication_bound [Finite R] (V : Verifier) : ∃ q : Polynomial ℕ,
    ∀ (P : Strategy R) (x r : List Bool), (bitEncode (P.claim x)).length +
      (V.history P x r (V.messages.eval x.length)).flatten.length ≤ q.eval x.length := by
  classical
  let _ := Fintype.ofFinite R
  refine ⟨C (Finset.univ.sup (fun y : R => (bitEncode y).length)) + V.messages * V.width, ?_⟩
  intro P x r
  rw [eval_add, eval_C, eval_mul]
  exact Nat.add_le_add (Finset.le_sup (f := fun y : R => (bitEncode y).length)
    (Finset.mem_univ (P.claim x))) (V.history_bounds P x r _).2

private theorem length_view (x y r : List Bool) (t : List (List Bool)) :
    (view x y r t).length = x.length + y.length + r.length + t.flatten.length + t.length := by
  have aux : (t.flatMap (fun m => m.map Symbol.payload ++ [.stop])).length =
      t.flatten.length + t.length := by
    induction t with
    | nil => rfl
    | cons m t ih => simp [ih]; omega
  simp [view, aux, Nat.add_assoc]

/-- Fix a verifier and a finite encoded range, so the length of an initial claim has one
upper bound independent of the input and strategy. Write $n$ for input length and $k$ for
the scheduled message count at $n$. Take any deterministic strategy, any tape of exactly
the scheduled length, and the verifier view after any $i \leq k$ messages. A single
polynomial in $n$ bounds $k+1$ times the sum of the send and decision machine clocks
evaluated at the length of that view. This bounds the work of the verifier's TM2 routines;
it does not count constructing or copying their views. -/
theorem Verifier.clock_bound [Finite R] (V : Verifier) : ∃ q : Polynomial ℕ,
    ∀ (P : Strategy R) (x r : List Bool) (i : ℕ), r.length = V.coins.eval x.length →
    i ≤ V.messages.eval x.length →
    let v := view x (bitEncode (P.claim x)) r (V.history P x r i)
    (V.messages.eval x.length + 1) *
      (V.sendTM.time.eval v.length + V.acceptTM.time.eval v.length) ≤ q.eval x.length := by
  classical
  let _ := Fintype.ofFinite R
  let c := Finset.univ.sup (fun y : R => (bitEncode y).length)
  let size := X + C c + V.coins + V.messages * V.width + V.messages
  refine ⟨(V.messages + 1) * ((V.sendTM.time + V.acceptTM.time).comp size), ?_⟩
  intro P x r i hr hi v
  have hc : (bitEncode (P.claim x)).length ≤ c :=
    Finset.le_sup (f := fun y : R => (bitEncode y).length) (Finset.mem_univ (P.claim x))
  obtain ⟨hlen, hbits⟩ := V.history_bounds P x r i
  have hb := hbits.trans (Nat.mul_le_mul_right _ hi)
  have hv : v.length ≤ size.eval x.length := by
    simp only [v, length_view, size, eval_add, eval_X, eval_C, eval_mul, hlen, hr]
    omega
  simp only [eval_add, eval_one, eval_mul, eval_comp]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add (TM2Composition.eval_mono V.sendTM.time hv)
    (TM2Composition.eval_mono V.acceptTM.time hv))

/-- For fixed private bits, run the designated number of alternating messages and decide on
the resulting transcript with those very same bits. -/
def Verifier.out (V : Verifier) (P : Strategy R) (x tape : List Bool) : Bool :=
  V.accept (view x (bitEncode (P.claim x)) tape (V.history P x tape (V.messages.eval x.length)))

/-- Acceptance probability, sampling the finite private tape uniformly once per interaction. -/
noncomputable def Verifier.acceptance (V : Verifier) (P : Strategy R) (x : List Bool) : ℝ :=
  winProb ((Cslib.Probability.PMF.uniformOfFintype (Fin (V.coins.eval x.length) → Bool)).map
    fun r => V.out P x (List.ofFn r))

/-- Statistical soundness tests all deterministic strategies at every input. The fixed-error
asymptotic computational convention tests each uniform polynomial-time strategy at every
sufficiently long input, with a length threshold allowed to depend on that strategy. -/
inductive Soundness where
  | statistical | computational
  deriving DecidableEq

/-- A private-coin proof or argument for a function on bitstrings with a finite encoded range.
The fixed errors `δc` and `δs` lie in `[0,1]`. On every input the prescribed computable prover
claims the correct value and is accepted with probability at least `1 - δc`; its time need
not be polynomial. For a proof, every deterministic strategy claiming a wrong value on any
input is accepted with probability at most `δs`. For an argument, fix a deterministic strategy
with uniform polynomial-time Turing implementations of its claim and reply. There must be a
threshold for this strategy beyond which the same bound holds on *all* inputs on which its
claim is wrong. Input length is the asymptotic parameter; there is no negligible additive
slack. This eventual bound specifies a convention for Thaler's polynomial-time restriction
(Definition 3.2), not a threshold printed in that definition. -/
def IsSystem [Finite R] (kind : Soundness) (V : Verifier) (P : Strategy R)
    (f : List Bool → R) (δc δs : ℝ) : Prop :=
  δc ∈ Set.Icc 0 1 ∧ δs ∈ Set.Icc 0 1 ∧
  Nonempty (TM2Computable id bitEncode P.claim) ∧ Nonempty (TM2Computable id id P.reply) ∧
  (∀ x, P.claim x = f x ∧ 1 - δc ≤ V.acceptance P x) ∧
  match kind with
  | .statistical => ∀ (A : Strategy R) x, A.claim x ≠ f x → V.acceptance A x ≤ δs
  | .computational => ∀ (A : Strategy R),
      Nonempty (TM2ComputableInPolyTime id bitEncode A.claim) →
      Nonempty (TM2ComputableInPolyTime id id A.reply) →
      ∃ N : ℕ, ∀ x, N ≤ x.length → A.claim x ≠ f x → V.acceptance A x ≤ δs

/-- A proof for a function with finite encoded range gives an argument with the same
verifier, prescribed prover and errors: threshold zero suffices for every efficient strategy. -/
theorem IsSystem.toArgument [Finite R] {V : Verifier} {P : Strategy R} {f : List Bool → R}
    {δc δs : ℝ} (h : IsSystem .statistical V P f δc δs) :
    IsSystem .computational V P f δc δs := by
  obtain ⟨hc, hs, hclaim, hreply, hcomplete, hsound⟩ := h
  exact ⟨hc, hs, hclaim, hreply, hcomplete, fun A _ _ => ⟨0, fun x _ => hsound A x⟩⟩

end Cslib.Crypto.Interaction
