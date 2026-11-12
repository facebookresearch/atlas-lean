/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Signatures.MerkleSignatures
public import Mathlib.Data.Nat.Pairing

/-!
# Tests for Merkle signatures

The generic `OracleComp.runStateful` and `queryAt` tests live in
`CSLibExtTest/Crypto/Framework/OracleTests.lean`.

**Merkle signatures.** Lamport keys on `2`-bit messages with `f x = x + 1` on `Fin 4`, three
one-time keys (an odd number, so the tree promotes a node), leaf hash `H` (base-4 digits of the
Lamport public key) and node hash `Nat.pair`. The signature at counter `1` verifies; it is
rejected on another message, at another index, and with a tampered path; there is no signature at
counter `3`. Both hashes are injective, so the key-mismatch event is empty.

**A forger and the reduction.** With `f = id` on `Bool`, `ℓ = 1` and `N = 2`, a public Lamport key
reveals its secret key, so the forger that asks for one signature reads the secret key from it and
forges on the other message: it wins on every key. The reduction wins when it guesses the
forgery's index `0` and loses when it guesses `1`, which is why the bound loses the factor `N`.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleSignaturesTests

open Finset Cslib.Crypto.Framework

/-! ### Merkle signatures -/

section MerkleSignatures

open Cslib.Crypto.Signatures Cslib.Crypto.Signatures.MerkleSig

/-- The one-way function of the Lamport keys. -/
def f4 (x : Fin 4) : Fin 4 := x + 1

/-- The leaf hash: the base-4 digits of a Lamport public key. -/
def H4 (pk : Fin 2 × Bool → Fin 4) : ℕ :=
  (pk (0, false)).val + 4 * (pk (0, true)).val + 16 * (pk (1, false)).val +
    64 * (pk (1, true)).val

/-- Three Lamport secret keys. -/
def sk3 : Fin 3 → Fin 2 × Bool → Fin 4 :=
  fun i ib => ⟨(i.val + 2 * ib.1.val + if ib.2 then 1 else 0) % 4, Nat.mod_lt _ (by decide)⟩

/-- The message `10`. -/
def m₁ : Fin 2 → Bool := ![true, false]

/-- The signature at counter `1` on `m₁`. -/
def σ₁ : Signature (Fin 4) (Fin 4) ℕ 2 :=
  ((sign f4 H4 Nat.pair sk3 1 m₁).get (by decide))

/-- **Correctness**, from `verify_sign`. -/
example : verify f4 H4 Nat.pair 3 (publicKey f4 H4 Nat.pair sk3) m₁ σ₁ = true :=
  verify_sign f4 H4 Nat.pair sk3 (i := 1) (Option.some_get _).symm

example : verify f4 H4 Nat.pair 3 (publicKey f4 H4 Nat.pair sk3) m₁ σ₁ = true := by decide

example : σ₁.index = 1 ∧ σ₁.path.length = 2 := by decide

/-- A forgery attempt: the signature on `m₁` does not verify on `01`. -/
example : verify f4 H4 Nat.pair 3 (publicKey f4 H4 Nat.pair sk3) ![false, true] σ₁ = false := by
  decide

/-- The same Lamport signature claimed at another index is rejected. -/
example : verify f4 H4 Nat.pair 3 (publicKey f4 H4 Nat.pair sk3) m₁ { σ₁ with index := 0 } =
    false := by
  decide

/-- A tampered authentication path is rejected. -/
example : verify f4 H4 Nat.pair 3 (publicKey f4 H4 Nat.pair sk3) m₁
    { σ₁ with path := σ₁.path.map (· + 1) } = false := by
  decide

/-- The three keys are used up: no signature at counter `3`. -/
example : sign f4 H4 Nat.pair sk3 3 m₁ = none := by decide

example : ¬ (sign f4 H4 Nat.pair sk3 3 m₁).isSome := by
  rw [isSome_sign]
  decide

theorem pair_injective : Function.Injective (Function.uncurry Nat.pair) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hp
  simp only [Function.uncurry_apply_pair, Nat.pair_eq_pair] at hp
  rw [hp.1, hp.2]

theorem H4_injective : Function.Injective H4 := by
  intro p q hpq
  have h0 := (p (0, false)).isLt
  have h1 := (p (0, true)).isLt
  have h2 := (p (1, false)).isLt
  have h3 := (p (1, true)).isLt
  have h4 := (q (0, false)).isLt
  have h5 := (q (0, true)).isLt
  have h6 := (q (1, false)).isLt
  have h7 := (q (1, true)).isLt
  simp only [H4] at hpq
  funext ⟨i, b⟩
  apply Fin.ext
  fin_cases i <;> cases b <;> simp <;> omega

/-- For these injective hashes, the forgery probability of any forger against the three-key
scheme is at most `3` times that of the Lamport forger built from it. -/
example (F : Forger (Fin 4) (Fin 4) ℕ Unit 2) :
    winProb (forgeGame f4 H4 Nat.pair 3 F) ≤
      3 * winProb (Lamport.forgeGame f4 (reduction f4 H4 Nat.pair 3 F)) := by
  exact_mod_cast winProb_forgeGame_le_of_injective f4 H4 Nat.pair 3 F pair_injective H4_injective

/-! #### A forger against `f = id` and the reduction -/

/-- The leaf hash on `1`-bit Lamport keys over `Bool`. -/
def Hb (pk : Fin 1 × Bool → Bool) : ℕ := (pk (0, false)).toNat + 2 * (pk (0, true)).toNat

/-- The forger: ask for a signature on `0`; the Lamport key in the answer is the secret key
(`f = id`), so sign `1` with it, reusing the index and the authentication path. -/
def idForger : Forger Bool Bool ℕ Unit 1 where
  forge _ _ := .liftBind ![false] fun ans => .pure <|
    match ans with
    | some s => (![true], ⟨s.index, s.pk, fun _ => s.pk (0, true), s.path⟩)
    | none => (![true], ⟨0, fun _ => false, fun _ => false, []⟩)

/-- Two keys for `f = id`. -/
def skb : Fin 2 → Fin 1 × Bool → Bool := fun i ib => decide (i.val = 0) && ib.2

example : win (id : Bool → Bool) Hb Nat.pair idForger skb () = true := by decide

/-- The forger wins on every key: its forgery probability is `1`. -/
example : winProb (forgeGame (id : Bool → Bool) Hb Nat.pair 2 idForger) = 1 := by
  rw [forgeGame, winProb_map_uniform]
  have hc : (univ.filter fun ω : (Fin 2 → Fin 1 × Bool → Bool) × Unit =>
      win (id : Bool → Bool) Hb Nat.pair idForger ω.1 ω.2 = true) = univ := by decide
  rw [hc, card_univ]
  have : (Fintype.card ((Fin 2 → Fin 1 × Bool → Bool) × Unit) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self this

/-- The reduction wins when it guesses the forgery's index `0` (the forgery uses key `0`). -/
example : (reduction (id : Bool → Bool) Hb Nat.pair 2 idForger).Wins id (skb 0) (0, skb, ()) := by
  decide

/-- The reduction loses when it guesses index `1`: the forgery is under the reduction's own key
`0`, not under the challenge key. -/
example : ¬ (reduction (id : Bool → Bool) Hb Nat.pair 2 idForger).Wins id (fun _ => false)
    (1, skb, ()) := by
  decide

end MerkleSignatures

end Cslib.Crypto.MerkleSignaturesTests
