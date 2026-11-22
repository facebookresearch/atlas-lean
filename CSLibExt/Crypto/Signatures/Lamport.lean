/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF

/-!
# Lamport one-time signatures: a forgery inverts the one-way function

Fix a function `f : X → Y` and a message length `ℓ`. A Lamport secret key is a family of
preimages `sk (i, b) : X` for each position `i < ℓ` and bit `b`; the public key is
`pk (i, b) = f (sk (i, b))`. The signature on `m : Fin ℓ → Bool` reveals `sk (i, m i)` for every
`i`, and `(m, σ)` verifies when `f (σ i) = pk (i, m i)` for every `i`.

* `verify_sign`: honest signatures verify.
* `forgeGame f A : PMF Bool` is the one-time existential forgery experiment: the secret key is
  uniform, the forger `A` (random coins in a finite type `R`) sees the public key, obtains one
  signature on a message of its choice, and wins with a valid signature on a different message.
* `invertGame f I : PMF Bool` is the one-wayness experiment: `x` is uniform, and the inverter `I`
  wins when it outputs a preimage of `f x`.
* `invert A` plants `f x` at a uniform position `(i, b)` of an otherwise honest public key, aborts
  if the forger asks to sign a message with `m i = b`, and otherwise returns `σ' i` from the
  forgery when `m' i = b`.
* `forgeGame_le` (**Lamport's scheme is one-time secure if `f` is one-way**, Katz and Lindell,
  Theorem 12.16): `Pr[A forges] ≤ 2 ℓ · Pr[invert A inverts f]` for `ℓ ≥ 1`, an exact finite
  inequality.

The games are `PMF Bool` experiments and the bound is an inequality between success
probabilities.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.6.1.
-/

@[expose] public section

namespace Cslib.Crypto.Signatures.Lamport

open Finset

variable {X Y : Type*} (f : X → Y) {ℓ : ℕ}

/-- The public key of a secret key: `pk (i, b) = f (sk (i, b))`. -/
def publicKey (sk : Fin ℓ × Bool → X) : Fin ℓ × Bool → Y := fun ib => f (sk ib)

/-- The signature on `m` reveals `sk (i, m i)` for every position `i`. -/
def sign (sk : Fin ℓ × Bool → X) (m : Fin ℓ → Bool) : Fin ℓ → X := fun i => sk (i, m i)

/-- A signature `σ` on `m` is valid for `pk` when `f (σ i) = pk (i, m i)` for every `i`. -/
def Verify (pk : Fin ℓ × Bool → Y) (m : Fin ℓ → Bool) (σ : Fin ℓ → X) : Prop :=
  ∀ i, f (σ i) = pk (i, m i)

instance [DecidableEq Y] (pk : Fin ℓ × Bool → Y) (m : Fin ℓ → Bool) (σ : Fin ℓ → X) :
    Decidable (Verify f pk m σ) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- **Correctness**: honest signatures verify. -/
theorem verify_sign (sk : Fin ℓ × Bool → X) (m : Fin ℓ → Bool) :
    Verify f (publicKey f sk) m (sign sk m) := fun _ => rfl

/-- A one-time forger with random coins in `R`: from the public key it chooses a message to be
signed, and from the public key and that signature it outputs a message and a signature. -/
structure Forger (X Y R : Type*) (ℓ : ℕ) where
  /-- The message whose signature the forger requests. -/
  choose : (Fin ℓ × Bool → Y) → R → Fin ℓ → Bool
  /-- The forgery. -/
  forge : (Fin ℓ × Bool → Y) → (Fin ℓ → X) → R → (Fin ℓ → Bool) × (Fin ℓ → X)

variable [Fintype X] [Nonempty X] [DecidableEq Y] {R : Type*} [Fintype R] [Nonempty R]

/-- Whether the forger wins against the secret key `sk` with coins `r`: its output message
differs from the one it had signed, and the signature verifies. -/
def Forger.Wins (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R) : Prop :=
  (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).1 ≠
      A.choose (publicKey f sk) r ∧
    Verify f (publicKey f sk) (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).1
      (A.forge (publicKey f sk) (sign sk (A.choose (publicKey f sk) r)) r).2

instance (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R) : Decidable (A.Wins f sk r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The one-time forgery experiment: uniform secret key and coins. -/
noncomputable def forgeGame (A : Forger X Y R ℓ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin ℓ × Bool → X) × R)).map fun ω =>
    decide (A.Wins f ω.1 ω.2)

/-- The one-wayness experiment for an inverter with random coins in `Ω`: `x` is uniform, and the
inverter wins when it outputs a preimage of `f x`. -/
noncomputable def invertGame {Ω : Type*} [Fintype Ω] [Nonempty Ω] (I : Y → Ω → Option X) :
    PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (X × Ω)).map fun ω =>
    match I (f ω.1) ω.2 with
    | some x' => decide (f x' = f ω.1)
    | none => false

/-- The public key with `y` planted at position `ib` and `f (sk ·)` elsewhere. -/
def plant (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) (y : Y) : Fin ℓ × Bool → Y :=
  fun jc => if jc = ib then y else f (sk jc)

/-- The inverter built from a forger: with coins `(ib, sk, r)` it plants `y` at `ib = (i, b)`,
aborts if the requested message has `m i = b`, and otherwise answers with `σ' i` when the forged
message has `m' i = b`. -/
def invert (A : Forger X Y R ℓ) (y : Y) (ω : (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) :
    Option X :=
  if A.choose (plant f ω.2.1 ω.1 y) ω.2.2 ω.1.1 = ω.1.2 then none
  else if (A.forge (plant f ω.2.1 ω.1 y) (sign ω.2.1 (A.choose (plant f ω.2.1 ω.1 y) ω.2.2))
      ω.2.2).1 ω.1.1 = ω.1.2 then
    some ((A.forge (plant f ω.2.1 ω.1 y) (sign ω.2.1 (A.choose (plant f ω.2.1 ω.1 y) ω.2.2))
      ω.2.2).2 ω.1.1)
  else none

omit [Fintype X] [Nonempty X] [DecidableEq Y] in
private theorem map_uniform_toReal {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → Bool) :
    ((Cslib.Probability.PMF.uniformOfFintype Ω).map g true).toReal =
      (∑ ω, if g ω = true then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun ω _ => by split_ifs <;> simp)]
  rw [div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = true <;> simp [hg, eq_comm (a := true)]

/-- The inverter's success indicator. -/
private def invWin (A : Forger X Y R ℓ) (x : X) (ω : (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) :
    ℝ :=
  match invert f A (f x) ω with
  | some x' => if f x' = f x then 1 else 0
  | none => 0

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
private theorem plant_update (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) (x : X) (y : Y) :
    plant f (Function.update sk ib x) ib y = plant f sk ib y := by
  funext jc
  by_cases h : jc = ib <;> simp [plant, h]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
private theorem sign_update {sk : Fin ℓ × Bool → X} {ib : Fin ℓ × Bool} {m : Fin ℓ → Bool}
    (hm : m ib.1 ≠ ib.2) (x : X) : sign (Function.update sk ib x) m = sign sk m := by
  funext j
  refine Function.update_of_ne (fun h => hm ?_) _ _
  rw [← h]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- The inverter never reads the secret-key entry at the planted position. -/
private theorem invert_update (A : Forger X Y R ℓ) (y : Y) (ib : Fin ℓ × Bool)
    (sk : Fin ℓ × Bool → X) (r : R) (x : X) :
    invert f A y (ib, Function.update sk ib x, r) = invert f A y (ib, sk, r) := by
  by_cases h1 : A.choose (plant f sk ib y) r ib.1 = ib.2
  · simp only [invert, plant_update, h1, ↓reduceIte]
  · simp only [invert, plant_update, h1, ↓reduceIte, sign_update h1]

omit [Fintype X] [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- Planting `f (sk ib)` at `ib` gives the honest public key. -/
private theorem plant_self (sk : Fin ℓ × Bool → X) (ib : Fin ℓ × Bool) :
    plant f sk ib (f (sk ib)) = publicKey f sk := by
  funext jc
  by_cases h : jc = ib <;> simp [plant, publicKey, h]

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- If the forger wins against `sk`, the inverter run on the honest key with the guess
`(j, m' j)` at a position where the messages differ succeeds. -/
private theorem one_le_sum_invWin (A : Forger X Y R ℓ) (sk : Fin ℓ × Bool → X) (r : R)
    (hw : A.Wins f sk r) : 1 ≤ ∑ ib : Fin ℓ × Bool, invWin f A (sk ib) (ib, sk, r) := by
  obtain ⟨hne, hver⟩ := hw
  set m := A.choose (publicKey f sk) r
  set out := A.forge (publicKey f sk) (sign sk m) r
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hnonneg : ∀ ib, 0 ≤ invWin f A (sk ib) (ib, sk, r) := by
    intro ib
    simp only [invWin]
    split <;> [split_ifs <;> norm_num; exact le_rfl]
  have hone : invWin f A (sk (j, out.1 j)) ((j, out.1 j), sk, r) = 1 := by
    simp only [invWin, invert, plant_self]
    have h1 : ¬ A.choose (publicKey f sk) r j = out.1 j := fun h => hj h.symm
    simp only [h1, ↓reduceIte]
    change (match (if out.1 j = out.1 j then some (out.2 j) else none) with
      | some x' => if f x' = f (sk (j, out.1 j)) then (1 : ℝ) else 0 | none => 0) = 1
    simp only [↓reduceIte]
    simp only [show f (out.2 j) = f (sk (j, out.1 j)) from hver j, ↓reduceIte]
  calc (1 : ℝ) = invWin f A (sk (j, out.1 j)) ((j, out.1 j), sk, r) := hone.symm
    _ ≤ _ := single_le_sum (fun ib _ => hnonneg ib) (mem_univ _)

omit [Nonempty X] [DecidableEq Y] [Fintype R] [Nonempty R] in
/-- Re-randomizing one secret-key entry: `∑ x, ∑ sk, G (update sk ib x) = |X| · ∑ sk, G sk`. -/
private theorem sum_sum_update [DecidableEq (Fin ℓ × Bool)] (ib : Fin ℓ × Bool)
    (G : (Fin ℓ × Bool → X) → ℝ) :
    ∑ x : X, ∑ sk : Fin ℓ × Bool → X, G (Function.update sk ib x) =
      Fintype.card X * ∑ sk, G sk := by
  have hR : (Fintype.card X : ℝ) * ∑ sk, G sk = ∑ q : (Fin ℓ × Bool → X) × X, G q.1 := by
    rw [Fintype.sum_prod_type, mul_sum]
    simp [sum_const, Finset.card_univ]
  let e : X × (Fin ℓ × Bool → X) ≃ (Fin ℓ × Bool → X) × X :=
    { toFun := fun p => (Function.update p.2 ib p.1, p.2 ib)
      invFun := fun q => (q.1 ib, Function.update q.1 ib q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [hR, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ fun p => rfl

/-- **Lamport one-time signatures are secure if `f` is one-way** (Katz and Lindell,
Theorem 12.16): the forgery probability is at most `2 ℓ` times the probability that the inverter
built from the forger inverts `f`. -/
theorem forgeGame_le [NeZero ℓ] (A : Forger X Y R ℓ) :
    (forgeGame f A true).toReal ≤ 2 * ℓ * (invertGame f (invert f A) true).toReal := by
  classical
  rw [forgeGame, invertGame, map_uniform_toReal, map_uniform_toReal]
  have hcard : Fintype.card (X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R) =
      Fintype.card X * (2 * ℓ) * Fintype.card ((Fin ℓ × Bool → X) × R) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℝ) < Fintype.card ((Fin ℓ × Bool → X) × R) := by exact_mod_cast Fintype.card_pos
  -- the inverter's success sum, as a sum of `invWin`
  have hinv : (∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R,
      if (match invert f A (f ω.1) ω.2 with
        | some x' => decide (f x' = f ω.1)
        | none => false) = true then (1 : ℝ) else 0) =
      ∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R, invWin f A ω.1 ω.2 := by
    refine sum_congr rfl fun ω _ => ?_
    simp only [invWin]
    split <;> simp
  -- re-randomize the planted entry
  have hsum : ∑ ω : X × (Fin ℓ × Bool) × (Fin ℓ × Bool → X) × R, invWin f A ω.1 ω.2 =
      Fintype.card X * ∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (α₁ := Fin ℓ × Bool) (α₂ := (Fin ℓ × Bool → X) × R),
      Fintype.sum_prod_type (α₁ := Fin ℓ × Bool → X) (α₂ := R)]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun ib _ => ?_
    rw [← sum_sum_update ib (fun sk => ∑ r : R, invWin f A (sk ib) (ib, sk, r))]
    refine sum_congr rfl fun x _ => sum_congr rfl fun sk _ => sum_congr rfl fun r _ => ?_
    simp only [invWin, Function.update_self, invert_update]
  -- each winning `(sk, r)` contributes at least one successful guess
  have hwin : (∑ ω : (Fin ℓ × Bool → X) × R, if decide (A.Wins f ω.1 ω.2) = true then (1 : ℝ)
      else 0) ≤ ∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r) := by
    have hswap : (∑ ib : Fin ℓ × Bool, ∑ sk : Fin ℓ × Bool → X, ∑ r : R,
        invWin f A (sk ib) (ib, sk, r)) =
        ∑ sk : Fin ℓ × Bool → X, ∑ r : R, ∑ ib : Fin ℓ × Bool, invWin f A (sk ib) (ib, sk, r) := by
      rw [sum_comm]
      exact sum_congr rfl fun sk _ => sum_comm
    rw [hswap, Fintype.sum_prod_type (α₁ := Fin ℓ × Bool → X) (α₂ := R)]
    refine sum_le_sum fun sk _ => sum_le_sum fun r _ => ?_
    by_cases hw : A.Wins f sk r
    · simp only [hw, decide_true, ↓reduceIte]
      exact one_le_sum_invWin f A sk r hw
    · simp only [hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine sum_nonneg fun ib _ => ?_
      simp only [invWin]
      split <;> [split_ifs <;> norm_num; exact le_rfl]
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  rw [hinv, hsum, hcard, div_le_iff₀ hΩ]
  push_cast
  rw [show ∀ S : ℝ, 2 * ℓ * ((Fintype.card X * S) /
      (Fintype.card X * (2 * ℓ) * Fintype.card ((Fin ℓ × Bool → X) × R))) *
      Fintype.card ((Fin ℓ × Bool → X) × R) = S from fun S => by field_simp]
  exact hwin

end Cslib.Crypto.Signatures.Lamport
