/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.HMAC

/-!
# Tests for the Wave 1 hash files: CRHF/UOWHF games, full Merkle–Damgård, HMAC

* **Games.** `parity : Fin 4 → Bool` (`x ↦ x mod 2`, the key is ignored) collides on `0` and `2`:
  the finder that outputs `(0, 2)` has collision advantage exactly `1`, and so has the
  target-collision adversary committing to `1` and answering `3`. The identity on `Fin 4` is
  injective, so every finder has advantage `0`, and the identity family is collision resistant
  and target collision resistant against all adversary families (`HashFamily` imposes no
  compression condition).
* **Double-length-encoded Merkle–Damgård**, `n = L = 4`. `[1, 0, 1]` pads to the blocks `1011 1100`
  and is recovered by `unpad`. The compression function `dropFirst` ignores the first bit of each
  block, so `[1]` and `[0]` (padded to `1100 1000` and `0100 1000`) collide, and `findCollision`
  returns the first-block compression inputs; the block-count bound applies with `maxLen = 10`.
* **HMAC**, `n = 4` with a toy compression function `mix`: concrete tags (different keys and
  different messages give different tags), the nested form evaluated on both sides, a key and a
  message on which the nested form differs from NMAC over `fullHash`, correctness of
  verification, and rejection of a wrong tag.
* **HMAC in the Framework experiment.** A forger with point-mass (non-uniform) coins that queries
  `true` and replays the answer has Framework forgery advantage exactly `0` against HMAC on one-bit
  messages (computed through `macGame_hmacSchemeOn`), and the Framework bound
  `hmacSchemeOn_macAdvantage_le` applies to it; a no-query forger on `Msg 2`, relabeled into
  `List Bool`, outputs the bit string `[1]` and gets the `hmacScheme` bound
  `hmacScheme_macAdvantage_le`; for uniform coins, the bridge equates the Framework experiment
  with `PRF.macGame`, and `hmacSchemeOn_macAdvantage_le_of_uniform` gives the PRF-to-MAC bound
  for a two-message space.
-/

@[expose] public section

namespace Cslib.Crypto.HashWave1Tests

open Cslib.Crypto.Framework Cslib.Crypto.MerkleDamgard
  Cslib.Crypto.MerkleDamgardPadding Cslib.Crypto.MerkleDamgardFull Cslib.Crypto.HMAC

/-! ### CRHF / UOWHF games -/

/-- A keyed hash on `Fin 4` that ignores its key and keeps only the parity. -/
noncomputable def parity : HashFamily Bool (Fin 4) Bool where
  gen := Cslib.Probability.PMF.uniformOfFintype Bool
  hash _ x := decide (x.val % 2 = 1)

/-- The collision finder that always outputs `(0, 2)`. -/
noncomputable def parityFinder : CollisionFinder Bool (Fin 4) Unit where
  coins := PMF.pure ()
  find _ _ := (0, 2)

example : IsCollision (parity.hash true) (0, 2) := by decide

example : ¬ IsCollision (parity.hash true) (0, 1) := by decide

theorem collAdvantage_parityFinder : collAdvantage parity parityFinder = 1 :=
  collAdvantage_eq_one_of_forall parity parityFinder fun s r => by cases s <;> cases r <;> decide

/-- The target-collision adversary that commits to `1` and then answers `3`. -/
noncomputable def parityTCR : TCRAdversary Bool (Fin 4) Unit where
  coins := PMF.pure ()
  commit _ := 1
  find _ _ := 3

theorem tcrAdvantage_parityTCR : tcrAdvantage parity parityTCR = 1 := by
  rw [tcrAdvantage_eq_collAdvantage]
  exact collAdvantage_eq_one_of_forall _ _ fun s r => by cases s <;> cases r <;> decide

/-- The identity on `Fin 4`, an injective keyed hash. -/
noncomputable def identityHash : HashFamily Bool (Fin 4) (Fin 4) where
  gen := Cslib.Probability.PMF.uniformOfFintype Bool
  hash _ x := x

example : collAdvantage identityHash parityFinder = 0 :=
  collAdvantage_eq_zero_of_injective identityHash (fun _ => Function.injective_id) parityFinder

/-- The identity family is collision resistant against every adversary family, although it does
not compress: `HashFamily` imposes no compression condition. -/
theorem identity_collisionResistant :
    CollisionResistant (fun _ => identityHash) (fun _ => Unit) fun _ => True := fun A _ =>
  negligibleAdv_zero.mono fun n => (collAdvantage_eq_zero_of_injective identityHash
    (fun _ => Function.injective_id) (A n)).le

example : TargetCollisionResistant (fun _ => identityHash) (fun _ => Unit) fun _ => True :=
  TargetCollisionResistant.of_collisionResistant (fun _ _ => trivial)
    identity_collisionResistant

/-! ### Non-vacuity of the asymptotic notions -/

/-- The parity family is not collision resistant: `parityFinder` has advantage `1`. -/
example : ¬ CollisionResistant (fun _ => parity) (fun _ => Unit) fun _ => True := fun h =>
  not_negligibleAdv_const (δ := 1) one_pos <| by
    simpa [collAdvantage_parityFinder] using h (fun _ => parityFinder) trivial

/-- The parity family is not target collision resistant: `parityTCR` has advantage `1`. -/
example : ¬ TargetCollisionResistant (fun _ => parity) (fun _ => Unit) fun _ => True := fun h =>
  not_negligibleAdv_const (δ := 1) one_pos <| by
    simpa [tcrAdvantage_parityTCR] using h (fun _ => parityTCR) trivial

/-- With coin type `Empty` there is no collision finder (no `PMF Empty` exists), so the
unguarded statement holds vacuously, even for the parity family shown insecure above. -/
example : AsymptoticallySecure (Adv := fun _ => CollisionFinder Bool (Fin 4) Empty)
    (fun _ A => collAdvantage parity A) fun _ => True :=
  fun A _ => ((A 0).coins.support_nonempty.some).elim

/-- With the empty input type there is no collision finder (it must output two inputs). -/
example : AsymptoticallySecure (Adv := fun _ => CollisionFinder Bool Empty Unit)
    (fun _ A => collAdvantage (⟨PMF.pure true, fun _ x => x.elim⟩ : HashFamily Bool Empty Bool) A)
    fun _ => True :=
  fun A _ => ((A 0).find true ()).1.elim

/-! The two vacuous statements above cannot be stated as `CollisionResistant` or
`TargetCollisionResistant`: the nonemptiness hypotheses on the coin and input types fail to
synthesize. Without those hypotheses each `example` below elaborates with no error, and its
`#guard_msgs` fails. -/

/-- error: failed to synthesize instance of type class
  ∀ (n : ℕ), Nonempty Empty

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command. -/
#guard_msgs (whitespace := lax) in
example : Prop := CollisionResistant (fun _ => parity) (fun _ => Empty) fun _ => True

/-- error: failed to synthesize instance of type class
  ∀ (n : ℕ), Nonempty Empty

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command. -/
#guard_msgs (whitespace := lax) in
example : Prop := TargetCollisionResistant (fun _ => parity) (fun _ => Empty) fun _ => True

/-- error: failed to synthesize instance of type class
  ∀ (n : ℕ), Nonempty Empty

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command. -/
#guard_msgs (whitespace := lax) in
example : Prop := CollisionResistant
    (fun _ => (⟨PMF.pure true, fun _ x => x.elim⟩ : HashFamily Bool Empty Bool))
    (fun _ => Unit) fun _ => True

/-- Under the hypotheses of the notions there is an adversary of each kind. -/
example : Nonempty (CollisionFinder Bool (Fin 4) Unit) := CollisionFinder.nonempty

example : Nonempty (TCRAdversary Bool (Fin 4) Unit) := TCRAdversary.nonempty

/-! ### The double-length-encoded Merkle–Damgård transform -/

/-- A four-bit block. -/
abbrev V := List.Vector Bool 4

/-- The block `abcd`. -/
def v (a b c d : Bool) : V := ⟨[a, b, c, d], rfl⟩

example : padBlocks 4 4 [true, false, true] =
    [v true false true true, v true true false false] := by
  decide

example : blocks 2 [true, false, true, true] = [⟨[true, false], rfl⟩, ⟨[true, true], rfl⟩] := by
  decide

example : blocks 2 [true, false, true] = [⟨[true, false], rfl⟩] := by decide

example : blocksFuel 2 5 [true, false, true] = [⟨[true, false], rfl⟩] := by decide

example : unpad 4 (unblocks 4 (padBlocks 4 4 [true, false, true])) = [true, false, true] :=
  unpad_unblocks_padBlocks 4 4 (by decide) (by decide)

example : padBlocks 4 4 [true] ≠ padBlocks 4 4 [false] := by decide

example : (padBlocks 4 4 (List.replicate 9 true)).length < 16 :=
  length_padBlocks_lt 4 4 (maxLen := 10) (by decide) (by decide) (by decide)

/-- A compression function that ignores the first bit of each block:
`h(z, x) = z ⊕ (0 x₂ x₃ x₄)`. -/
def dropFirst (p : V × V) : V := xorBlock p.1 (v false (p.2.get 1) (p.2.get 2) (p.2.get 3))

example : fullHash dropFirst (v true false false true) (blockCountLenBlock 4) 4 [true] =
    fullHash dropFirst (v true false false true) (blockCountLenBlock 4) 4 [false] := by decide

example : findCollision dropFirst (v true false false true) (blockCountLenBlock 4)
    (padBlocks 4 4 [true]) (padBlocks 4 4 [false]) =
      some ((v true false false true, v true true false false),
        (v true false false true, v false true false false)) := by decide

example : ∃ p, findCollision dropFirst (v true false false true) (blockCountLenBlock 4)
    (padBlocks 4 4 [true]) (padBlocks 4 4 [false]) = some p ∧
      MerkleDamgard.IsCollision dropFirst p :=
  findCollision_fullHash dropFirst (v true false false true) (blockCountLenBlock 4) 4
    (maxLen := 10) (maxBlocks := 16) (by decide) (fun _ _ ha hb => blockCountLenBlock_injOn 4 ha hb)
    (by decide) (by decide) (by decide) (by decide) (by decide)

example (A : Bool → List Bool × List Bool) :
    fullCollisionGame dropFirst (v true false false true) (blockCountLenBlock 4) 4 10 A true ≤
      compressionCollisionGame dropFirst
        (reduction dropFirst (v true false false true) (blockCountLenBlock 4)
          (blockAdversary 4 4 A)) true :=
  fullCollisionGame_le dropFirst _ _ 4 (maxBlocks := 16) (by decide)
    (fun _ _ ha hb => blockCountLenBlock_injOn 4 ha hb) (by decide) A

/-- The keyed compression function `h^s(z, x) = dropFirst (z ⊕ s, x)`. -/
noncomputable def dropFirstFamily : HashFamily V (V × V) V where
  gen := Cslib.Probability.PMF.uniformOfFintype V
  hash s p := dropFirst (xorBlock p.1 s, p.2)

example (A : CollisionFinder V (Msg 10) Unit) :
    collAdvantage (mdFamily dropFirstFamily (v true false false true) (blockCountLenBlock 4) 4 10)
        A ≤ collAdvantage dropFirstFamily
          (mdReduction dropFirstFamily (v true false false true) (blockCountLenBlock 4) 4 A) :=
  collAdvantage_blockCount_le dropFirstFamily _ (by decide) (by decide) A

/-! ### HMAC -/

/-- A toy compression function on four-bit blocks. -/
def mix (p : V × V) : V :=
  List.Vector.ofFn fun i : Fin 4 =>
    xor (xor (p.1.get (i + 1)) (p.2.get i && !p.1.get i)) (p.2.get (i + 3))

/-- The inner pad `0110`. -/
def ipad : V := v false true true false

/-- The outer pad `1010`. -/
def opad : V := v true false true false

/-- The initial value `1001`. -/
def iv : V := v true false false true

/-- HMAC over `mix` with the block-count length block. -/
def tag (k : V) (m : List Bool) : V :=
  hmac mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad k m

example : tag (v true false false false) [true, false, true] = v true true false true := by decide

example : tag (v true true false false) [true, false, true] = v false false false false := by
  decide

example : tag (v true true false false) [true, false, false] = v false true false true := by decide

example : tag (v true true false false) [true, false, true] ≠
    tag (v true false false false) [true, false, true] := by decide

example : tag (v true false false false) [true, false, true] =
    nestedContHash mix (blockCountLenBlock 4) 4 List.Vector.toList
      (innerKey mix iv ipad (v true false false false))
      (outerKey mix iv opad (v true false false false)) [true, false, true] := by decide

example (k : V) (m : List Bool) : tag k m =
    nestedContHash mix (blockCountLenBlock 4) 4 List.Vector.toList (innerKey mix iv ipad k)
      (outerKey mix iv opad k) m :=
  hmac_eq_nestedContHash mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad (by decide)
    k m

/-- The nested form is not NMAC over `fullHash`: for the key `0000` and the empty message, HMAC,
i.e. the nested continuation hash with the derived keys, is `0000`, while `fullHash` started at the
derived chaining values (which pads the message alone) gives `1001`. -/
example : tag (v false false false false) [] = v false false false false ∧
    fullHash mix (outerKey mix iv opad (v false false false false)) (blockCountLenBlock 4) 4
        (List.Vector.toList (fullHash mix (innerKey mix iv ipad (v false false false false))
          (blockCountLenBlock 4) 4 [])) = v true false false true := by
  decide

example : innerKey mix iv ipad (v true false false false) ≠
    innerKey mix iv ipad (v true true false false) := by decide

example : (hmacScheme mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad).verify
    (v true false false false) [true, false, true] (v true true false true) = true := by
  decide

example : (hmacScheme mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad).verify
    (v true false false false) [true, false, true] (v false false false false) = false := by
  decide

example : (hmacScheme mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad).Correct :=
  hmacScheme_correct mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad

/-! ### HMAC in the Framework forgery experiment -/

/-- HMAC on one-bit messages `x ↦ [x]`. -/
noncomputable abbrev hmacBit : MACScheme Bool V V :=
  hmacSchemeOn mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad fun x => [x]

/-- A forger with point-mass coins `true : Bool` (not uniform on `Bool`): it queries `true` and
outputs the answer as its forgery on `true`. -/
noncomputable def replayForger : MACForger Bool V Bool where
  coins := PMF.pure true
  forge _ := OracleComp.query true fun t => OracleComp.done (true, t)

/-- The replayed tag verifies, but `true` was queried, so the forgery never counts. -/
example : macAdvantage hmacBit replayForger = 0 := by
  have hw : ∀ k : V, ¬ PRF.MacWins
      (fun x => hmac mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad k [x])
      (replayForger.forge true) :=
    fun _ h => h.2 (List.mem_singleton_self true)
  rw [macAdvantage, macGame_hmacSchemeOn, show replayForger.coins = PMF.pure true from rfl,
    PMF.pure_bind, PRF.macGame]
  simpa [winProb_map_uniform] using hw

example : ∃ r ∈ replayForger.coins.support, macAdvantage hmacBit replayForger ≤
    PRF.prfAdvantage (fun k (x : Bool) => tag k [x])
      (fun _ : Unit => PRF.macReduction [] (replayForger.forge r)) + 1 / 16 := by
  obtain ⟨r, hr, h⟩ := hmacSchemeOn_macAdvantage_le mix iv (blockCountLenBlock 4) 4
    List.Vector.toList ipad opad (fun x : Bool => [x]) replayForger
  have hc : Fintype.card V = 16 := by simp [V, card_vector]
  exact ⟨r, hr, by rwa [hc, Nat.cast_ofNat] at h⟩

/-- A no-query forger on messages shorter than `2` bits: it outputs the message `[1]` with the tag
`0000`. -/
noncomputable def guessForger : MACForger (Msg 2) V Unit where
  coins := PMF.pure ()
  forge _ := OracleComp.done (⟨[true], by decide⟩, v false false false false)

/-- Relabeled into `List Bool`, the forger outputs the bit string `[1]`. -/
example (O : List Bool → V) :
    ((guessForger.relabel Subtype.val).forge ()).run O = ([true], v false false false false) :=
  rfl

example : ∃ r ∈ guessForger.coins.support,
    macAdvantage (hmacScheme mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad)
        (guessForger.relabel Subtype.val) ≤
      PRF.prfAdvantage (fun k (x : Msg 2) => tag k x.1)
        (fun _ : Unit => PRF.macReduction [] (guessForger.forge r)) + 1 / 16 := by
  obtain ⟨r, hr, h⟩ := hmacScheme_macAdvantage_le mix iv (blockCountLenBlock 4) 4
    List.Vector.toList ipad opad 2 guessForger
  have hc : Fintype.card V = 16 := by simp [V, card_vector]
  exact ⟨r, hr, by rwa [hc, Nat.cast_ofNat] at h⟩

/-- With uniform coins, the Framework experiment is the PRF file's `PRF.macGame`. -/
example (A : Unit → PRF.OracleComp Bool V (Bool × V)) :
    macGame hmacBit ⟨Cslib.Probability.PMF.uniformOfFintype Unit, A⟩ =
      PRF.macGame (fun k (x : Bool) => tag k [x]) A :=
  macGame_hmacSchemeOn_of_uniform mix iv (blockCountLenBlock 4) 4 List.Vector.toList ipad opad
    _ ⟨_, A⟩ rfl

/-- With uniform coins, the Framework forgery advantage is bounded by the PRF advantage of the
distinguisher over the same coins, plus `1 / |V| = 1 / 16`. -/
example (A : Unit → PRF.OracleComp Bool V (Bool × V)) :
    macAdvantage hmacBit ⟨Cslib.Probability.PMF.uniformOfFintype Unit, A⟩ ≤
      PRF.prfAdvantage (fun k (x : Bool) => tag k [x]) (fun r => PRF.macReduction [] (A r)) +
        1 / 16 := by
  have h := hmacSchemeOn_macAdvantage_le_of_uniform mix iv (blockCountLenBlock 4) 4
    List.Vector.toList ipad opad (fun x : Bool => [x]) ⟨_, A⟩ rfl
  have hc : Fintype.card V = 16 := by simp [V, card_vector]
  rwa [hc, Nat.cast_ofNat] at h

end Cslib.Crypto.HashWave1Tests
