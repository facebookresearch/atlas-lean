/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.Framework.Oracle
public import CSLibExt.Crypto.Hash.MerkleTree
public import CSLibExt.Crypto.Signatures.Lamport

/-!
# Merkle signatures: many-time signatures from Lamport one-time signatures and a Merkle tree

Fix a one-way function `f : X → Y` for Lamport's scheme on `ℓ`-bit messages, a leaf hash
`H : (Fin ℓ × Bool → Y) → A` compressing a Lamport public key to a tree node, and a two-to-one
hash `h : A → A → A`. The signer holds `N` Lamport secret keys `sk : Fin N → (Fin ℓ × Bool → X)`.
The leaves of the Merkle tree are the hashed Lamport public keys, and the public key is the
Merkle root (`publicKey`). The scheme is **stateful**: the `i`-th signature (`i < N`) uses the
`i`-th Lamport key, and is the tuple (index `i`, Lamport public key `pk_i`, Lamport signature of
the message under `sk_i`, Merkle authentication path of leaf `i`) (`sign`). Verification checks the
Lamport signature against `pk_i` and the authentication path of `H pk_i` against the root
(`verify`).

* `verify_sign` (**correctness**): every signature produced by the signer verifies.
* `verify_sound`: a verifying signature at index `i` is a valid Lamport signature under the
  key it carries, and that key is the honest `pk_i`, or `h` or `H` has a collision (the
  leaf-or-collision form of `MerkleTree.verify_sound`).
* `forgeGame N F`: the existential forgery experiment against the stateful signer. Keys and the
  forger's coins (in a finite type `R`) are uniform; the forger `F` sees the root and adaptively
  queries a signing oracle that answers its `i`-th query with the `i`-th signature (and `none` once
  the `N` keys are used up, so the forger may ask any number of queries); it wins with a verifying
  signature on a message it never queried.
* `keyMismatchGame N F`: the **key-mismatch (bad) event**, in which the forger wins with a signature
  whose Lamport key is not the honest one at its index. `collision_of_keyMismatchGame` shows that
  each such run exhibits a collision of `h` or `H` (an existence statement), and
  `winProb_keyMismatchGame_eq_zero` shows the event is empty for injective hashes.
* `reduction N F`: a Lamport one-time forger. It guesses the index `j` of the forgery, plants the
  challenge Lamport public key at leaf `j`, generates the other `N - 1` keys itself, answers the
  `j`-th signing query with its single Lamport signing query, and outputs the Lamport part of the
  forgery.
* `winProb_forgeGame_le` (**forgery bound up to the bad event**): for `ℓ ≥ 1` and `N ≥ 1`,
  `Pr[F forges] ≤ N · Pr[reduction N F forges Lamport] + Pr[keyMismatchGame]`.
  `winProb_forgeGame_le_invert` composes the bound with `Lamport.forgeGame_le`, and
  `winProb_forgeGame_le_of_injective` drops the bad event for injective hashes.

**What is not proved: EUF security under collision resistance.** The bad-event term is the
original forger's key-mismatch probability, not the advantage of a collision finder. No
collision-extraction reduction is constructed: `collision_of_keyMismatchGame` only says that a
collision exists. For compressing `H` or `h` collisions always exist, so `winProb_forgeGame_le`
and `winProb_forgeGame_le_invert` are intermediate bad-event bounds, not EUF-security theorems.
Bounding the bad event by a collision finder's advantage needs an explicit extractor from a
verifying authentication path for the wrong leaf (the Wave-2 item recorded at
`MerkleTree.verify_sound`). `winProb_forgeGame_le_of_injective` is a complete reduction to Lamport
one-time security, but only for injective hashes, which cannot compress (an injective
`h : A → A → A` needs an infinite or trivial `A`).

The games use uniform coins over finite types, like `Lamport.forgeGame`; the Framework's
`SigScheme` and `sigGame` model stateless signers, so the stateful signer is run by the
Framework's `OracleComp.runStateful`, which feeds the query counter to the signing function.
Wave 2: express the scheme with a stateful-signer extension of `SigScheme`, and unify `Collides`
and `MerkleTree.HasCollision` with the hash lane's collision-resistance game.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 12.6 (signatures from hash functions: Lamport's one-time scheme, Section 12.6.1, and
  stateful many-time signatures built from one-time signatures) and Section 5.6.2 (Merkle trees).
* R. C. Merkle, *A certified digital signature*, CRYPTO '89, LNCS 435, 1990.
-/

@[expose] public section

namespace Cslib.Crypto.Signatures.MerkleSig

open Finset Cslib.Crypto.Framework
open Cslib.Crypto.Framework.OracleComp (runStateful queryAt queryAt_congr runStateful_congr
  mem_of_queryAt)

/-! ### The scheme -/

/-- A Merkle signature: the index of the Lamport key used, that Lamport public key, the Lamport
signature, and the Merkle authentication path of the key's leaf. -/
structure Signature (X Y A : Type*) (ℓ : ℕ) where
  /-- The index of the one-time key (the signer's counter). -/
  index : ℕ
  /-- The Lamport public key at that index. -/
  pk : Fin ℓ × Bool → Y
  /-- The Lamport signature on the message. -/
  sig : Fin ℓ → X
  /-- The authentication path of leaf `index`. -/
  path : List A

/-- The hash `H` has a collision: two distinct inputs with the same hash. Wave 2: unify with the
hash lane's collision-resistance (CRHF) game. -/
def Collides {B A : Type*} (H : B → A) : Prop := ∃ a b, a ≠ b ∧ H a = H b

variable {X Y A : Type*} {ℓ : ℕ} (f : X → Y) (H : (Fin ℓ × Bool → Y) → A) (h : A → A → A)

/-- The Merkle leaves: the hashes of a family of `N` Lamport public keys. -/
def leavesOf {N : ℕ} (pks : Fin N → Fin ℓ × Bool → Y) : List A := List.ofFn fun i => H (pks i)

/-- The Merkle root over a family of Lamport public keys. -/
def rootOf {N : ℕ} (pks : Fin N → Fin ℓ × Bool → Y) : Option A :=
  MerkleTree.root h (leavesOf H pks)

/-- The stateful signer for the Lamport public keys `pks`, with `sg i m` the Lamport signature
on `m` under key `i`: at counter `i < N` it returns `(i, pks i, sg i m, authPath i)`; once the
keys are used up it returns `none`. -/
def signerOf {N : ℕ} (pks : Fin N → Fin ℓ × Bool → Y) (sg : Fin N → (Fin ℓ → Bool) → Fin ℓ → X)
    (i : ℕ) (m : Fin ℓ → Bool) : Option (Signature X Y A ℓ) :=
  if hi : i < N then some ⟨i, pks ⟨i, hi⟩, sg ⟨i, hi⟩ m, MerkleTree.authPath h (leavesOf H pks) i⟩
  else none

/-- The Lamport public keys of a family of Lamport secret keys. -/
def lamportKeys {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X) : Fin N → Fin ℓ × Bool → Y :=
  fun i => Lamport.publicKey f (sk i)

/-- The public key: the Merkle root over the hashed Lamport public keys (`none` when `N = 0`). -/
def publicKey {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X) : Option A := rootOf H h (lamportKeys f sk)

/-- The stateful signing algorithm: the signature at counter `i` uses the `i`-th Lamport key. -/
def sign {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X) :
    ℕ → (Fin ℓ → Bool) → Option (Signature X Y A ℓ) :=
  signerOf H h (lamportKeys f sk) fun i => Lamport.sign (sk i)

/-- Verification against the root `pk` of an `n`-leaf tree: the Lamport signature verifies under
the Lamport key carried by the signature, and the authentication path of that key's leaf verifies
against the root. -/
def verify [DecidableEq Y] [DecidableEq A] (n : ℕ) (pk : Option A) (m : Fin ℓ → Bool)
    (σ : Signature X Y A ℓ) : Bool :=
  match pk with
  | some r =>
    decide (Lamport.Verify f σ.pk m σ.sig) && MerkleTree.verify h n σ.index (H σ.pk) σ.path r
  | none => false

/-- There is one leaf per Lamport key. -/
theorem length_leavesOf {N : ℕ} (pks : Fin N → Fin ℓ × Bool → Y) : (leavesOf H pks).length = N :=
  List.length_ofFn

/-- Leaf `i` is the hash of the `i`-th Lamport public key. -/
theorem getElem?_leavesOf {N : ℕ} (pks : Fin N → Fin ℓ × Bool → Y) {i : ℕ} (hi : i < N) :
    (leavesOf H pks)[i]? = some (H (pks ⟨i, hi⟩)) := by
  simp [leavesOf, hi]

/-- Iterating `MerkleTree.level` keeps a nonempty list nonempty. -/
theorem iterate_level_ne_nil : ∀ (k : ℕ) {l : List A}, l ≠ [] → (MerkleTree.level h)^[k] l ≠ []
  | 0, _, hl => hl
  | k + 1, l, hl => by
    rw [Function.iterate_succ_apply]
    apply iterate_level_ne_nil k
    apply List.ne_nil_of_length_pos
    rw [MerkleTree.length_level]
    have := List.length_pos_of_ne_nil hl
    omega

/-- A nonempty list of leaves has a root. -/
theorem exists_root_eq_some {l : List A} (hl : l ≠ []) : ∃ r, MerkleTree.root h l = some r := by
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil (iterate_level_ne_nil h (Nat.clog 2 l.length) hl)
  exact ⟨a, by rw [MerkleTree.root, ht, List.head?_cons]⟩

/-- The signer returns a signature exactly while keys remain. -/
theorem isSome_sign {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X) (i : ℕ) (m : Fin ℓ → Bool) :
    (sign f H h sk i m).isSome ↔ i < N := by
  unfold sign signerOf
  split_ifs with hi <;> simp [hi]

/-- **Correctness**: every signature produced by the signer verifies against the public key. -/
theorem verify_sign [DecidableEq Y] [DecidableEq A] {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X)
    {i : ℕ} {m : Fin ℓ → Bool} {σ : Signature X Y A ℓ} (hσ : sign f H h sk i m = some σ) :
    verify f H h N (publicKey f H h sk) m σ = true := by
  unfold sign signerOf at hσ
  split_ifs at hσ with hi
  obtain rfl := Option.some.inj hσ
  have hne : leavesOf H (lamportKeys f sk) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [length_leavesOf]; omega)
  obtain ⟨r, hr⟩ := exists_root_eq_some h hne
  have hM := MerkleTree.verify_authPath h (getElem?_leavesOf H (lamportKeys f sk) hi) hr
  rw [length_leavesOf] at hM
  simp only [publicKey, rootOf, hr, verify, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Lamport.verify_sign f _ m, hM⟩

/-- **Soundness of verification**: a signature that verifies against the honest public key carries
a valid Lamport signature under its Lamport key, its index is in range, and that key is the honest
key at its index, or `h` or `H` has a collision. -/
theorem verify_sound [DecidableEq Y] [DecidableEq A] {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X)
    {m : Fin ℓ → Bool} {σ : Signature X Y A ℓ}
    (hv : verify f H h N (publicKey f H h sk) m σ = true) :
    Lamport.Verify f σ.pk m σ.sig ∧ ∃ hi : σ.index < N,
      σ.pk = Lamport.publicKey f (sk ⟨σ.index, hi⟩) ∨ MerkleTree.HasCollision h ∨ Collides H := by
  rcases hr : publicKey f H h sk with _ | r
  · simp [hr, verify] at hv
  · rw [hr] at hv
    simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hL, hM⟩ := hv
    have hi := ((MerkleTree.verify_eq_true_iff h).1 hM).1
    refine ⟨hL, hi, ?_⟩
    rw [← length_leavesOf H (lamportKeys f sk)] at hM
    rcases MerkleTree.verify_sound h hr hM with hl | hc
    · rw [getElem?_leavesOf H _ hi] at hl
      by_cases hpk : σ.pk = Lamport.publicKey f (sk ⟨σ.index, hi⟩)
      · exact Or.inl hpk
      · exact Or.inr (Or.inr ⟨_, _, hpk, (Option.some.inj hl).symm⟩)
    · exact Or.inr (Or.inl hc)

/-! ### The forgery experiment -/

/-- An adaptive forger against the stateful Merkle signer, with random coins in `R`: from the
public key (the root) and its coins it queries the signing oracle, whose answers are
`Option (Signature X Y A ℓ)` (`none` once the keys are used up), and outputs a message and a
signature. -/
structure Forger (X Y A R : Type*) (ℓ : ℕ) where
  /-- The forger, as an oracle computation from the root and the coins. -/
  forge : Option A → R →
    OracleComp (Fin ℓ → Bool) (Option (Signature X Y A ℓ)) ((Fin ℓ → Bool) × Signature X Y A ℓ)

section Game

variable {R : Type*}

/-- The run of the forger against the honest stateful signer with keys `sk` and coins `r`: its
output and the transcript of its signing queries. -/
def run {N : ℕ} (F : Forger X Y A R ℓ) (sk : Fin N → Fin ℓ × Bool → X) (r : R) :
    ((Fin ℓ → Bool) × Signature X Y A ℓ) ×
      List ((Fin ℓ → Bool) × Option (Signature X Y A ℓ)) :=
  runStateful (sign f H h sk) 0 (F.forge (publicKey f H h sk) r)

variable [DecidableEq Y] [DecidableEq A]

/-- The forger wins: its signature verifies and its message was never queried. -/
def win {N : ℕ} (F : Forger X Y A R ℓ) (sk : Fin N → Fin ℓ × Bool → X) (r : R) : Bool :=
  let o := run f H h F sk r
  verify f H h N (publicKey f H h sk) o.1.1 o.1.2 && !decide (o.1.1 ∈ o.2.map Prod.fst)

/-- The Lamport key carried by the signature `σ` is the honest key at its index. -/
def keyMatches {N : ℕ} (sk : Fin N → Fin ℓ × Bool → X) (σ : Signature X Y A ℓ) : Bool :=
  if hi : σ.index < N then decide (σ.pk = Lamport.publicKey f (sk ⟨σ.index, hi⟩)) else false

variable [Fintype X] [Nonempty X] [Fintype R] [Nonempty R]

/-- The **existential forgery experiment** against the `N`-key stateful Merkle signer (Katz and
Lindell's `Sig-forge`, Definition 12.2, for a stateful scheme): uniform keys and coins, and the
experiment outputs whether the forger wins. -/
noncomputable def forgeGame (N : ℕ) (F : Forger X Y A R ℓ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin N → Fin ℓ × Bool → X) × R)).map fun ω =>
    win f H h F ω.1 ω.2

/-- The **key-mismatch event**, a bad event of the forgery experiment (not a collision-finding
experiment): the forger wins with a signature whose Lamport key is not the honest key at its index.
Its probability is the original forger's; nothing here bounds it by a collision finder's
advantage. The forger is run once per sample. -/
noncomputable def keyMismatchGame (N : ℕ) (F : Forger X Y A R ℓ) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype ((Fin N → Fin ℓ × Bool → X) × R)).map fun ω =>
    let o := run f H h F ω.1 ω.2
    (verify f H h N (publicKey f H h ω.1) o.1.1 o.1.2 && !decide (o.1.1 ∈ o.2.map Prod.fst)) &&
      !keyMatches f ω.1 o.1.2

/-- `keyMismatchGame` in terms of `win` and `keyMatches`. -/
theorem keyMismatchGame_eq (N : ℕ) (F : Forger X Y A R ℓ) :
    keyMismatchGame f H h N F =
      (Cslib.Probability.PMF.uniformOfFintype ((Fin N → Fin ℓ × Bool → X) × R)).map fun ω =>
        win f H h F ω.1 ω.2 && !keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2 :=
  rfl

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- Every run in the key-mismatch event exhibits a collision of `h` or of `H`. This is an
existence statement, not a collision finder: the collision is not computed from the run, and for
compressing hashes a collision exists whatever the forger does. -/
theorem collision_of_keyMismatchGame {N : ℕ} (F : Forger X Y A R ℓ)
    (sk : Fin N → Fin ℓ × Bool → X) (r : R)
    (hb : (win f H h F sk r && !keyMatches f sk (run f H h F sk r).1.2) = true) :
    MerkleTree.HasCollision h ∨ Collides H := by
  simp only [win, Bool.and_eq_true, Bool.not_eq_true'] at hb
  obtain ⟨⟨hv, -⟩, hk⟩ := hb
  obtain ⟨-, hi, hpk | hc⟩ := verify_sound f H h sk hv
  · simp [keyMatches, hi, hpk] at hk
  · exact hc

/-- For injective hashes the key-mismatch event has probability `0`. -/
theorem winProb_keyMismatchGame_eq_zero (N : ℕ) (F : Forger X Y A R ℓ)
    (hh : Function.Injective (Function.uncurry h)) (hH : Function.Injective H) :
    winProb (keyMismatchGame f H h N F) = 0 := by
  rw [keyMismatchGame_eq, winProb_map_uniform, div_eq_zero_iff]
  left
  norm_cast
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ω _ hb
  rcases collision_of_keyMismatchGame f H h F ω.1 ω.2 hb with hc | ⟨a, b, hab, he⟩
  · exact MerkleTree.not_hasCollision_of_injective h hh hc
  · exact hab (hH he)

end Game

/-! ### The reduction to Lamport one-time security -/

section Reduction

variable {R : Type*} {N : ℕ}

/-- The reduction's Lamport public keys: the challenge key `pkStar` at the guessed index `j`, and
the public keys of its own secret keys `skO` elsewhere. -/
def simKeys (pkStar : Fin ℓ × Bool → Y) (j : Fin N) (skO : Fin N → Fin ℓ × Bool → X) :
    Fin N → Fin ℓ × Bool → Y :=
  fun i => if i = j then pkStar else Lamport.publicKey f (skO i)

/-- The reduction's signing oracle: at index `j` it signs with `σj`, elsewhere with its own keys. -/
def redSigner (pkStar : Fin ℓ × Bool → Y) (j : Fin N) (skO : Fin N → Fin ℓ × Bool → X)
    (σj : (Fin ℓ → Bool) → Fin ℓ → X) : ℕ → (Fin ℓ → Bool) → Option (Signature X Y A ℓ) :=
  signerOf H h (simKeys f pkStar j skO) fun i m => if i = j then σj m else Lamport.sign (skO i) m

/-- The reduction's message for its one Lamport signing query: the forger's `j`-th signing query,
or, if the forger asks fewer queries, the complement of the forger's output message. The
simulation up to query `j` does not need the Lamport signature, so `σj` is a placeholder. -/
def redChoose (F : Forger X Y A R ℓ) (pkStar : Fin ℓ × Bool → Y)
    (ω : Fin N × (Fin N → Fin ℓ × Bool → X) × R) : Fin ℓ → Bool :=
  let sJ := redSigner f H h pkStar ω.1 ω.2.1 (Lamport.sign (ω.2.1 ω.1))
  let c := F.forge (rootOf H h (simKeys f pkStar ω.1 ω.2.1)) ω.2.2
  match queryAt sJ 0 c ω.1 with
  | some m => m
  | none => let o := (runStateful sJ 0 c).1.1; fun t => !(o t)

/-- The reduction's forgery: run the forger, answering the `j`-th query with the Lamport signature
`σ`, and output the Lamport part of its forgery. -/
def redForge (F : Forger X Y A R ℓ) (pkStar : Fin ℓ × Bool → Y) (σ : Fin ℓ → X)
    (ω : Fin N × (Fin N → Fin ℓ × Bool → X) × R) : (Fin ℓ → Bool) × (Fin ℓ → X) :=
  let o := (runStateful (redSigner f H h pkStar ω.1 ω.2.1 fun _ => σ) 0
    (F.forge (rootOf H h (simKeys f pkStar ω.1 ω.2.1)) ω.2.2)).1
  (o.1, o.2.sig)

/-- The **reduction**: a Lamport one-time forger with coins `(j, skO, r)` (guessed index, the
other Lamport secret keys, the Merkle forger's coins) that plants the challenge key at leaf `j`. -/
def reduction (N : ℕ) (F : Forger X Y A R ℓ) :
    Lamport.Forger X Y (Fin N × (Fin N → Fin ℓ × Bool → X) × R) ℓ where
  choose := redChoose f H h F
  forge := redForge f H h F

/-- With the challenge key `Lamport.publicKey f skStar` planted at `j`, the reduction's keys are
those of `Function.update skO j skStar`. -/
theorem simKeys_eq (skStar : Fin ℓ × Bool → X) (j : Fin N) (skO : Fin N → Fin ℓ × Bool → X) :
    simKeys f (Lamport.publicKey f skStar) j skO =
      lamportKeys f (Function.update skO j skStar) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [simKeys, lamportKeys]
  · simp [simKeys, lamportKeys, hij]

/-- The reduction's signing oracle agrees with the honest signer for the keys
`Function.update skO j skStar` at every index other than `j`, and at `j` on every message that
`σj` signs correctly. -/
theorem redSigner_eq (skStar : Fin ℓ × Bool → X) (j : Fin N) (skO : Fin N → Fin ℓ × Bool → X)
    (σj : (Fin ℓ → Bool) → Fin ℓ → X) (i : ℕ) (m : Fin ℓ → Bool)
    (him : i ≠ j.val ∨ σj m = Lamport.sign skStar m) :
    redSigner f H h (Lamport.publicKey f skStar) j skO σj i m =
      sign f H h (Function.update skO j skStar) i m := by
  unfold redSigner sign
  rw [simKeys_eq]
  unfold signerOf
  by_cases hi : i < N
  · simp only [hi, ↓reduceDIte, Option.some.injEq, Signature.mk.injEq, true_and, and_true]
    by_cases hij : (⟨i, hi⟩ : Fin N) = j
    · subst hij
      simp only [↓reduceIte, Function.update_self]
      rcases him with h' | h'
      · exact absurd rfl h'
      · exact h'
    · simp [hij]
  · simp [hi]

/-- The core of the reduction: if the Merkle forger wins with keys
`Function.update skO j skStar` and coins `r`, using the honest Lamport key at index `j`, then the
reduction with coins `(j, skO, r)` forges a Lamport signature under `skStar`. -/
theorem reduction_wins [DecidableEq Y] [DecidableEq A] [NeZero ℓ] (F : Forger X Y A R ℓ) (j : Fin N)
    (skO : Fin N → Fin ℓ × Bool → X) (skStar : Fin ℓ × Bool → X) (r : R)
    (hw : win f H h F (Function.update skO j skStar) r = true)
    (hk : keyMatches f (Function.update skO j skStar)
      (run f H h F (Function.update skO j skStar) r).1.2 = true)
    (hj : (run f H h F (Function.update skO j skStar) r).1.2.index = j.val) :
    (reduction f H h N F).Wins f skStar (j, skO, r) := by
  set sk := Function.update skO j skStar with hsk
  set c := F.forge (publicKey f H h sk) r with hc
  have hroot : rootOf H h (simKeys f (Lamport.publicKey f skStar) j skO) = publicKey f H h sk := by
    rw [simKeys_eq]; rfl
  -- the forger's output in the honest game
  have hrun : run f H h F sk r = runStateful (sign f H h sk) 0 c := rfl
  simp only [win, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
  obtain ⟨hv, hfresh⟩ := hw
  obtain ⟨hL, hi, -⟩ := verify_sound f H h sk hv
  have hpk : (run f H h F sk r).1.2.pk = Lamport.publicKey f (sk ⟨_, hi⟩) := by
    simpa [keyMatches, hi] using hk
  -- the Lamport key of the forgery is `pkStar`
  have hpkStar : (run f H h F sk r).1.2.pk = Lamport.publicKey f skStar := by
    rw [hpk]
    congr 1
    have : (⟨(run f H h F sk r).1.2.index, hi⟩ : Fin N) = j := Fin.ext hj
    rw [this, hsk, Function.update_self]
  -- signers that agree with the honest one away from `j`
  have hagree : ∀ σj : (Fin ℓ → Bool) → Fin ℓ → X, ∀ i m, i ≠ j.val →
      redSigner f H h (Lamport.publicKey f skStar) j skO σj i m = sign f H h sk i m :=
    fun σj i m hij => redSigner_eq f H h skStar j skO σj i m (Or.inl hij)
  set sJ := redSigner f H h (Lamport.publicKey f skStar) j skO (Lamport.sign (skO j)) with hsJ
  have hq : queryAt sJ 0 c j.val = queryAt (sign f H h sk) 0 c j.val :=
    queryAt_congr (fun i hi m => hagree _ i m (Nat.ne_of_lt hi)) 0 c (Nat.zero_le _)
  have hchoose : (reduction f H h N F).choose (Lamport.publicKey f skStar) (j, skO, r) =
      match queryAt (sign f H h sk) 0 c j.val with
      | some m => m
      | none => fun t => !((runStateful sJ 0 c).1.1 t) := by
    simp only [reduction, redChoose, hroot]
    rw [← hc, ← hsJ, hq]
  rcases hqR : queryAt (sign f H h sk) 0 c j.val with _ | mj
  · -- the forger asks fewer than `j + 1` queries
    have hJ : runStateful sJ 0 c = runStateful (sign f H h sk) 0 c :=
      runStateful_congr (fun i m hij => hagree _ i m hij) 0 c (by rw [hq, hqR]; simp)
    have hB : ∀ σ, runStateful (redSigner f H h (Lamport.publicKey f skStar) j skO fun _ => σ) 0 c =
        runStateful (sign f H h sk) 0 c := fun σ =>
      runStateful_congr (fun i m hij => hagree _ i m hij) 0 c (by
        rw [queryAt_congr (s' := sign f H h sk) (fun i hi m => hagree _ i m (Nat.ne_of_lt hi)) 0 c
          (Nat.zero_le _), hqR]
        simp)
    unfold Lamport.Forger.Wins
    rw [hchoose, hqR]
    simp only [reduction, redForge, hroot, ← hc, hB, hJ]
    refine ⟨fun heq => ?_, ?_⟩
    · have h0 := congrFun heq ⟨0, Nat.pos_of_ne_zero (NeZero.ne ℓ)⟩
      beta_reduce at h0
      revert h0
      generalize (runStateful (sign f H h sk) 0 c).1.1 ⟨0, Nat.pos_of_ne_zero (NeZero.ne ℓ)⟩ = b
      cases b <;> simp
    · rw [← hpkStar]
      exact hL
  · -- the forger's `j`-th query is `mj`, answered by the Lamport signing oracle
    have hB : runStateful (redSigner f H h (Lamport.publicKey f skStar) j skO
        fun _ => Lamport.sign skStar mj) 0 c = runStateful (sign f H h sk) 0 c := by
      symm
      refine runStateful_congr (fun i m hij => (hagree _ i m hij).symm) 0 c ?_
      intro m hm
      rw [hqR, Option.some.injEq] at hm
      subst hm
      exact (redSigner_eq f H h skStar j skO _ j.val mj (Or.inr rfl)).symm
    have hmem := mem_of_queryAt (sign f H h sk) 0 c hqR
    unfold Lamport.Forger.Wins
    rw [hchoose, hqR]
    simp only [reduction, redForge, hroot, ← hc, hB]
    refine ⟨fun heq => hfresh (heq ▸ hmem), ?_⟩
    rw [← hpkStar]
    exact hL

end Reduction

/-! ### Forgery bound up to the key-mismatch event -/

section ForgeryBound

variable {R : Type*} [Fintype X] [Nonempty X] [Fintype R] [Nonempty R]

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- The success probability of a deterministic test on a uniform sample, as a sum of
indicators. -/
private theorem winProb_map_uniform_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → Bool) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype Ω).map g) =
      (∑ ω, if g ω = true then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  rw [winProb_map_uniform, card_filter, Nat.cast_sum]
  congr 1
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- Re-randomizing one key of a family: `∑ x, ∑ sk, G (update sk j x) = |K| · ∑ sk, G sk`. -/
private theorem sum_sum_update {K : Type*} [Fintype K] {N : ℕ} (j : Fin N)
    (G : (Fin N → K) → ℝ) :
    ∑ x : K, ∑ sk : Fin N → K, G (Function.update sk j x) = Fintype.card K * ∑ sk, G sk := by
  have hR : (Fintype.card K : ℝ) * ∑ sk, G sk = ∑ q : (Fin N → K) × K, G q.1 := by
    rw [Fintype.sum_prod_type, mul_sum]
    simp [sum_const, Finset.card_univ]
  let e : K × (Fin N → K) ≃ (Fin N → K) × K :=
    { toFun := fun p => (Function.update p.2 j p.1, p.2 j)
      invFun := fun q => (q.1 j, Function.update q.1 j q.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  rw [hR, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ fun p => rfl

variable [DecidableEq Y] [DecidableEq A]

omit [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- The guessed index is right for exactly one `j` when the forgery uses an honest key. -/
private theorem sum_indicator_index {N : ℕ} (F : Forger X Y A R ℓ)
    (sk : Fin N → Fin ℓ × Bool → X) (r : R) :
    ∑ j : Fin N, (if (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true ∧
        (run f H h F sk r).1.2.index = j.val then (1 : ℝ) else 0) =
      if (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true then 1 else 0 := by
  by_cases hg : (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true
  · have hi : (run f H h F sk r).1.2.index < N := by
      have hg' := hg
      simp only [Bool.and_eq_true] at hg'
      have hk := hg'.2
      by_contra hn
      simp [keyMatches, hn] at hk
    simp only [hg, true_and, ↓reduceIte]
    rw [Finset.sum_eq_single ⟨_, hi⟩]
    · simp
    · intro b _ hb
      refine ite_eq_right_of_eq_false _ _ (eq_false fun he => hb (Fin.ext he.symm))
    · intro hn
      exact absurd (mem_univ _) hn
  · simp [hg]

/-- **Forgery bound up to the key-mismatch event** (an intermediate bad-event bound, not EUF
security): for `ℓ ≥ 1` and `N ≥ 1`, the forgery probability against the `N`-key stateful signer is
at most `N` times the success probability of the Lamport one-time forger `reduction N F`, plus the
probability of the key-mismatch event `keyMismatchGame`, in which the forger's signature carries a
Lamport key other than the honest one at its index. That term is the forger's own bad-event
probability, not a collision finder's advantage: each run in it exhibits a collision of `h` or `H`
(`collision_of_keyMismatchGame`), but no collision finder is constructed, and for compressing
hashes collisions exist, so this theorem alone does not give EUF security under collision
resistance. The factor `N` is the guess of the forgery's index (Katz and Lindell, Section 12.6,
for one-time signatures and hash trees). -/
theorem winProb_forgeGame_le [NeZero ℓ] (N : ℕ) [NeZero N] (F : Forger X Y A R ℓ) :
    winProb (forgeGame f H h N F) ≤
      N * winProb (Lamport.forgeGame f (reduction f H h N F)) +
        winProb (keyMismatchGame f H h N F) := by
  classical
  have hlg : winProb (Lamport.forgeGame f (reduction f H h N F)) =
      (∑ ω : (Fin ℓ × Bool → X) × Fin N × (Fin N → Fin ℓ × Bool → X) × R,
        if decide ((reduction f H h N F).Wins f ω.1 ω.2) = true then (1 : ℝ) else 0) /
        Fintype.card ((Fin ℓ × Bool → X) × Fin N × (Fin N → Fin ℓ × Bool → X) × R) :=
    winProb_map_uniform_sum _
  rw [forgeGame, keyMismatchGame_eq, winProb_map_uniform_sum, winProb_map_uniform_sum, hlg]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  -- the reduction wins whenever the forger wins at the guessed index with the honest key
  have step1 : ∀ (x : Fin ℓ × Bool → X) (j : Fin N) (skO : Fin N → Fin ℓ × Bool → X) (r : R),
      (if (win f H h F (Function.update skO j x) r &&
          keyMatches f (Function.update skO j x)
            (run f H h F (Function.update skO j x) r).1.2) = true ∧
          (run f H h F (Function.update skO j x) r).1.2.index = j.val then (1 : ℝ) else 0) ≤
        if decide ((reduction f H h N F).Wins f x (j, skO, r)) = true then 1 else 0 := by
    intro x j skO r
    by_cases hc : (win f H h F (Function.update skO j x) r &&
        keyMatches f (Function.update skO j x)
          (run f H h F (Function.update skO j x) r).1.2) = true ∧
        (run f H h F (Function.update skO j x) r).1.2.index = j.val
    · obtain ⟨hg, hj⟩ := hc
      have hg' := hg
      simp only [Bool.and_eq_true] at hg'
      obtain ⟨hw, hk⟩ := hg'
      have hW := reduction_wins f H h F j skO x r hw hk hj
      simp [hg, hj, hW]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      split_ifs <;> norm_num
  have hkey : (Fintype.card (Fin ℓ × Bool → X) : ℝ) *
      (∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
        if (win f H h F ω.1 ω.2 && keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
          (1 : ℝ) else 0) ≤
      ∑ ω : (Fin ℓ × Bool → X) × Fin N × (Fin N → Fin ℓ × Bool → X) × R,
        if decide ((reduction f H h N F).Wins f ω.1 ω.2) = true then (1 : ℝ) else 0 := by
    calc (Fintype.card (Fin ℓ × Bool → X) : ℝ) *
          (∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
            if (win f H h F ω.1 ω.2 && keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
              (1 : ℝ) else 0)
        = Fintype.card (Fin ℓ × Bool → X) *
            ∑ sk : Fin N → Fin ℓ × Bool → X, ∑ r : R, ∑ j : Fin N,
              (if (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true ∧
                (run f H h F sk r).1.2.index = j.val then (1 : ℝ) else 0) := by
          rw [Fintype.sum_prod_type]
          simp only [sum_indicator_index]
      _ = ∑ j : Fin N, Fintype.card (Fin ℓ × Bool → X) *
            ∑ sk : Fin N → Fin ℓ × Bool → X, ∑ r : R,
              (if (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true ∧
                (run f H h F sk r).1.2.index = j.val then (1 : ℝ) else 0) := by
          rw [← mul_sum]
          congr 1
          symm
          rw [sum_comm]
          exact sum_congr rfl fun sk _ => sum_comm
      _ = ∑ j : Fin N, ∑ x : Fin ℓ × Bool → X, ∑ skO : Fin N → Fin ℓ × Bool → X, ∑ r : R,
              (if (win f H h F (Function.update skO j x) r &&
                keyMatches f (Function.update skO j x)
                  (run f H h F (Function.update skO j x) r).1.2) = true ∧
                (run f H h F (Function.update skO j x) r).1.2.index = j.val then
                  (1 : ℝ) else 0) :=
          sum_congr rfl fun j _ => (sum_sum_update j (fun sk => ∑ r : R,
            (if (win f H h F sk r && keyMatches f sk (run f H h F sk r).1.2) = true ∧
              (run f H h F sk r).1.2.index = j.val then (1 : ℝ) else 0))).symm
      _ = ∑ x : Fin ℓ × Bool → X, ∑ j : Fin N, ∑ skO : Fin N → Fin ℓ × Bool → X, ∑ r : R,
              (if (win f H h F (Function.update skO j x) r &&
                keyMatches f (Function.update skO j x)
                  (run f H h F (Function.update skO j x) r).1.2) = true ∧
                (run f H h F (Function.update skO j x) r).1.2.index = j.val then
                  (1 : ℝ) else 0) := sum_comm
      _ ≤ ∑ x : Fin ℓ × Bool → X, ∑ j : Fin N, ∑ skO : Fin N → Fin ℓ × Bool → X, ∑ r : R,
              if decide ((reduction f H h N F).Wins f x (j, skO, r)) = true then (1 : ℝ)
                else 0 :=
          sum_le_sum fun x _ => sum_le_sum fun j _ => sum_le_sum fun skO _ =>
            sum_le_sum fun r _ => step1 x j skO r
      _ = _ := by simp only [Fintype.sum_prod_type]
  -- split the winning runs by whether the forgery uses the honest key
  have hsplit : (∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
      if win f H h F ω.1 ω.2 = true then (1 : ℝ) else 0) ≤
      (∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
        if (win f H h F ω.1 ω.2 && keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
          (1 : ℝ) else 0) +
      ∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
        if (win f H h F ω.1 ω.2 && !keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
          (1 : ℝ) else 0 := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun ω _ => ?_
    cases win f H h F ω.1 ω.2 <;> cases keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2 <;> norm_num
  have hK : (0 : ℝ) < Fintype.card (Fin ℓ × Bool → X) := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < Fintype.card (Fin N → Fin ℓ × Bool → X) := by
    exact_mod_cast Fintype.card_pos
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  set SW := ∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
    if win f H h F ω.1 ω.2 = true then (1 : ℝ) else 0
  set SG := ∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
    if (win f H h F ω.1 ω.2 && keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
      (1 : ℝ) else 0
  set SC := ∑ ω : (Fin N → Fin ℓ × Bool → X) × R,
    if (win f H h F ω.1 ω.2 && !keyMatches f ω.1 (run f H h F ω.1 ω.2).1.2) = true then
      (1 : ℝ) else 0
  set SB := ∑ ω : (Fin ℓ × Bool → X) × Fin N × (Fin N → Fin ℓ × Bool → X) × R,
    if decide ((reduction f H h N F).Wins f ω.1 ω.2) = true then (1 : ℝ) else 0
  set cK := (Fintype.card (Fin ℓ × Bool → X) : ℝ)
  set cS := (Fintype.card (Fin N → Fin ℓ × Bool → X) : ℝ)
  set cR := (Fintype.card R : ℝ)
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNB : (N : ℝ) * (SB / (cK * (N * (cS * cR)))) = SB / (cK * (cS * cR)) := by
    field_simp
  rw [hNB]
  calc SW / (cS * cR) ≤ (SG + SC) / (cS * cR) :=
        div_le_div_of_nonneg_right hsplit (by positivity)
    _ = SG / (cS * cR) + SC / (cS * cR) := add_div _ _ _
    _ ≤ SB / (cK * (cS * cR)) + SC / (cS * cR) := by
        refine add_le_add_left ?_ _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt (mul_pos hS hR))]

/-- **Reduction to Lamport for injective hashes**: the key-mismatch event is empty, so the forgery
probability is at most `N` times the success probability of the Lamport forger. This is a complete
reduction to Lamport one-time security, but only for injective hashes, which cannot compress (an
injective `h : A → A → A` needs an infinite or trivial `A`); it says nothing about compressing hash
functions. -/
theorem winProb_forgeGame_le_of_injective [NeZero ℓ] (N : ℕ) [NeZero N]
    (F : Forger X Y A R ℓ) (hh : Function.Injective (Function.uncurry h))
    (hH : Function.Injective H) :
    winProb (forgeGame f H h N F) ≤ N * winProb (Lamport.forgeGame f (reduction f H h N F)) := by
  have := winProb_forgeGame_le f H h N F
  rwa [winProb_keyMismatchGame_eq_zero f H h N F hh hH, add_zero] at this

/-- **Bad-event bound from one-wayness**: composing `winProb_forgeGame_le` with Lamport's
reduction (`Lamport.forgeGame_le`, Katz and Lindell, Theorem 12.16), the forgery probability is at
most `N · 2 ℓ` times the success probability of an inverter for `f`, plus the key-mismatch event.
As for `winProb_forgeGame_le`, that term is not bounded by a collision-finding advantage, so this is
not EUF security from one-wayness and collision resistance. -/
theorem winProb_forgeGame_le_invert [NeZero ℓ] (N : ℕ) [NeZero N] (F : Forger X Y A R ℓ) :
    winProb (forgeGame f H h N F) ≤
      N * (2 * ℓ * (Lamport.invertGame f (Lamport.invert f (reduction f H h N F)) true).toReal) +
        winProb (keyMismatchGame f H h N F) := by
  have h2 := Lamport.forgeGame_le f (reduction f H h N F)
  calc _ ≤ _ := winProb_forgeGame_le f H h N F
    _ ≤ _ := by
      gcongr
      exact h2

end ForgeryBound

end Cslib.Crypto.Signatures.MerkleSig
