/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleDamgardFull
public import CSLibExt.Crypto.Framework.Migration
public import Mathlib.Data.Fintype.Vector

/-!
# HMAC

HMAC (Katz and Lindell, Section 5.3.2, Construction 5.7) over the double-length-encoded
Merkle–Damgård hash `H = MerkleDamgardFull.fullHash h iv lenBlock L` (a strengthened variant of
Construction 5.3, see `MerkleDamgardFull`) of a compression function
`h : S × {0,1}^n → S`, with an `n`-bit key `k` and two fixed `n`-bit constants `ipad`, `opad`:

  `HMAC_k(m) = H((k ⊕ opad) ‖ H((k ⊕ ipad) ‖ m))`,

where the inner digest is turned into bits by `toBits : S → List Bool`.

* `hmac` is the construction and `hmac_eq_nestedContHash` its **nested form**: because
  `k ⊕ ipad` and `k ⊕ opad` each fill exactly the first block, `HMAC_k(m)` is
  `nestedContHash k_in k_out m = H'_{k_out}(H'_{k_in}(m))` for the derived chaining values
  `k_in = h(iv, k ⊕ ipad)` and `k_out = h(iv, k ⊕ opad)`, where the **continuation hash**
  `H'_z(m) = contHash z m` runs the chain from `z` over `m` padded as the continuation of one
  `n`-bit block (its length field encodes `n + |m|`, and the block count includes that block).
  `hmac_eq_of_innerKey_eq` records that the tag depends on `k` only through `(k_in, k_out)`.
  The ingredients are `pad_append` (padding `u ‖ m` keeps `u` as a prefix), `blocks_append`
  (a leading full block is cut off as the first block) and `hash_cons` (the first block moves
  into the initial chaining value). `nestedContHash` has the shape of NMAC (Bellare, Canetti and
  Krawczyk) but is **not** NMAC over `fullHash`: NMAC's keyed hash would be `fullHash` started at
  `z`, which pads `m` alone, and the two differ in general.
* `hmacSchemeOn enc` is HMAC as a MAC on messages of a type `X` encoded into bit strings by `enc`:
  the Framework PRF-MAC `Framework.Migration.prfMac` (Katz and Lindell, Construction 4.5) of the
  keyed function `k, x ↦ HMAC_k(enc x)`, i.e. a uniform key, deterministic tags and verification
  by recomputation (an `EncryptThenMac.detMac`). `hmacScheme` is `hmacSchemeOn id`.
  `hmacScheme_correct` and `hmacSchemeOn_correct` are correctness (Katz and Lindell,
  Definition 4.1), from `Framework.Migration.prfMac_correct`.
* **HMAC is a secure MAC if it is a PRF**, in the Framework experiment `Framework.macAdvantage`
  for Framework forgers `Framework.MACForger` with **arbitrary** coins `coins : PMF R`
  (Katz and Lindell, Theorem 4.6 applied to HMAC as a keyed function):
  - `hmacSchemeOn_macAdvantage_le`: for a finite message type `X`, there are coins `r` in the
    support of the forger's coins such that its forgery probability against `hmacSchemeOn enc` is
    at most the PRF advantage of the deterministic distinguisher `PRF.macReduction [] (A.forge r)`
    against `k, x ↦ HMAC_k(enc x)`, plus `1 / |S|`. It and `macGame_hmacSchemeOn`, which writes
    the experiment as an average over the coins of the PRF file's `PRF.macGame`, are the generic
    PRF-MAC results `Framework.Migration.exists_macAdvantage_prfMac_le` (coin fixing) and
    `Framework.Migration.macGame_prfMac_eq_bind` for this keyed function.
  - `hmacScheme_macAdvantage_le`: the same bound for `hmacScheme` itself (all bit strings), for
    forgers whose queries and forgery are bit strings shorter than `maxLen`, i.e. forgers against
    `Msg maxLen` relabeled into `List Bool` (`Framework.MACForger.relabel`,
    `macGame_hmacScheme_relabel`, an instance of `Framework.Migration.macGame_prfMac_relabel`). The
    length bound is needed because the random-function experiment of `PRF.prfAdvantage` is over
    a finite message space.
  - For uniform coins, `macGame_hmacSchemeOn_of_uniform` (the Framework experiment equals
    `PRF.macGame`) and `hmacSchemeOn_macAdvantage_le_of_uniform` (the bound with the distinguisher
    over the same coins) are `Framework.Migration.prf_macGame_eq` and
    `Framework.Migration.prf_macAdvantage_le` for the keyed function `k, x ↦ HMAC_k(enc x)`,
    stated for a Framework forger whose coins are uniform.

**Deferred.** The theorem that HMAC is a PRF when the compression function is a PRF (on both the
chaining-value key and the derived keys) and weakly collision resistant (Bellare, Canetti and
Krawczyk; Katz and Lindell, Theorem 5.8) is not proved here: its hybrid over the nested
construction needs the derived keys `h(iv, k ⊕ ipad)` and `h(iv, k ⊕ opad)` to be jointly
pseudorandom, which is an additional assumption of Katz and Lindell's statement. Relating
`nestedContHash` to the keyed-hash NMAC of that analysis, whose padding differs, is part of what is
deferred. No unproved statement is made.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.3.2 (Construction 5.7, Theorem 5.8) and Section 4.3 (Theorem 4.6).
* M. Bellare, R. Canetti and H. Krawczyk, *Keying hash functions for message authentication*,
  CRYPTO 1996.
-/

@[expose] public section

namespace Cslib.Crypto.HMAC

open Cslib.Crypto.MerkleDamgard Cslib.Crypto.MerkleDamgardPadding Cslib.Crypto.MerkleDamgardFull

/-! ### Structural lemmas: a leading full block -/

section Structure

variable (n L : ℕ)

/-- The padding of `m` behind an `off`-bit prefix: `m`, the `1` bit, the zeros, and the
`L`-bit length field of the whole string, whose length is `off + |m|`. -/
def padTail (off : ℕ) (m : List Bool) : List Bool :=
  m ++ (true :: List.replicate (numZeros n L (off + m.length)) false) ++
    encodeLength L (off + m.length)

/-- Padding `u ‖ m` keeps `u` as a prefix; the rest depends on `u` only through its length. -/
theorem pad_append (u m : List Bool) : pad n L (u ++ m) = u ++ padTail n L u.length m := by
  simp [pad, padTail, List.append_assoc]

/-- A leading `n`-bit block of a bit string is its first block. -/
theorem blocks_append (hn : 0 < n) (v : List.Vector Bool n) (T : List Bool) :
    blocks n (v.toList ++ T) = v :: blocks n T := by
  have hv : v.toList.length = n := v.toList_length
  have hfuel : (v.toList ++ T).length / n = T.length / n + 1 := by
    rw [List.length_append, hv, Nat.add_comm, Nat.add_div_right _ hn]
  rw [blocks, hfuel, blocksFuel,
    dite_eq_left (by rw [List.length_take, List.length_append, hv]; omega), blocks]
  congr 1
  · exact List.Vector.toList_injective (List.take_left' hv)
  · rw [List.drop_left' hv]

variable {S : Type*} {n} (h : S × List.Vector Bool n → S) (lenBlock : ℕ → List.Vector Bool n)

/-- The first block moves into the initial chaining value. -/
theorem hash_cons (iv : S) (x : List.Vector Bool n) (xs : List (List.Vector Bool n)) :
    MerkleDamgard.hash h iv lenBlock (x :: xs) =
      h (chain h (h (iv, x)) xs, lenBlock (xs.length + 1)) := by
  simp [MerkleDamgard.hash, chain_eq_foldl]

/-- The **continuation hash** `H'_z(m)`: the Merkle–Damgård chain started at the chaining value
`z` over the blocks of `m` padded as the continuation of one `n`-bit block (the length field
encodes `n + |m|`), finished with the block count of the whole message, one more than the blocks
of `m`. It is how `fullHash` finishes a message after its first block (`fullHash_vector_append`);
it is not `fullHash` started at `z`, which pads `m` alone. -/
def contHash (z : S) (m : List Bool) : S :=
  h (chain h z (blocks n (padTail n L n m)), lenBlock ((blocks n (padTail n L n m)).length + 1))

/-- Hashing a one-block prefix `v` followed by `m` is hashing `m` from the chaining value
`h(iv, v)`. -/
theorem fullHash_vector_append (hn : 0 < n) (iv : S) (v : List.Vector Bool n) (m : List Bool) :
    fullHash h iv lenBlock L (v.toList ++ m) = contHash L h lenBlock (h (iv, v)) m := by
  rw [fullHash, padBlocks, pad_append, v.toList_length, blocks_append n hn, hash_cons, contHash]

end Structure

/-! ### The construction -/

section HMAC

variable {S : Type*} {n : ℕ} (h : S × List.Vector Bool n → S) (iv : S)
  (lenBlock : ℕ → List.Vector Bool n) (L : ℕ) (toBits : S → List Bool)
  (ipad opad : List.Vector Bool n)

/-- Bitwise exclusive or of two blocks. -/
def xorBlock (a b : List.Vector Bool n) : List.Vector Bool n := List.Vector.map₂ xor a b

/-- **HMAC** (Katz and Lindell, Construction 5.7):
`HMAC_k(m) = H((k ⊕ opad) ‖ H((k ⊕ ipad) ‖ m))` for the double-length-encoded Merkle–Damgård
hash `H = fullHash`. -/
def hmac (k : List.Vector Bool n) (m : List Bool) : S :=
  fullHash h iv lenBlock L ((xorBlock k opad).toList ++
    toBits (fullHash h iv lenBlock L ((xorBlock k ipad).toList ++ m)))

/-- The derived inner key `k_in = h(iv, k ⊕ ipad)`. -/
def innerKey (k : List.Vector Bool n) : S := h (iv, xorBlock k ipad)

/-- The derived outer key `k_out = h(iv, k ⊕ opad)`. -/
def outerKey (k : List.Vector Bool n) : S := h (iv, xorBlock k opad)

/-- The nested construction over the continuation hash with chaining-value keys `k_in` and
`k_out`: `H'_{k_out}(H'_{k_in}(m))`. It has the shape of NMAC (Bellare, Canetti and Krawczyk) but
is not NMAC over `fullHash`, whose keyed hash pads the message alone (see `contHash`). -/
def nestedContHash (kin kout : S) (m : List Bool) : S :=
  contHash L h lenBlock kout (toBits (contHash L h lenBlock kin m))

/-- **HMAC in nested form** (Katz and Lindell, Section 5.3.2): with the derived chaining values,
`HMAC_k(m) = H'_{h(iv, k ⊕ opad)}(H'_{h(iv, k ⊕ ipad)}(m))` for the continuation hash `H'`. -/
theorem hmac_eq_nestedContHash (hn : 0 < n) (k : List.Vector Bool n) (m : List Bool) :
    hmac h iv lenBlock L toBits ipad opad k m =
      nestedContHash h lenBlock L toBits (innerKey h iv ipad k) (outerKey h iv opad k) m := by
  rw [hmac, fullHash_vector_append L h lenBlock hn, fullHash_vector_append L h lenBlock hn,
    nestedContHash, innerKey, outerKey]

/-- HMAC depends on its key only through the two derived keys. -/
theorem hmac_eq_of_innerKey_eq (hn : 0 < n) {k k' : List.Vector Bool n}
    (hin : innerKey h iv ipad k = innerKey h iv ipad k')
    (hout : outerKey h iv opad k = outerKey h iv opad k') (m : List Bool) :
    hmac h iv lenBlock L toBits ipad opad k m = hmac h iv lenBlock L toBits ipad opad k' m := by
  rw [hmac_eq_nestedContHash h iv lenBlock L toBits ipad opad hn,
    hmac_eq_nestedContHash h iv lenBlock L toBits ipad opad hn, hin, hout]

/-! ### HMAC as a MAC -/

variable [DecidableEq S]

/-- HMAC as a MAC (Katz and Lindell, Definition 4.1) on messages of a type `X`, encoded into bit
strings by `enc`: the PRF-MAC `Framework.Migration.prfMac` (Construction 4.5) of the keyed function
`k, x ↦ HMAC_k(enc x)`, with a uniform `n`-bit key, the tag `HMAC_k(enc x)`, and verification by
recomputing the tag. `hmacScheme` is the case `enc = id`. -/
noncomputable def hmacSchemeOn {X : Type*} (enc : X → List Bool) :
    Cslib.Crypto.Framework.MACScheme X (List.Vector Bool n) S :=
  Cslib.Crypto.Framework.Migration.prfMac fun k x =>
    hmac h iv lenBlock L toBits ipad opad k (enc x)

/-- HMAC as a deterministic MAC on all bit strings (Katz and Lindell, Definition 4.1): a uniform
`n`-bit key, the tag `HMAC_k(m)`, and verification by recomputing the tag. -/
noncomputable abbrev hmacScheme :
    Cslib.Crypto.Framework.MACScheme (List Bool) (List.Vector Bool n) S :=
  hmacSchemeOn h iv lenBlock L toBits ipad opad id

/-- **Correctness** of HMAC on encoded messages (Katz and Lindell, Definition 4.1): honest tags
verify, by `Framework.Migration.prfMac_correct`. -/
theorem hmacSchemeOn_correct {X : Type*} (enc : X → List Bool) :
    (hmacSchemeOn h iv lenBlock L toBits ipad opad enc).Correct :=
  Cslib.Crypto.Framework.Migration.prfMac_correct _

/-- **Correctness** of HMAC (Katz and Lindell, Definition 4.1): honest tags verify. -/
theorem hmacScheme_correct : (hmacScheme h iv lenBlock L toBits ipad opad).Correct :=
  hmacSchemeOn_correct h iv lenBlock L toBits ipad opad id

/-! ### The Framework forgery experiment of HMAC -/

variable {X R : Type*} [DecidableEq X]

/-- The Framework `Mac-forge` experiment of HMAC (Katz and Lindell, Definition 4.2) for a forger
`A` with **arbitrary** coins: draw `r ← A.coins`, then run the PRF file's forgery experiment
`PRF.macGame` of HMAC (uniform key) for the forger fixed at the coins `r`. This is
`Framework.Migration.macGame_prfMac_eq_bind` for the keyed function `k, x ↦ HMAC_k(enc x)`. -/
theorem macGame_hmacSchemeOn (enc : X → List Bool) (A : Cslib.Crypto.Framework.MACForger X S R) :
    Cslib.Crypto.Framework.macGame (hmacSchemeOn h iv lenBlock L toBits ipad opad enc) A =
      A.coins.bind fun r => PRF.macGame (fun k x => hmac h iv lenBlock L toBits ipad opad k (enc x))
        (fun _ : Unit => A.forge r) :=
  Cslib.Crypto.Framework.Migration.macGame_prfMac_eq_bind _ A

variable [Fintype S] [Nonempty S]

/-- **HMAC is a secure MAC if it is a PRF**, for the Framework experiment `macAdvantage` of
`hmacSchemeOn enc` (Katz and Lindell, Theorem 4.6 applied to HMAC as a keyed function): for
messages in a finite type `X` encoded by `enc` and every Framework forger `A`, with arbitrary
coins `A.coins : PMF R`, there are coins `r` in the support of `A.coins` such that the forgery
probability is at most the PRF advantage of the deterministic distinguisher
`PRF.macReduction [] (A.forge r)` against `k, x ↦ HMAC_k(enc x)`, plus `1 / |S|`. This is
`Framework.Migration.exists_macAdvantage_prfMac_le` for `k, x ↦ HMAC_k(enc x)`. -/
theorem hmacSchemeOn_macAdvantage_le [Fintype X] (enc : X → List Bool)
    (A : Cslib.Crypto.Framework.MACForger X S R) :
    ∃ r ∈ A.coins.support,
      Cslib.Crypto.Framework.macAdvantage (hmacSchemeOn h iv lenBlock L toBits ipad opad enc) A ≤
        PRF.prfAdvantage (fun k x => hmac h iv lenBlock L toBits ipad opad k (enc x))
          (fun _ : Unit => PRF.macReduction [] (A.forge r)) + 1 / Fintype.card S :=
  Cslib.Crypto.Framework.Migration.exists_macAdvantage_prfMac_le _ A

omit [Fintype S] [Nonempty S] in
/-- **Exact bridge for uniform coins**: for a Framework forger whose coins are uniform on a finite
type, the Framework experiment of `hmacSchemeOn enc` is the PRF file's `PRF.macGame` of HMAC. This
is `Framework.Migration.prf_macGame_eq` for the keyed function `k, x ↦ HMAC_k(enc x)`. -/
theorem macGame_hmacSchemeOn_of_uniform [Fintype R] [Nonempty R] (enc : X → List Bool)
    (A : Cslib.Crypto.Framework.MACForger X S R)
    (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype R) :
    Cslib.Crypto.Framework.macGame (hmacSchemeOn h iv lenBlock L toBits ipad opad enc) A =
      PRF.macGame (fun k x => hmac h iv lenBlock L toBits ipad opad k (enc x)) A.forge := by
  obtain ⟨coins, forge⟩ := A
  subst hA
  exact (Cslib.Crypto.Framework.Migration.prf_macGame_eq _ forge).symm

/-- `hmacSchemeOn_macAdvantage_le` for a forger with uniform coins, with the distinguisher
`r ↦ PRF.macReduction [] (A.forge r)` over the same coins (Katz and Lindell, Theorem 4.6): this is
`Framework.Migration.prf_macAdvantage_le` for the keyed function `k, x ↦ HMAC_k(enc x)`. -/
theorem hmacSchemeOn_macAdvantage_le_of_uniform [Fintype X] [Fintype R] [Nonempty R]
    (enc : X → List Bool) (A : Cslib.Crypto.Framework.MACForger X S R)
    (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype R) :
    Cslib.Crypto.Framework.macAdvantage (hmacSchemeOn h iv lenBlock L toBits ipad opad enc) A ≤
      PRF.prfAdvantage (fun k x => hmac h iv lenBlock L toBits ipad opad k (enc x))
        (fun r => PRF.macReduction [] (A.forge r)) + 1 / Fintype.card S := by
  obtain ⟨coins, forge⟩ := A
  subst hA
  exact Cslib.Crypto.Framework.Migration.prf_macAdvantage_le _ forge

/-! ### Forgers against `hmacScheme` with length-bounded messages -/

omit [Fintype S] [Nonempty S] in
/-- For an injective encoding `enc`, a forger `A` against `hmacSchemeOn enc`, relabeled along `enc`
into a forger against `hmacScheme` (all bit strings), has the same forgery experiment: freshness
of the forged message is preserved because `enc` is injective. This is
`Framework.Migration.macGame_prfMac_relabel` for HMAC. -/
theorem macGame_hmacScheme_relabel {enc : X → List Bool} (henc : Function.Injective enc)
    (A : Cslib.Crypto.Framework.MACForger X S R) :
    Cslib.Crypto.Framework.macGame (hmacScheme h iv lenBlock L toBits ipad opad)
        (A.relabel enc) =
      Cslib.Crypto.Framework.macGame (hmacSchemeOn h iv lenBlock L toBits ipad opad enc) A :=
  Cslib.Crypto.Framework.Migration.macGame_prfMac_relabel _ henc A

/-- **HMAC is a secure MAC if it is a PRF**, for `hmacScheme` itself (all bit strings) in the
Framework experiment (Katz and Lindell, Theorem 4.6): every Framework forger, with arbitrary
coins, whose queries and forgery are bit strings shorter than `maxLen` (a forger
`A : MACForger (Msg maxLen) S R` relabeled into `List Bool`) has forgery probability at most the
PRF advantage of a deterministic distinguisher against HMAC on `Msg maxLen`, plus `1 / |S|`.
The random-function experiment of `PRF.prfAdvantage` needs a finite message space, which is why
the message length is bounded. -/
theorem hmacScheme_macAdvantage_le (maxLen : ℕ)
    (A : Cslib.Crypto.Framework.MACForger (Msg maxLen) S R) :
    ∃ r ∈ A.coins.support,
      Cslib.Crypto.Framework.macAdvantage (hmacScheme h iv lenBlock L toBits ipad opad)
          (A.relabel Subtype.val) ≤
        PRF.prfAdvantage (fun k (x : Msg maxLen) => hmac h iv lenBlock L toBits ipad opad k x.1)
          (fun _ : Unit => PRF.macReduction [] (A.forge r)) + 1 / Fintype.card S := by
  rw [Cslib.Crypto.Framework.macAdvantage,
    macGame_hmacScheme_relabel h iv lenBlock L toBits ipad opad Subtype.val_injective]
  exact hmacSchemeOn_macAdvantage_le h iv lenBlock L toBits ipad opad Subtype.val A

end HMAC

end Cslib.Crypto.HMAC
