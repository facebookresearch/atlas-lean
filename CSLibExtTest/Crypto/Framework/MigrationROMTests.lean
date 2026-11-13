/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Migration
public import CSLibExt.Crypto.Framework.RandomOracle

/-!
# Tests for the Framework migration equalities and the random-oracle model

Each migration equality is used to compute a bespoke game on a toy scheme from its Framework
counterpart (or back); every computed value would fail for a different game, so the equalities
are exercised, not just restated.

* **PRF-MAC.** With the (insecure) keyed function `F k m = k + m` on `ZMod 2`, honest tags
  verify (`prfMac_correct`) and a wrong tag does not; a forger that
  queries `0` and forges on `1` wins with probability `1`, a replay of the queried message wins
  with probability `0`, in both the PRF file's game and the Framework game. With point-mass
  (non-uniform) coins, `macGame_prfMac_eq_bind` computes the Framework game from the PRF file's
  game at that coin.
* **PRF-CPA.** With `F k r = k` (constant in `r`), a one-query adversary learns `k` from an
  encryption of `0` and wins the PRF file's CPA game with probability `1`.
* **ElGamal.** With the degenerate generator `g = 1` the ciphertext is `(1, m)`, and an adversary
  reading `m` wins the ElGamal file's eavesdropping game with probability `1`.
* **Lamport.** With `f = id` the public key is the secret key, and a one-query forger wins the
  Lamport file's forgery game with probability `1`.
* **Random oracle.** Two queries of the same point always agree (probability `1`); a fresh answer
  is uniform (probability `1/2` on `Bool`); two distinct points collide with probability exactly
  `1/2` on `Bool`, which meets the birthday bound `2 · 1 / (2 · 2)`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.MigrationROM

open Cslib.Crypto.Framework Cslib.Crypto.Framework.Migration FreeM OracleComp

/-! ### PRF-MAC -/

/-- An insecure keyed function on `ZMod 2`. -/
def macF (k m : ZMod 2) : ZMod 2 := k + m

/-- Query `0`, learn `k`, and forge the tag `k + 1` on the fresh message `1`. -/
def macForge : Unit → OracleComp (ZMod 2) (ZMod 2) (ZMod 2 × ZMod 2) :=
  fun _ => query 0 fun t => done (1, t + 1)

/-- Replay the queried message. -/
def macReplay : Unit → OracleComp (ZMod 2) (ZMod 2) (ZMod 2 × ZMod 2) :=
  fun _ => query 0 fun t => done (0, t)

/-- `prfMac_correct`: the honest tag `macF 1 0 = 1` on message `0` under key `1` verifies (the
wrong tag `0` would not: `(prfMac macF).verify 1 0 0 = false`). -/
theorem prfMac_correct_test : (prfMac macF).verify 1 0 1 = true :=
  prfMac_correct macF 1 (by simp [prfMac]) 0 1 (by simp [prfMac, macF])

/-- The wrong tag does not verify, so `prfMac_correct_test` is not vacuous. -/
example : (prfMac macF).verify 1 0 0 = false := by decide

/-- The forger wins the Framework `Mac-forge` game with probability `1`. -/
theorem framework_macGame_forge : macGame (prfMac macF) (toMACForger macForge) = PMF.pure true := by
  simp only [macGame, prfMac, EncryptThenMac.detMac_gen, EncryptThenMac.detMac_tag,
    EncryptThenMac.detMac_verify, toMACForger, macForge, evalLog_pure_comp, run, queries,
    PMF.pure_map]
  refine (congrArg (PMF.bind _) (funext fun k => ?_)).trans (PMF.bind_const _ _)
  refine (congrArg (PMF.bind _) (funext fun _ => ?_)).trans (PMF.bind_const _ _)
  congr 1
  revert k
  decide

/-- The PRF file's forgery game, computed through `prf_macGame_eq`. -/
theorem prf_macGame_forge : Cslib.Crypto.PRF.macGame macF macForge = PMF.pure true := by
  rw [prf_macGame_eq, framework_macGame_forge]

/-- The same forger with point-mass coins `true : Bool`, which are not uniform. -/
noncomputable def macForgeAtTrue : MACForger (ZMod 2) (ZMod 2) Bool :=
  ⟨PMF.pure true, fun _ => macForge ()⟩

/-- For arbitrary coins, `macGame_prfMac_eq_bind` reduces the Framework game to the PRF file's
game at the coin `true`, which the forger wins with probability `1`. -/
example : macGame (prfMac macF) macForgeAtTrue = PMF.pure true := by
  rw [macGame_prfMac_eq_bind, show macForgeAtTrue.coins = PMF.pure true from rfl, PMF.pure_bind]
  exact prf_macGame_forge

/-- A replay never wins, in the PRF file's game. -/
theorem prf_macGame_replay : Cslib.Crypto.PRF.macGame macF macReplay = PMF.pure false := by
  rw [prf_macGame_eq]
  simp only [macGame, prfMac, EncryptThenMac.detMac_gen, EncryptThenMac.detMac_tag,
    EncryptThenMac.detMac_verify, toMACForger, macReplay, evalLog_pure_comp, run, queries,
    PMF.pure_map]
  refine (congrArg (PMF.bind _) (funext fun k => ?_)).trans (PMF.bind_const _ _)
  refine (congrArg (PMF.bind _) (funext fun _ => ?_)).trans (PMF.bind_const _ _)
  congr 1

/-! ### PRF-CPA -/

/-- A keyed function that ignores its input: `F k r = k`. -/
def cpaF (k _r : ZMod 2) : ZMod 2 := k

/-- Ask for an encryption of `0`, which reveals the pad `k`; challenge with `(0, 1)` and unmask. -/
def cpaAdv : Cslib.Crypto.PRF.CPAAdversary (ZMod 2) (ZMod 2) Unit :=
  fun _ => query 0 fun c => done ((0, 1), fun ch => done (ch.2 - c.2 == 1))

/-- The adversary makes one encryption query. -/
theorem cpaAdv_queryBounded : (toCPAAdversary cpaAdv).QueryBounded 1 :=
  fun _ _ _ => trivial

/-- In the Framework CPA experiment the adversary always outputs the challenge bit. -/
theorem framework_cpaExp (b : Bool) :
    cpaExp (prfEnc cpaF) (toCPAAdversary cpaAdv) b = PMF.pure b := by
  simp only [cpaExp, prfEnc, EncryptThenMac.coinScheme, toCPAAdversary, cpaAdv, evalPMF_liftBind,
    evalPMF_pure', PMF.bind_map, PMF.pure_bind, Function.comp_def, PMF.bind_bind,
    Cslib.Crypto.PRF.encrypt, cpaF]
  cases b
  · simp only [PMF.bind_const]; simp; rfl
  · simp [PMF.bind_const]

/-- The PRF file's CPA game, computed through `prf_cpaGame_eq`: the adversary always wins. -/
theorem prf_cpaGame_adv : Cslib.Crypto.PRF.cpaGame 1 cpaF cpaAdv = PMF.pure true := by
  rw [prf_cpaGame_eq cpaF cpaAdv cpaAdv_queryBounded, cpaGame, bitGame]
  simp only [framework_cpaExp, PMF.pure_map, beq_self_eq_true]
  exact PMF.bind_const _ _

/-! ### ElGamal -/

section ElGamalTest

open Cslib.Crypto.PublicKey.ElGamal

/-- The degenerate generator `g = 1` of `Multiplicative (ZMod 2)`: the ciphertext is `(1, m)`. -/
def egAdv : Adversary (Multiplicative (ZMod 2)) Unit where
  choose _ _ := (1, Multiplicative.ofAdd 1)
  guess _ c _ := c.2 == Multiplicative.ofAdd 1

/-- In the Framework `PubK^eav` experiment the adversary always outputs the challenge bit. -/
theorem framework_pubCpaExp (b : Bool) :
    pubCpaExp (scheme 2 (1 : Multiplicative (ZMod 2))) egAdv.toPubCPA b = PMF.pure b := by
  simp only [pubCpaExp, scheme, Adversary.toPubCPA, egAdv, PMF.bind_map, PMF.map_comp,
    Function.comp_def, publicKey, encrypt, Cslib.Crypto.PublicKey.gpow, one_pow, one_mul]
  cases b <;> simp [PMF.bind_const] <;> exact PMF.map_const _ _

/-- The ElGamal file's eavesdropping game, computed through `elgamal_eavGame_eq`. -/
theorem eavGame_degenerate : eavGame 2 (1 : Multiplicative (ZMod 2)) egAdv = PMF.pure true := by
  rw [elgamal_eavGame_eq, pubCpaGame, bitGame]
  simp only [framework_pubCpaExp, PMF.pure_map, beq_self_eq_true]
  exact PMF.bind_const _ _

end ElGamalTest

/-! ### Lamport -/

section LamportTest

open Cslib.Crypto.Signatures.Lamport

/-- With `f = id` the public key reveals the secret key: forge on `true` from it. -/
def lamAdv : Forger Bool Bool Unit 1 where
  choose _ _ := fun _ => false
  forge pk _ _ := (fun _ => true, fun i => pk (i, true))

/-- The forger wins the Framework `Sig-forge` game with probability `1`. -/
theorem framework_sigGame : sigGame (lamport id) lamAdv.toSigForger = PMF.pure true := by
  simp only [sigGame, lamport, Forger.toSigForger, lamAdv, evalLog_liftBind, evalLog_pure,
    PMF.pure_bind, PMF.pure_map, PMF.bind_map, Function.comp_def]
  refine (congrArg (PMF.bind _) (funext fun sk => ?_)).trans (PMF.bind_const _ _)
  refine (congrArg (PMF.bind _) (funext fun _ => ?_)).trans (PMF.bind_const _ _)
  congr 1
  simp [Verify, publicKey, funext_iff]

/-- The Lamport file's forgery game, computed through `lamport_forgeGame_eq`. -/
theorem forgeGame_id : forgeGame id lamAdv = PMF.pure true := by
  rw [lamport_forgeGame_eq, framework_sigGame]

end LamportTest

/-! ### Random oracle -/

section RO

open RandomOracle

/-- Querying the same point twice gives the same answer, with probability `1`. -/
theorem ro_same_query :
    eval (Rng := Bool) (query (0 : Fin 3) fun y₁ => query 0 fun y₂ => done (y₁ == y₂)) =
      PMF.pure true := by
  rw [eval, LazySampling.lazyRF_query_query]
  simp only [LazySampling.lazyRF, LazySampling.runState, beq_self_eq_true, PMF.map_bind,
    PMF.pure_map]
  exact PMF.bind_const _ _

/-- A fresh answer is uniform: it is `true` with probability `1/2`. -/
theorem ro_fresh : eval (Rng := Bool) (query (2 : Fin 3) fun y => done y) true = 1 / 2 := by
  have h : eval (Rng := Bool) (query (2 : Fin 3) fun y => done y) =
      Cslib.Probability.PMF.uniformOfFintype Bool := by
    rw [← LazySampling.rfStep_map_fst_of_none (T := LazySampling.Table.empty) (x := (2 : Fin 3))
      rfl, eval, LazySampling.lazyRF]
    simp only [LazySampling.runState, PMF.map_bind, PMF.pure_map]
    rw [← PMF.bind_pure_comp]
    rfl
  rw [h, Cslib.Probability.PMF.uniformOfFintype_apply]
  simp

/-- Two distinct points collide with probability exactly `1/2` on `Bool`. -/
theorem ro_collision_two : winProb (collisionExp (Rng := Bool) ![(0 : Fin 3), 1]) = 1 / 2 := by
  have hinj : Function.Injective ![(0 : Fin 3), 1] := by decide
  rw [winProb, collisionExp_eq hinj]
  change Cslib.Crypto.Birthday.collisionProb Bool 2 = 1 / 2
  rw [Cslib.Crypto.Birthday.collisionProb_eq]
  norm_num [Nat.descFactorial]

/-- The birthday bound for two distinct queries to a random oracle with range `Bool`. -/
example : winProb (collisionExp (Rng := Bool) ![(0 : Fin 3), 1]) ≤ 2 * (2 - 1) / (2 * 2) := by
  have h := winProb_collisionExp_le (Rng := Bool) (q := 2) (xs := ![(0 : Fin 3), 1])
    (by decide)
  simpa using h

end RO

end Cslib.Crypto.FrameworkTests.MigrationROM
