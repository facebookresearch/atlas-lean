/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.SymmetricKey.PRF
public import CSLibExt.Crypto.SymmetricKey.EncryptThenMac
public import CSLibExt.Crypto.PublicKey.ElGamalCPA
public import CSLibExt.Crypto.Signatures.Lamport

/-!
# Migration: the bespoke games are instances of the generic Framework games

The scheme files `CSLibExt.Crypto.SymmetricKey.PRF`, `CSLibExt.Crypto.PublicKey.ElGamal` and
`CSLibExt.Crypto.Signatures.Lamport` predate the generic games of
`CSLibExt.Crypto.Framework.Games` and state their experiments directly as `PMF Bool`s over a
uniform sample space. This file presents each of their schemes as a Framework scheme, reusing the
existing Framework constructors, and proves the bespoke experiment **equal** (as a `PMF Bool`) to
the generic one, so every bound proved for the old game is a bound on the Framework game.

* `prfMac F`: the PRF-MAC `Mac_k(m) = F k m` (Katz and Lindell, Construction 4.5), defined as the
  deterministic MAC `EncryptThenMac.detMac` with a uniform key; correct by `prfMac_correct`
  (`EncryptThenMac.correct_detMac`); `prf_macGame_eq`:
  `Cslib.Crypto.PRF.macGame F A = macGame (prfMac F) ⟨U, A⟩`. For Framework forgers with
  **arbitrary** coins, `macGame_prfMac_eq_bind` writes the experiment as an average over the coins
  of the PRF file's game, `exists_macAdvantage_prfMac_le` is the PRF-MAC bound by coin fixing,
  and `macGame_prfMac_relabel` moves a forger along an injective map of messages.
* `prfEnc F`: PRF encryption `Enc_k(m) = (r, F k r + m)` (Construction 3.30), defined as the
  `EncryptThenMac.coinScheme` with a uniform key and uniform randomness `r`; correct by
  `prfEnc_correct` (`EncryptThenMac.correct_coinScheme`); `prf_cpaGame_eq`: for adversaries making
  at most `q` encryption queries over both stages,
  `Cslib.Crypto.PRF.cpaGame q F A = cpaGame (prfEnc F) ⟨U, A⟩`.
  Since `prfMac F` is a `detMac` and `prfEnc F` a `coinScheme`, they are components that
  `EncryptThenMac.ctxtAdvantage_le` and `EncryptThenMac.ccaAdvantage_le` accept as they are.
* ElGamal (Construction 11.16): the Framework scheme is `ElGamal.scheme q g` of
  `CSLibExt.Crypto.PublicKey.ElGamalCPA`; `elgamal_eavGame_eq` is `ElGamal.pubCpaGame_eq_eavGame`
  for the embedded old-style adversary:
  `ElGamal.eavGame q g A = pubCpaGame (ElGamal.scheme q g) A.toPubCPA`.
* `lamport f`: Lamport's scheme (Section 12.6.1) as a `SigScheme`; `lamport_forgeGame_eq`:
  `Lamport.forgeGame f A = sigGame (lamport f) A.toSigForger`, where `A.toSigForger` is the
  one-query forger (`toSigForger_queryBounded`).

Consequences such as `prf_macAdvantage_le` transport the old bounds to the Framework advantages.

**Coin-model gaps.** The old games draw all randomness uniformly from finite types; the Framework
games take the adversary's coins as an arbitrary `coins : PMF R`. The migration equalities
`prf_macGame_eq`, `prf_cpaGame_eq`, `elgamal_eavGame_eq` and `lamport_forgeGame_eq` are for
**uniform coins** `coins = uniformOfFintype R`: an old-style adversary is embedded with uniform
coins, and these equalities say nothing about Framework adversaries with non-uniform coins (which
the old games cannot express). Only the PRF-MAC also covers arbitrary coins, by averaging the
old game over them (`macGame_prfMac_eq_bind`, `exists_macAdvantage_prfMac_le`). Two further gaps,
both documented at the theorems:
* PRF-CPA: the old game draws the randomness of the encryption oracle up front (`Fin q → X`) and
  stops an adversary at its `(q + 1)`-st query; the Framework oracle samples afresh per query and
  never stops. The equality therefore needs `CPAAdversary.QueryBounded q`; without it the games
  differ.
* Lamport: the old forger always makes exactly one signing query; Framework one-time forgers may
  also make none. The embedding goes from old to new only.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Constructions 3.30, 4.5 and 11.16, and Section 12.6.1.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.Migration

open Cslib.Crypto.Framework FreeM OracleComp

/-- `Cslib.Probability.PMF.uniformOfFintype_prod` in the orientation the proofs below rewrite
with: uniform sampling on a product as two nested uniform samples. -/
private theorem uniformOfFintype_prod_eq_bind (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    Cslib.Probability.PMF.uniformOfFintype (α × β) =
      (Cslib.Probability.PMF.uniformOfFintype α).bind fun a =>
        (Cslib.Probability.PMF.uniformOfFintype β).bind fun b => PMF.pure (a, b) :=
  (Cslib.Probability.PMF.uniformOfFintype_prod α β).symm

/-! ### The PRF-MAC -/

section MAC

variable {K M T R : Type*} [Fintype K] [Nonempty K] [DecidableEq M] [Fintype R] [Nonempty R]

/-- The PRF-MAC `Mac_k(m) = F k m` with a uniform key (Katz and Lindell, Construction 4.5): the
deterministic MAC `EncryptThenMac.detMac` with tag function `F`, so verification recomputes the
tag. -/
noncomputable def prfMac [DecidableEq T] (F : K → M → T) : MACScheme M K T :=
  EncryptThenMac.detMac (Cslib.Probability.PMF.uniformOfFintype K) F

omit [DecidableEq M] in
/-- The PRF-MAC is correct (Katz and Lindell, Definition 4.1): the honest tag `F k m` verifies,
by `EncryptThenMac.correct_detMac`. -/
theorem prfMac_correct [DecidableEq T] (F : K → M → T) : (prfMac F).Correct :=
  EncryptThenMac.correct_detMac _ F

/-- An old-style forger `A : R → OracleComp M T (M × T)` of `Cslib.Crypto.PRF.macGame`, as a
Framework forger with uniform coins. -/
noncomputable def toMACForger (A : R → OracleComp M T (M × T)) : MACForger M T R :=
  ⟨Cslib.Probability.PMF.uniformOfFintype R, A⟩

/-- **PRF-MAC migration** (Katz and Lindell, Construction 4.5 and Definition 4.2): the PRF file's
forgery experiment is the Framework `Mac-forge` experiment of `prfMac F` for the forger with
uniform coins. -/
theorem prf_macGame_eq [DecidableEq T] (F : K → M → T) (A : R → OracleComp M T (M × T)) :
    Cslib.Crypto.PRF.macGame F A = macGame (prfMac F) (toMACForger A) := by
  simp only [Cslib.Crypto.PRF.macGame, macGame, prfMac, EncryptThenMac.detMac_gen,
    EncryptThenMac.detMac_tag, EncryptThenMac.detMac_verify, toMACForger, evalLog_pure_comp,
    uniformOfFintype_prod_eq_bind, PMF.map_bind, PMF.pure_map]
  congr 1; funext k; congr 1; funext r
  congr 1
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr ?_
  simp [Cslib.Crypto.PRF.MacWins, List.map_map, Function.comp_def, eq_comm]

/-- The PRF-MAC bound of `Cslib.Crypto.PRF.macGame_le` (Katz and Lindell, Theorem 4.6), for the
Framework advantage. -/
theorem prf_macAdvantage_le [Fintype M] [Fintype T] [Nonempty T] [DecidableEq T] (F : K → M → T)
    (A : R → OracleComp M T (M × T)) :
    macAdvantage (prfMac F) (toMACForger A) ≤
      Cslib.Crypto.PRF.prfAdvantage F (fun r => Cslib.Crypto.PRF.macReduction [] (A r)) +
        1 / Fintype.card T := by
  rw [macAdvantage, winProb, ← prf_macGame_eq]
  exact Cslib.Crypto.PRF.macGame_le F A

omit [Fintype R] [Nonempty R] in
/-- **The PRF-MAC experiment for arbitrary coins**: for a Framework forger whose coins
`A.coins : PMF R` are arbitrary, the `Mac-forge` experiment of `prfMac F` draws `r ← A.coins` and
runs the PRF file's forgery experiment for the forger fixed at the coins `r`. -/
theorem macGame_prfMac_eq_bind [DecidableEq T] (F : K → M → T) (A : MACForger M T R) :
    macGame (prfMac F) A =
      A.coins.bind fun r => Cslib.Crypto.PRF.macGame F (fun _ : Unit => A.forge r) := by
  simp only [macGame, Cslib.Crypto.PRF.macGame, prfMac, EncryptThenMac.detMac_gen,
    EncryptThenMac.detMac_tag, EncryptThenMac.detMac_verify, evalLog_pure_comp,
    ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind, PMF.map_comp, PMF.pure_map]
  rw [PMF.bind_comm]
  congr 1; funext r; congr 1; funext k
  rw [← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype Unit)]
  congr 1; funext u
  rw [Function.const_apply, Function.comp_apply, ← Bool.decide_and]
  exact decide_eq_decide.mpr
    (by simp [Cslib.Crypto.PRF.MacWins, List.map_map, Function.comp_def, eq_comm])

omit [Fintype R] [Nonempty R] in
/-- **The PRF-MAC bound for arbitrary coins** (Katz and Lindell, Theorem 4.6, with coin fixing):
for a Framework forger `A` with arbitrary coins there are coins `r` in the support of `A.coins`
such that the forgery advantage against `prfMac F` is at most the PRF advantage of the
deterministic distinguisher `PRF.macReduction [] (A.forge r)`, plus `1 / |T|`. -/
theorem exists_macAdvantage_prfMac_le [Fintype M] [Fintype T] [Nonempty T] [DecidableEq T]
    (F : K → M → T) (A : MACForger M T R) :
    ∃ r ∈ A.coins.support, macAdvantage (prfMac F) A ≤
      Cslib.Crypto.PRF.prfAdvantage F
        (fun _ : Unit => Cslib.Crypto.PRF.macReduction [] (A.forge r)) + 1 / Fintype.card T := by
  obtain ⟨r, hr, hle⟩ := Cslib.Probability.PMF.exists_mem_support_bind_apply_le A.coins
    (fun r => Cslib.Crypto.PRF.macGame F (fun _ : Unit => A.forge r)) true
  refine ⟨r, hr, le_trans ?_ (Cslib.Crypto.PRF.macGame_le _ _)⟩
  rw [macAdvantage, winProb, macGame_prfMac_eq_bind]
  exact ENNReal.toReal_mono (PMF.apply_ne_top _ _) hle

omit [Fintype R] [Nonempty R] in
/-- **Relabeling along an injection**: for an injective `e : M → M'`, a forger `A` against
`prfMac fun k m => G k (e m)`, relabeled along `e` (`MACForger.relabel`), has the same `Mac-forge`
experiment against `prfMac G`; freshness of the forged message is preserved because `e` is
injective. -/
theorem macGame_prfMac_relabel {M' : Type*} [DecidableEq M'] [DecidableEq T] (G : K → M' → T)
    {e : M → M'} (he : Function.Injective e) (A : MACForger M T R) :
    macGame (prfMac G) (A.relabel e) = macGame (prfMac fun k m => G k (e m)) A := by
  simp only [macGame, MACForger.relabel, prfMac, EncryptThenMac.detMac_gen,
    EncryptThenMac.detMac_tag, EncryptThenMac.detMac_verify]
  congr 1; funext k; congr 1; funext r
  rw [evalLog_relabel, PMF.map_comp]
  congr 1; funext p
  have hmap : (p.2.map fun q => (e q.1, q.2)).map Prod.fst = (p.2.map Prod.fst).map e := by
    simp [List.map_map, Function.comp_def]
  simp only [Function.comp_apply, hmap, List.mem_map_of_injective he]

end MAC

/-! ### PRF encryption -/

section CPA

open Cslib.Crypto.PRF (encrypt decrypt runEnc cpaGuess)

variable {K X Y R : Type*} [Fintype K] [Nonempty K] [Fintype X] [Nonempty X]
  [AddCommGroup Y] [Fintype R] [Nonempty R]

/-- PRF encryption `Enc_k(m) = (r, F k r + m)` with a uniform key and uniform fresh randomness
`r` (Katz and Lindell, Construction 3.30): the `EncryptThenMac.coinScheme` that encrypts with
`PRF.encrypt (F k) m r` and decrypts with `PRF.decrypt (F k)`. -/
noncomputable def prfEnc (F : K → X → Y) : SymmEncScheme Y K (X × Y) :=
  EncryptThenMac.coinScheme (Cslib.Probability.PMF.uniformOfFintype K)
    (Cslib.Probability.PMF.uniformOfFintype X) (fun k => encrypt (F k))
    fun k c => some (decrypt (F k) c)

/-- PRF encryption is correct, by `EncryptThenMac.correct_coinScheme` and `PRF.decrypt_encrypt`. -/
theorem prfEnc_correct (F : K → X → Y) : (prfEnc F).Correct :=
  EncryptThenMac.correct_coinScheme fun k m r =>
    congrArg some (Cslib.Crypto.PRF.decrypt_encrypt (F k) m r)

/-- An old-style CPA adversary of `Cslib.Crypto.PRF.cpaGame` as a Framework CPA adversary with
uniform coins. -/
noncomputable def toCPAAdversary (A : Cslib.Crypto.PRF.CPAAdversary X Y R) :
    CPAAdversary Y (X × Y) R :=
  ⟨Cslib.Probability.PMF.uniformOfFintype R, A⟩

omit [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- `runEnc` of a sequential composition: the second computation resumes at the query index the
first one stopped at. -/
theorem runEnc_bind {q : ℕ} {β γ : Type*} (f : X → Y) (ρ : Fin q → X)
    (g : β → OracleComp Y (X × Y) γ) :
    ∀ (c : OracleComp Y (X × Y) β) (i : ℕ), runEnc f ρ (PFunctor.FreeM.bind c g) i =
      (runEnc f ρ c i).bind fun p => runEnc f ρ (g p.1) p.2
  | .pure _, _ => rfl
  | .liftBind m k, i => by
    change runEnc f ρ (.liftBind m fun y => PFunctor.FreeM.bind (k y) g) i = _
    rw [runEnc, runEnc]
    split_ifs with h
    · exact runEnc_bind f ρ g _ (i + 1)
    · rfl

omit [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- Dropping the first entry of the up-front randomness shifts the query index by one. -/
theorem runEnc_succ {n : ℕ} {β : Type*} (f : X → Y) (ρ : Fin (n + 1) → X) :
    ∀ (c : OracleComp Y (X × Y) β) (i : ℕ),
      runEnc f ρ c (i + 1) = (runEnc f (Fin.tail ρ) c i).map fun p => (p.1, p.2 + 1)
  | .pure _, _ => rfl
  | .liftBind m k, i => by
    rw [runEnc, runEnc]
    by_cases h : i < n
    · rw [dite_eq_left (by omega), dite_eq_left h]
      exact runEnc_succ f ρ _ (i + 1)
    · rw [dite_eq_right (by omega), dite_eq_right h]
      rfl

omit [Fintype K] [Nonempty K] [Fintype R] [Nonempty R] in
/-- **Up-front versus fresh randomness**: for an algorithm making at most `n` encryption
queries, answering its `i`-th query with the `i`-th entry of a uniform `ρ : Fin n → X` gives the
same output distribution as sampling fresh randomness per query (`evalPMF`), and never stops
it. -/
theorem map_uniform_runEnc {β : Type*} (f : X → Y) :
    ∀ (n : ℕ) (c : OracleComp Y (X × Y) β), IsQueryBounded n c →
      (Cslib.Probability.PMF.uniformOfFintype (Fin n → X)).map
          (fun ρ => (runEnc f ρ c 0).map Prod.fst) =
        (evalPMF (fun m => (Cslib.Probability.PMF.uniformOfFintype X).map (encrypt f m)) c).map
          some
  | _, .pure a, _ => by
    change (Cslib.Probability.PMF.uniformOfFintype _).map (Function.const _ (some a)) = _
    rw [PMF.map_const, evalPMF_pure', PMF.pure_map]
  | 0, .liftBind _ _, hc => hc.elim
  | n + 1, .liftBind m k, hc => by
    have step : ∀ ρ : Fin (n + 1) → X, (runEnc f ρ (.liftBind m k) 0).map Prod.fst =
        (runEnc f (Fin.tail ρ) (k (encrypt f m (ρ 0))) 0).map Prod.fst := by
      intro ρ
      rw [runEnc, dite_eq_left (Nat.succ_pos n), runEnc_succ, Option.map_map]
      rfl
    simp only [step, Cslib.Probability.PMF.uniformOfFintype_fin_succ X n, PMF.map_bind,
      PMF.map_comp, Function.comp_def, Fin.tail_cons, Fin.cons_zero, evalPMF_liftBind,
      PMF.bind_map]
    congr 1
    funext x
    exact map_uniform_runEnc f n _ (hc _)

omit [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] [Fintype R] [Nonempty R] in
/-- The old game's guess is the run of the two stages composed into one oracle algorithm. -/
theorem cpaGuess_eq {q : ℕ} (f : X → Y) (ρ : Fin q → X) (rs : X) (b : Bool)
    (c : OracleComp Y (X × Y) ((Y × Y) × (X × Y → OracleComp Y (X × Y) Bool))) :
    cpaGuess f ρ rs b c = ((runEnc f ρ (PFunctor.FreeM.bind c fun out =>
      out.2 (encrypt f (pick out.1 b) rs)) 0).map Prod.fst).getD false := by
  rw [cpaGuess, runEnc_bind, Option.map_bind]
  rfl

/-- The challenge-bit-and-coin sample space of the old game, reordered so that the challenge
bit comes first and the up-front oracle randomness last. -/
def cpaReorder (q : ℕ) :
    Bool × K × R × X × (Fin q → X) ≃ K × (Fin q → X) × X × Bool × R where
  toFun ω := (ω.2.1, ω.2.2.2.2, ω.2.2.2.1, ω.1, ω.2.2.1)
  invFun ω := (ω.2.2.2.1, ω.1, ω.2.2.2.2, ω.2.2.1, ω.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **PRF-CPA migration** (Katz and Lindell, Construction 3.30 and Definition 3.22): for an
adversary making at most `q` encryption queries over both stages, the PRF file's CPA experiment
(with the oracle randomness drawn up front as `ρ : Fin q → X`) is the Framework `PrivK^cpa`
experiment of `prfEnc F` (fresh randomness per query) for the adversary with uniform coins.

Gap: without the query bound the two games differ, since the old game stops an adversary at its
`(q + 1)`-st query and outputs the guess `false`. -/
theorem prf_cpaGame_eq {q : ℕ} (F : K → X → Y) (A : Cslib.Crypto.PRF.CPAAdversary X Y R)
    (hA : (toCPAAdversary A).QueryBounded q) :
    Cslib.Crypto.PRF.cpaGame q F A = cpaGame (prfEnc F) (toCPAAdversary A) := by
  -- the inner experiment for fixed `b, k, r, rs`
  have inner : ∀ (b : Bool) (k : K) (r : R) (rs : X),
      ((Cslib.Probability.PMF.uniformOfFintype (Fin q → X)).bind fun ρ =>
        PMF.pure (cpaGuess (F k) ρ rs b (A r) == b)) =
      (evalPMF ((prfEnc F).enc k) (PFunctor.FreeM.bind (A r) fun out =>
        out.2 (encrypt (F k) (pick out.1 b) rs))).map (· == b) := by
    intro b k r rs
    have hb : IsQueryBounded q (PFunctor.FreeM.bind (A r) fun out =>
        out.2 (encrypt (F k) (pick out.1 b) rs)) :=
      isQueryBounded_bind ((hA r).mono fun out j h => h _)
    have h := congrArg (PMF.map fun o : Option Bool => o.getD false == b)
      (map_uniform_runEnc (F k) q _ hb)
    simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at h
    simp only [cpaGuess_eq]
    exact h
  -- the Framework experiment, with the challenge randomness pulled out
  have rhs : ∀ (b : Bool) (k : K) (r : R),
      ((evalPMF ((prfEnc F).enc k) (A r)).bind fun out =>
        ((prfEnc F).enc k (pick out.1 b)).bind fun c =>
          (evalPMF ((prfEnc F).enc k) (out.2 c)).map (· == b)) =
      (Cslib.Probability.PMF.uniformOfFintype X).bind fun rs =>
        (evalPMF ((prfEnc F).enc k) (PFunctor.FreeM.bind (A r) fun out =>
          out.2 (encrypt (F k) (pick out.1 b) rs))).map (· == b) := by
    intro b k r
    simp only [prfEnc, EncryptThenMac.coinScheme, PMF.bind_map, Function.comp_def,
      evalPMF_freeMBind, PMF.map_bind]
    exact PMF.bind_comm _ _ _
  rw [Cslib.Crypto.PRF.cpaGame, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv
    (cpaReorder q), PMF.map_comp]
  simp only [cpaGame, bitGame, cpaExp, fairCoin, toCPAAdversary, uniformOfFintype_prod_eq_bind,
    PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map, rhs]
  congr 1; funext b; congr 1; funext k; congr 1; funext r; congr 1; funext rs
  exact inner b k r rs

/-- The PRF-CPA bound of `Cslib.Crypto.PRF.cpaAdvantage_le` (Katz and Lindell, Theorem 3.31), for
the Framework CPA advantage of a `q`-query adversary. -/
theorem prf_cpaAdvantage_le [DecidableEq X] [Fintype Y] {q : ℕ} (F : K → X → Y)
    (A : Cslib.Crypto.PRF.CPAAdversary X Y R) (hA : (toCPAAdversary A).QueryBounded q) :
    cpaAdvantage (prfEnc F) (toCPAAdversary A) ≤
      Cslib.Crypto.PRF.prfAdvantage F (Cslib.Crypto.PRF.cpaReduction q A) +
        q / (2 * Fintype.card X) := by
  have h := Cslib.Crypto.PRF.cpaAdvantage_le (q := q) F A
  rwa [Cslib.Crypto.PRF.cpaAdvantage, prf_cpaGame_eq F A hA] at h

end CPA

/-! ### ElGamal -/

section ElGamal

open Cslib.Crypto.PublicKey Cslib.Crypto.PublicKey.ElGamal

variable {G : Type*} [CommGroup G] (g : G) (q : ℕ) [NeZero q] {R : Type*} [Fintype R]
  [Nonempty R]

/-- An ElGamal eavesdropper as a Framework public-key adversary with uniform coins. -/
noncomputable def _root_.Cslib.Crypto.PublicKey.ElGamal.Adversary.toPubCPA (A : Adversary G R) :
    PubCPAAdversary G G (G × G) R :=
  ⟨Cslib.Probability.PMF.uniformOfFintype R, A.choose, A.guess⟩

/-- **ElGamal migration** (Katz and Lindell, Definition 11.2): the ElGamal file's eavesdropping
experiment is the Framework `PubK^eav` experiment of `ElGamal.scheme q g` for the adversary with
uniform coins. This is `ElGamal.pubCpaGame_eq_eavGame` for the embedded adversary `A.toPubCPA`,
whose underlying ElGamal adversary is `A` itself; `ElGamal.pubCpaAdvantage_eq_eavAdvantage` and
`ElGamal.eavAdvantage_eq_ddhAdvantage` give the advantage and the DDH bound. -/
theorem elgamal_eavGame_eq (A : Adversary G R) :
    eavGame q g A = pubCpaGame (ElGamal.scheme q g) A.toPubCPA :=
  (pubCpaGame_eq_eavGame (q := q) g A.toPubCPA rfl).symm

end ElGamal

/-! ### Lamport signatures -/

section Lamport

open Cslib.Crypto.Signatures.Lamport

variable {X Y : Type*} (f : X → Y) {ℓ : ℕ} [Fintype X] [Nonempty X] [DecidableEq Y] {R : Type*}
  [Fintype R] [Nonempty R]

/-- Lamport's one-time scheme (Katz and Lindell, Section 12.6.1) as a Framework `SigScheme`:
uniform secret key `sk`, public key `f ∘ sk`, deterministic signing. -/
noncomputable def lamport : SigScheme (Fin ℓ → Bool) (Fin ℓ × Bool → Y) (Fin ℓ × Bool → X)
    (Fin ℓ → X) where
  gen := (Cslib.Probability.PMF.uniformOfFintype (Fin ℓ × Bool → X)).map fun sk =>
    (publicKey f sk, sk)
  sign sk m := PMF.pure (sign sk m)
  verify pk m σ := decide (Verify f pk m σ)

/-- Lamport's scheme is correct, by `Lamport.verify_sign`. -/
theorem lamport_correct : (lamport f (ℓ := ℓ)).Correct := by
  intro kp hkp m σ hσ
  simp only [lamport, PMF.support_map, Set.mem_image, PMF.support_pure,
    Set.mem_singleton_iff] at hkp hσ
  obtain ⟨sk, -, rfl⟩ := hkp
  subst hσ
  exact decide_eq_true (verify_sign f sk m)

/-- An old-style one-time forger as a Framework forger with uniform coins: it makes exactly one
signing query, on `A.choose pk r`. -/
noncomputable def _root_.Cslib.Crypto.Signatures.Lamport.Forger.toSigForger
    (A : Forger X Y R ℓ) : SigForger (Fin ℓ → Bool) (Fin ℓ × Bool → Y) (Fin ℓ → X) R :=
  ⟨Cslib.Probability.PMF.uniformOfFintype R, fun pk r =>
    query (A.choose pk r) fun σ => done (A.forge pk σ r)⟩

omit [Fintype X] [Nonempty X] [DecidableEq Y] in
/-- The embedded forger is a one-time forger (Katz and Lindell, Section 12.6.1). -/
theorem toSigForger_queryBounded (A : Forger X Y R ℓ) : A.toSigForger.QueryBounded 1 :=
  fun _ _ => isQueryBounded_liftBind fun _ => isQueryBounded_pure 0 _

/-- **Lamport migration** (Katz and Lindell, Definition 12.2 and Section 12.6.1): the Lamport
file's one-time forgery experiment is the Framework `Sig-forge` experiment of `lamport f` for the
one-query forger with uniform coins. -/
theorem lamport_forgeGame_eq (A : Forger X Y R ℓ) :
    forgeGame f A = sigGame (lamport f) A.toSigForger := by
  simp only [forgeGame, sigGame, lamport, Forger.toSigForger, uniformOfFintype_prod_eq_bind,
    PMF.map_bind, PMF.pure_map, PMF.bind_map, Function.comp_def, PMF.pure_bind, evalLog_liftBind,
    evalLog_pure]
  congr 1; funext sk; congr 1; funext r
  congr 1
  rw [← Bool.decide_and]
  refine decide_eq_decide.mpr ?_
  simp [Forger.Wins, and_comm]

/-- Lamport's one-time security bound `Lamport.forgeGame_le` (Katz and Lindell, Theorem 12.16),
for the Framework forgery advantage. -/
theorem lamport_sigAdvantage_le [NeZero ℓ] (A : Forger X Y R ℓ) :
    sigAdvantage (lamport f) A.toSigForger ≤
      2 * ℓ * ((Cslib.Crypto.Signatures.Lamport.invertGame f (invert f A)) true).toReal := by
  rw [sigAdvantage, winProb, ← lamport_forgeGame_eq]
  exact forgeGame_le f A

end Lamport

end Cslib.Crypto.Framework.Migration
