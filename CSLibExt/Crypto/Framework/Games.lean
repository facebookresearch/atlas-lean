/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.Framework.Oracle
public import Cslib.Crypto.Protocols.PerfectSecrecy.Encryption

/-!
# Generic security games

One canonical way to write a computational security game, for the four primitives of Katz and
Lindell's textbook. Every scheme is a structure with probabilistic algorithms valued in `PMF`;
every adversary carries its random coins as a distribution `coins : PMF R` and is otherwise a
deterministic function of those coins; oracle access is an `OracleComp` interpreted by
`FreeM.evalPMF` (fresh randomness per oracle call); every experiment is a `PMF Bool`, and every
security notion is a `winProb`, `advantage` or `guessAdvantage`
(`CSLibExt.Crypto.Framework.Advantage`).

**Schemes.** All type arguments are in the order message, key(s), output, as in CSLib's
`EncScheme`.
* `SymmEncScheme M K C` (Katz and Lindell, Definition 3.7): `gen : PMF K`,
  `enc : K → M → PMF C`, `dec : K → C → Option M` (`none` is the error symbol `⊥`).
* `PKEScheme M PK SK C` (Definition 11.1): `gen : PMF (PK × SK)`, `enc`, `dec`.
* `MACScheme M K T` (Definition 4.1): `gen`, `tag : K → M → PMF T`, `verify : K → M → T → Bool`.
* `SigScheme M PK SK S` (Definition 12.1): `gen`, `sign`, `verify`.
Correctness is a separate predicate (`Correct`) rather than a field, so that insecure or toy
schemes, and schemes that are correct only with overwhelming probability, are expressible.

**Relationship to CSLib's `EncScheme`.** `Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme`
(Katz and Lindell, Definition 2.1) is designed for perfect secrecy: decryption is total, and
correctness is a field. `SymmEncScheme` is deliberately separate: computational definitions need
`⊥` from decryption (CCA) and schemes without bundled correctness proofs. `ofEncScheme` embeds
every `EncScheme` (decryption composed with `some`), and `correct_ofEncScheme` transports its
correctness; CSLib's definitions are unchanged.

**Experiments.** The two-stage adversaries of the indistinguishability experiments are written in
continuation style: the first stage outputs the challenge messages together with the second stage,
a function of the challenge ciphertext, so state passes between the stages without a separate
state type (the pattern of `Cslib.Crypto.PRF.CPAAdversary`).
* `cpaExp S A b`, `cpaGame S A = bitGame (cpaExp S A)`, `cpaAdvantage`: `PrivK^cpa`
  (Definition 3.22). The eavesdropping experiment `PrivK^eav` (Definition 3.8) is the case of
  adversaries making no queries, `CPAAdversary.QueryBounded 0`.
* `ccaExp`, `ccaGame`, `ccaAdvantage`: `PrivK^cca` (Definition 3.33), with oracles for both
  `Enc_k` and `Dec_k`; in the second stage the decryption oracle answers `⊥` on the challenge
  ciphertext (equivalent to forbidding that query).
* `ctxtGame`, `ctxtAdvantage`: ciphertext integrity (`INT-CTXT`, Bellare and Namprempre; the
  ciphertext form of the unforgeable encryption of Katz and Lindell, Section 4.5): a
  `CtxtForger` with an encryption oracle wins by outputting a valid ciphertext that was never an
  oracle answer.
* `pubCpaExp`, `pubCpaGame`, `pubCpaAdvantage`: `PubK^eav` (Definition 11.2), which equals CPA
  security for public-key schemes (Proposition 11.3): with the public key in hand an encryption
  oracle is redundant.
* `PubOracleCPAAdversary`, `pubOracleCpaExp`, `pubOracleCpaGame`, `pubOracleCpaAdvantage`:
  `PubK^cpa` (Section 11.2.2), the public-key experiment **with** an encryption oracle in both
  stages. `pubCpaAdvantage_toEav` proves Proposition 11.3 as an exact equality: for a scheme
  with `Enc_pk(m) = encR pk m ρ` for uniform `ρ` and an adversary making at most `n` queries,
  the eavesdropper `A.toEav encR n`, which presamples `n` coins per stage and answers the
  queries itself (`OracleComp.runCoins`), has exactly `A`'s CPA advantage; its coins are
  uniform whenever `A`'s are (`PubOracleCPAAdversary.toEav_coins_uniform`).
* `pubCcaExp`, `pubCcaGame`, `pubCcaAdvantage`: `PubK^cca` (Definition 11.8).
* `macGame`, `macAdvantage`: `Mac-forge` (Definition 4.2), existential unforgeability under an
  adaptive chosen-message attack; `macStrongGame` is the strong variant (Definition 4.3).
* `sigGame`, `sigAdvantage`: `Sig-forge` (Definition 12.2). One-time security (Section 12.6.1,
  Lamport) is the case `SigForger.QueryBounded 1`.

Each adversary structure has a `QueryBounded q` predicate (at most `q` oracle queries in total,
along every path), built from `FreeM.IsQueryBounded`.

**Known simplifications.** Message spaces are types, so Katz and Lindell's requirement that the
two challenge messages have equal length is expressed by choosing a fixed-length message type;
variable-length message spaces are not modelled. There is no security parameter here: these are
concrete (fixed-size) games, and `CSLibExt.Crypto.Framework.Asymptotic` indexes them by `n`.

**Coexistence with existing files.** `Cslib.Crypto.PublicKey.ElGamal.eavGame` has the shape of
`pubCpaGame` with uniform coins; `Cslib.Crypto.PRF.cpaGame` and `Cslib.Crypto.PRF.macGame` have the
shape of `cpaGame` and `macGame`, but sample the oracle's randomness up front instead of per query;
`Cslib.Crypto.Signatures.Lamport.forgeGame` has the shape of a one-query `sigGame`. None is
migrated here; the Wave-2 migration must prove each equal to its generic instance.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Definitions 2.1, 3.7, 3.8, 3.22, 3.33, 4.1–4.3, 11.1, 11.2, 11.8, 12.1, 12.2,
  Section 4.5 (unforgeable encryption), Section 11.2.2 (Proposition 11.3), and Section 12.6.1.
* M. Bellare and C. Namprempre, *Authenticated encryption: relations among notions and analysis
  of the generic composition paradigm*, ASIACRYPT 2000.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open FreeM OracleComp

universe u

/-- The message selected by the challenge bit: `m.2` for `true` (`b = 1`), `m.1` for `false`. -/
def pick {M : Type*} (m : M × M) (b : Bool) : M := if b then m.2 else m.1

@[simp] theorem pick_true {M : Type*} (m : M × M) : pick m true = m.2 := rfl

@[simp] theorem pick_false {M : Type*} (m : M × M) : pick m false = m.1 := rfl

/-! ### Private-key encryption -/

/-- A private-key encryption scheme for computational security (Katz and Lindell,
Definition 3.7): probabilistic key generation and encryption, and decryption that may fail
(`none` is `⊥`). Separate from CSLib's perfect-secrecy `EncScheme`; see `ofEncScheme`. -/
structure SymmEncScheme (M K C : Type*) where
  /-- Key generation `Gen`. -/
  gen : PMF K
  /-- Probabilistic encryption `Enc_k(m)`. -/
  enc : K → M → PMF C
  /-- Deterministic decryption `Dec_k(c)`, with `none` for `⊥`. -/
  dec : K → C → Option M

namespace SymmEncScheme

variable {M K C : Type*}

/-- **Correctness** (Katz and Lindell, Definition 3.7): for every key in the support of `Gen`,
decryption recovers every message from every ciphertext in the support of its encryption. -/
def Correct (S : SymmEncScheme M K C) : Prop :=
  ∀ k ∈ S.gen.support, ∀ m, ∀ c ∈ (S.enc k m).support, S.dec k c = some m

/-- Every CSLib perfect-secrecy `EncScheme` (Katz and Lindell, Definition 2.1) is a
`SymmEncScheme` whose decryption never fails. -/
def ofEncScheme (E : Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme M K C) :
    SymmEncScheme M K C where
  gen := E.gen
  enc := E.enc
  dec k c := some (E.dec k c)

/-- The embedding of an `EncScheme` is correct, by the correctness field of `EncScheme`. -/
theorem correct_ofEncScheme (E : Cslib.Crypto.Protocols.PerfectSecrecy.EncScheme M K C) :
    (ofEncScheme E).Correct := fun k hk m c hc =>
  congrArg some (E.correct k hk m c hc)

end SymmEncScheme

/-- A chosen-plaintext adversary against a private-key scheme (Katz and Lindell,
Definition 3.22): with coins `r ← coins`, the first stage `run r` has access to the encryption
oracle and outputs two challenge messages and the second stage, which receives the challenge
ciphertext, again has oracle access, and outputs a guess. -/
structure CPAAdversary (M C R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The two stages, as a function of the coins. -/
  run : R → OracleComp M C ((M × M) × (C → OracleComp M C Bool))

/-- The CPA adversary makes at most `q` encryption queries in total, over both stages, along
every path. With `q = 0` this is an eavesdropper (Katz and Lindell, Definition 3.8). -/
def CPAAdversary.QueryBounded {M C R : Type*} (q : ℕ) (A : CPAAdversary M C R) : Prop :=
  ∀ r, IsQueryBoundedWith (fun out j => ∀ c, IsQueryBounded j (out.2 c)) q (A.run r)

section CPA

variable {M K C R : Type*}

/-- The left-or-right CPA experiment with challenge bit `b`: `k ← Gen`, the adversary runs with
oracle `Enc_k`, the challenge is `Enc_k(m_b)`, and the experiment outputs the adversary's guess. -/
noncomputable def cpaExp (S : SymmEncScheme M K C) (A : CPAAdversary M C R) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun k => A.coins.bind fun r =>
    (evalPMF (S.enc k) (A.run r)).bind fun out =>
      (S.enc k (pick out.1 b)).bind fun c => evalPMF (S.enc k) (out.2 c)

/-- **`PrivK^cpa`** (Katz and Lindell, Definition 3.22): a uniform challenge bit, and the
experiment outputs `1` when the adversary guesses it. -/
noncomputable def cpaGame (S : SymmEncScheme M K C) (A : CPAAdversary M C R) : PMF Bool :=
  bitGame (cpaExp S A)

/-- The CPA advantage `|Pr[PrivK^cpa = 1] - 1/2|`. -/
noncomputable def cpaAdvantage (S : SymmEncScheme M K C) (A : CPAAdversary M C R) : ℝ :=
  guessAdvantage (cpaGame S A)

/-- The CPA advantage is half the distinguishing advantage between the two challenge bits. -/
theorem cpaAdvantage_eq (S : SymmEncScheme M K C) (A : CPAAdversary M C R) :
    cpaAdvantage S A = advantage (cpaExp S A true) (cpaExp S A false) / 2 :=
  guessAdvantage_bitGame _

end CPA

/-- The oracle interface of a CCA adversary: a query `.inl m` asks for an encryption of `m`
(answered in `C`), a query `.inr c` asks for the decryption of `c` (answered in `Option M`). -/
abbrev CCASig (M C : Type u) : PFunctor.{u, u} := ⟨M ⊕ C, Sum.elim (fun _ => C) (fun _ => Option M)⟩

/-- A chosen-ciphertext adversary against a private-key scheme (Katz and Lindell,
Definition 3.33): like `CPAAdversary`, with a decryption oracle besides the encryption oracle. -/
structure CCAAdversary (M C R : Type u) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The two stages, as a function of the coins. -/
  run : R → (CCASig M C).FreeM ((M × M) × (C → (CCASig M C).FreeM Bool))

/-- The CCA adversary makes at most `q` oracle queries (encryption and decryption together). -/
def CCAAdversary.QueryBounded {M C R : Type u} (q : ℕ) (A : CCAAdversary M C R) : Prop :=
  ∀ r, IsQueryBoundedWith (fun out j => ∀ c, IsQueryBounded j (out.2 c)) q (A.run r)

section CCA

variable {M K C R : Type u} [DecidableEq C]

/-- The CCA oracles for the key `k`: encryption, and decryption that answers `⊥` on the
challenge ciphertext `ch` (if any). -/
noncomputable def ccaOracle (S : SymmEncScheme M K C) (k : K) (ch : Option C) :
    (a : M ⊕ C) → PMF ((CCASig M C).B a)
  | .inl m => S.enc k m
  | .inr c => PMF.pure (if ch = some c then none else S.dec k c)

/-- The left-or-right CCA experiment with challenge bit `b`. -/
noncomputable def ccaExp (S : SymmEncScheme M K C) (A : CCAAdversary M C R) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun k => A.coins.bind fun r =>
    (evalPMF (ccaOracle S k none) (A.run r)).bind fun out =>
      (S.enc k (pick out.1 b)).bind fun c => evalPMF (ccaOracle S k (some c)) (out.2 c)

/-- **`PrivK^cca`** (Katz and Lindell, Definition 3.33). -/
noncomputable def ccaGame (S : SymmEncScheme M K C) (A : CCAAdversary M C R) : PMF Bool :=
  bitGame (ccaExp S A)

/-- The CCA advantage `|Pr[PrivK^cca = 1] - 1/2|`. -/
noncomputable def ccaAdvantage (S : SymmEncScheme M K C) (A : CCAAdversary M C R) : ℝ :=
  guessAdvantage (ccaGame S A)

/-- The CCA advantage is half the distinguishing advantage between the two challenge bits. -/
theorem ccaAdvantage_eq (S : SymmEncScheme M K C) (A : CCAAdversary M C R) :
    ccaAdvantage S A = advantage (ccaExp S A true) (ccaExp S A false) / 2 :=
  guessAdvantage_bitGame _

end CCA

/-- A ciphertext forger against a private-key scheme: with coins `r ← coins` and access to the
encryption oracle, it outputs a ciphertext. -/
structure CtxtForger (M C R : Type*) where
  /-- The distribution of the forger's coins. -/
  coins : PMF R
  /-- The forger, as a function of its coins. -/
  forge : R → OracleComp M C C

/-- The ciphertext forger makes at most `q` encryption queries. -/
def CtxtForger.QueryBounded {M C R : Type*} (q : ℕ) (A : CtxtForger M C R) : Prop :=
  ∀ r, IsQueryBounded q (A.forge r)

section Ctxt

variable {M K C R : Type*} [DecidableEq C]

/-- **Ciphertext integrity** (`INT-CTXT`; Bellare and Namprempre; the ciphertext form of Katz
and Lindell's unforgeable encryption, Section 4.5): `k ← Gen`, the forger runs with oracle
`Enc_k` and outputs `c`; it wins when `Dec_k(c) ≠ ⊥` and `c` was never an oracle answer. -/
noncomputable def ctxtGame (S : SymmEncScheme M K C) (A : CtxtForger M C R) : PMF Bool :=
  S.gen.bind fun k => A.coins.bind fun r =>
    (evalLog (S.enc k) (A.forge r)).map fun p =>
      (S.dec k p.1).isSome && decide (p.1 ∉ p.2.map Prod.snd)

/-- The ciphertext-forgery advantage `Pr[INT-CTXT = 1]`. -/
noncomputable def ctxtAdvantage (S : SymmEncScheme M K C) (A : CtxtForger M C R) : ℝ :=
  winProb (ctxtGame S A)

end Ctxt

/-! ### Public-key encryption -/

/-- A public-key encryption scheme (Katz and Lindell, Definition 11.1). -/
structure PKEScheme (M PK SK C : Type*) where
  /-- Key generation, producing a public key and a secret key. -/
  gen : PMF (PK × SK)
  /-- Probabilistic encryption under the public key. -/
  enc : PK → M → PMF C
  /-- Deterministic decryption with the secret key, with `none` for `⊥`. -/
  dec : SK → C → Option M

/-- **Correctness** of a public-key scheme (Katz and Lindell, Definition 11.1, with perfect
correctness). -/
def PKEScheme.Correct {M PK SK C : Type*} (S : PKEScheme M PK SK C) : Prop :=
  ∀ kp ∈ S.gen.support, ∀ m, ∀ c ∈ (S.enc kp.1 m).support, S.dec kp.2 c = some m

/-- A chosen-plaintext (equivalently, eavesdropping) adversary against a public-key scheme: from
the public key it chooses two messages, and from the public key and the challenge ciphertext it
guesses. The shape of `Cslib.Crypto.PublicKey.ElGamal.Adversary`, with an arbitrary coin
distribution. -/
structure PubCPAAdversary (M PK C R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The two challenge messages. -/
  choose : PK → R → M × M
  /-- The guess of the challenge bit. -/
  guess : PK → C → R → Bool

section PubCPA

variable {M PK SK C R : Type*}

/-- The left-or-right public-key experiment with challenge bit `b`. -/
noncomputable def pubCpaExp (S : PKEScheme M PK SK C) (A : PubCPAAdversary M PK C R) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun kp => A.coins.bind fun r =>
    (S.enc kp.1 (pick (A.choose kp.1 r) b)).map fun c => A.guess kp.1 c r

/-- **`PubK^eav`** (Katz and Lindell, Definition 11.2), which for public-key schemes is
equivalent to CPA security (Proposition 11.3). -/
noncomputable def pubCpaGame (S : PKEScheme M PK SK C) (A : PubCPAAdversary M PK C R) :
    PMF Bool :=
  bitGame (pubCpaExp S A)

/-- The public-key CPA advantage `|Pr[PubK^eav = 1] - 1/2|`. -/
noncomputable def pubCpaAdvantage (S : PKEScheme M PK SK C) (A : PubCPAAdversary M PK C R) : ℝ :=
  guessAdvantage (pubCpaGame S A)

theorem pubCpaAdvantage_eq (S : PKEScheme M PK SK C) (A : PubCPAAdversary M PK C R) :
    pubCpaAdvantage S A = advantage (pubCpaExp S A true) (pubCpaExp S A false) / 2 :=
  guessAdvantage_bitGame _

end PubCPA

/-- A chosen-plaintext adversary against a public-key scheme **with an encryption oracle**
(Katz and Lindell, Section 11.2.2): with coins `r ← coins`, the first stage sees the public key
and has access to `Enc_pk(·)`, and outputs two challenge messages and the second stage, which
receives the challenge ciphertext and again has oracle access. -/
structure PubOracleCPAAdversary (M PK C R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The two stages, as a function of the public key and the coins. -/
  run : PK → R → OracleComp M C ((M × M) × (C → OracleComp M C Bool))

/-- The adversary makes at most `n` encryption queries in total, over both stages, along every
path. -/
def PubOracleCPAAdversary.QueryBounded {M PK C R : Type*} (n : ℕ)
    (A : PubOracleCPAAdversary M PK C R) : Prop :=
  ∀ pk r, IsQueryBoundedWith (fun out j => ∀ c, IsQueryBounded j (out.2 c)) n (A.run pk r)

section PubOracleCPA

open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_prod)

variable {M PK SK C R : Type*}

/-- The left-or-right public-key CPA experiment with challenge bit `b`: `(pk, sk) ← Gen`, the
adversary runs with `pk` and the oracle `Enc_pk`, the challenge is `Enc_pk(m_b)`. -/
noncomputable def pubOracleCpaExp (S : PKEScheme M PK SK C) (A : PubOracleCPAAdversary M PK C R)
    (b : Bool) : PMF Bool :=
  S.gen.bind fun kp => A.coins.bind fun r =>
    (evalPMF (S.enc kp.1) (A.run kp.1 r)).bind fun out =>
      (S.enc kp.1 (pick out.1 b)).bind fun c => evalPMF (S.enc kp.1) (out.2 c)

/-- **`PubK^cpa`** (Katz and Lindell, Section 11.2.2): a uniform challenge bit, and the
experiment outputs `1` when the adversary guesses it. -/
noncomputable def pubOracleCpaGame (S : PKEScheme M PK SK C)
    (A : PubOracleCPAAdversary M PK C R) : PMF Bool :=
  bitGame (pubOracleCpaExp S A)

/-- The public-key CPA advantage `|Pr[PubK^cpa = 1] - 1/2|`. -/
noncomputable def pubOracleCpaAdvantage (S : PKEScheme M PK SK C)
    (A : PubOracleCPAAdversary M PK C R) : ℝ :=
  guessAdvantage (pubOracleCpaGame S A)

variable {Rnd : Type*} [Fintype Rnd] [Nonempty Rnd] [Inhabited Rnd]

/-- The eavesdropper that runs a CPA adversary and simulates its encryption oracle from the
public key (Katz and Lindell, proof of Proposition 11.3): it samples `n` encryption coins for each
stage and answers the `i`-th query `m` of a stage with `encR pk m ρᵢ`. -/
noncomputable def PubOracleCPAAdversary.toEav (A : PubOracleCPAAdversary M PK C R)
    (encR : PK → M → Rnd → C) (n : ℕ) :
    PubCPAAdversary M PK C (R × (Fin n → Rnd) × (Fin n → Rnd)) where
  coins := A.coins.bind fun r => (uniformOfFintype ((Fin n → Rnd) × (Fin n → Rnd))).map (r, ·)
  choose pk ω := (runCoins (encR pk) (A.run pk ω.1) (List.ofFn ω.2.1)).1
  guess pk c ω := runCoins (encR pk) ((runCoins (encR pk) (A.run pk ω.1) (List.ofFn ω.2.1)).2 c)
    (List.ofFn ω.2.2)

/-- The simulating eavesdropper has uniform coins whenever the CPA adversary does. -/
theorem PubOracleCPAAdversary.toEav_coins_uniform [Fintype R] [Nonempty R]
    (A : PubOracleCPAAdversary M PK C R) (hA : A.coins = uniformOfFintype R)
    (encR : PK → M → Rnd → C) (n : ℕ) :
    (A.toEav encR n).coins = uniformOfFintype (R × (Fin n → Rnd) × (Fin n → Rnd)) := by
  rw [PubOracleCPAAdversary.toEav, hA]
  exact uniformOfFintype_prod _ _

/-- The two experiments agree for each challenge bit. -/
theorem pubCpaExp_toEav (S : PKEScheme M PK SK C) (encR : PK → M → Rnd → C)
    (hS : ∀ pk m, S.enc pk m = (uniformOfFintype Rnd).map (encR pk m))
    {n : ℕ} (A : PubOracleCPAAdversary M PK C R) (hA : A.QueryBounded n) (b : Bool) :
    pubCpaExp S (A.toEav encR n) b = pubOracleCpaExp S A b := by
  have hS' : S.enc = fun pk m => (uniformOfFintype Rnd).map (encR pk m) :=
    funext fun pk => funext (hS pk)
  unfold pubCpaExp pubOracleCpaExp
  congr 1
  funext kp
  rw [PubOracleCPAAdversary.toEav, PMF.bind_bind]
  congr 1
  funext r
  rw [PMF.bind_map, ← uniformOfFintype_prod, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  -- the second stage: swap its presampled coins past the challenge encryption
  have stage2 : ∀ f₁ : Fin n → Rnd,
      ((uniformOfFintype (Fin n → Rnd)).bind fun f₂ =>
        (S.enc kp.1 (pick (runCoins (encR kp.1) (A.run kp.1 r) (List.ofFn f₁)).1 b)).map
          fun c => runCoins (encR kp.1)
            ((runCoins (encR kp.1) (A.run kp.1 r) (List.ofFn f₁)).2 c) (List.ofFn f₂)) =
      (S.enc kp.1 (pick (runCoins (encR kp.1) (A.run kp.1 r) (List.ofFn f₁)).1 b)).bind fun c =>
        evalPMF (S.enc kp.1) ((runCoins (encR kp.1) (A.run kp.1 r) (List.ofFn f₁)).2 c) := by
    intro f₁
    obtain ⟨j, hj, hcont⟩ := exists_cont_runCoins (encR kp.1) (hA kp.1 r) (List.ofFn f₁)
    simp only [PMF.map, Function.comp_def]
    rw [PMF.bind_comm]
    congr 1
    funext c
    rw [hS']
    rw [← map_runCoins (encR kp.1) ((hcont c).mono hj)]
    rfl
  simp only [stage2]
  -- the first stage
  have stage1 := map_runCoins (encR kp.1)
    ((hA kp.1 r).mono (cont' := fun _ _ => True) fun _ _ _ => trivial)
  have hO : S.enc kp.1 = fun x => (uniformOfFintype Rnd).map (encR kp.1 x) := funext (hS kp.1)
  rw [← hO] at stage1
  rw [← stage1, PMF.bind_map]
  rfl

/-- **Eavesdropping security implies CPA security for public-key encryption** (Katz and Lindell,
Proposition 11.3), as an exact equality: for a scheme with encryption `Enc_pk(m) = encR pk m ρ`
for uniform `ρ`, a CPA adversary making at most `n` encryption queries has exactly the advantage of
the eavesdropper `A.toEav encR n` that simulates its oracle. -/
theorem pubCpaAdvantage_toEav (S : PKEScheme M PK SK C) (encR : PK → M → Rnd → C)
    (hS : ∀ pk m, S.enc pk m = (uniformOfFintype Rnd).map (encR pk m))
    {n : ℕ} (A : PubOracleCPAAdversary M PK C R) (hA : A.QueryBounded n) :
    pubCpaAdvantage S (A.toEav encR n) = pubOracleCpaAdvantage S A := by
  unfold pubCpaAdvantage pubOracleCpaAdvantage pubCpaGame pubOracleCpaGame
  congr 2
  funext b
  exact pubCpaExp_toEav S encR hS A hA b

/-- Any bound on eavesdropping advantages bounds the CPA advantage. -/
theorem pubOracleCpaAdvantage_le (S : PKEScheme M PK SK C) (encR : PK → M → Rnd → C)
    (hS : ∀ pk m, S.enc pk m = (uniformOfFintype Rnd).map (encR pk m))
    {n : ℕ} (A : PubOracleCPAAdversary M PK C R) (hA : A.QueryBounded n) {ε : ℝ}
    (hε : pubCpaAdvantage S (A.toEav encR n) ≤ ε) : pubOracleCpaAdvantage S A ≤ ε :=
  (pubCpaAdvantage_toEav S encR hS A hA).symm.le.trans hε

end PubOracleCPA

/-- A chosen-ciphertext adversary against a public-key scheme (Katz and Lindell,
Definition 11.8): both stages see the public key and have a decryption oracle. -/
structure PubCCAAdversary (M PK C R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The two stages, as a function of the public key and the coins. -/
  run : PK → R → OracleComp C (Option M) ((M × M) × (C → OracleComp C (Option M) Bool))

/-- The public-key CCA adversary makes at most `q` decryption queries. -/
def PubCCAAdversary.QueryBounded {M PK C R : Type*} (q : ℕ) (A : PubCCAAdversary M PK C R) :
    Prop :=
  ∀ pk r, IsQueryBoundedWith (fun out j => ∀ c, IsQueryBounded j (out.2 c)) q (A.run pk r)

section PubCCA

variable {M PK SK C R : Type*} [DecidableEq C]

/-- The decryption oracle with secret key `sk`, answering `⊥` on the challenge `ch` (if any). -/
noncomputable def pubDecOracle (S : PKEScheme M PK SK C) (sk : SK) (ch : Option C) :
    C → PMF (Option M) :=
  fun c => PMF.pure (if ch = some c then none else S.dec sk c)

/-- The left-or-right public-key CCA experiment with challenge bit `b`. -/
noncomputable def pubCcaExp (S : PKEScheme M PK SK C) (A : PubCCAAdversary M PK C R) (b : Bool) :
    PMF Bool :=
  S.gen.bind fun kp => A.coins.bind fun r =>
    (evalPMF (pubDecOracle S kp.2 none) (A.run kp.1 r)).bind fun out =>
      (S.enc kp.1 (pick out.1 b)).bind fun c => evalPMF (pubDecOracle S kp.2 (some c)) (out.2 c)

/-- **`PubK^cca`** (Katz and Lindell, Definition 11.8). -/
noncomputable def pubCcaGame (S : PKEScheme M PK SK C) (A : PubCCAAdversary M PK C R) :
    PMF Bool :=
  bitGame (pubCcaExp S A)

/-- The public-key CCA advantage `|Pr[PubK^cca = 1] - 1/2|`. -/
noncomputable def pubCcaAdvantage (S : PKEScheme M PK SK C) (A : PubCCAAdversary M PK C R) : ℝ :=
  guessAdvantage (pubCcaGame S A)

theorem pubCcaAdvantage_eq (S : PKEScheme M PK SK C) (A : PubCCAAdversary M PK C R) :
    pubCcaAdvantage S A = advantage (pubCcaExp S A true) (pubCcaExp S A false) / 2 :=
  guessAdvantage_bitGame _

end PubCCA

/-! ### Message authentication codes -/

/-- A message authentication code (Katz and Lindell, Definition 4.1). -/
structure MACScheme (M K T : Type*) where
  /-- Key generation. -/
  gen : PMF K
  /-- Probabilistic tagging `Mac_k(m)`. -/
  tag : K → M → PMF T
  /-- Deterministic verification `Vrfy_k(m, t)`. -/
  verify : K → M → T → Bool

/-- **Correctness** of a MAC (Katz and Lindell, Definition 4.1): honest tags verify. -/
def MACScheme.Correct {M K T : Type*} (S : MACScheme M K T) : Prop :=
  ∀ k ∈ S.gen.support, ∀ m, ∀ t ∈ (S.tag k m).support, S.verify k m t = true

/-- A forger against a MAC: with coins `r ← coins` it has access to the tagging oracle and
outputs a message and a tag. -/
structure MACForger (M T R : Type*) where
  /-- The distribution of the forger's random coins. -/
  coins : PMF R
  /-- The forger, as a function of its coins. -/
  forge : R → OracleComp M T (M × T)

/-- The forger makes at most `q` tagging queries. -/
def MACForger.QueryBounded {M T R : Type*} (q : ℕ) (A : MACForger M T R) : Prop :=
  ∀ r, IsQueryBounded q (A.forge r)

section MAC

variable {M K T R : Type*} [DecidableEq M]

/-- **`Mac-forge`** (Katz and Lindell, Definition 4.2): `k ← Gen`, the forger runs with oracle
`Mac_k` and outputs `(m, t)`; the experiment outputs `1` when `Vrfy_k(m, t) = 1` and `m` was never
queried. -/
noncomputable def macGame (S : MACScheme M K T) (A : MACForger M T R) : PMF Bool :=
  S.gen.bind fun k => A.coins.bind fun r =>
    (evalLog (S.tag k) (A.forge r)).map fun p =>
      S.verify k p.1.1 p.1.2 && decide (p.1.1 ∉ p.2.map Prod.fst)

/-- The forgery advantage `Pr[Mac-forge = 1]`. -/
noncomputable def macAdvantage (S : MACScheme M K T) (A : MACForger M T R) : ℝ :=
  winProb (macGame S A)

/-- The strong forgery experiment (Katz and Lindell, Definition 4.3): the forgery wins when it
verifies and the pair `(m, t)` was never an oracle query with its answer. -/
noncomputable def macStrongGame [DecidableEq T] (S : MACScheme M K T) (A : MACForger M T R) :
    PMF Bool :=
  S.gen.bind fun k => A.coins.bind fun r =>
    (evalLog (S.tag k) (A.forge r)).map fun p =>
      S.verify k p.1.1 p.1.2 && decide (p.1 ∉ p.2)

end MAC

/-! ### Digital signatures -/

/-- A signature scheme (Katz and Lindell, Definition 12.1). -/
structure SigScheme (M PK SK S : Type*) where
  /-- Key generation, producing a public key and a secret key. -/
  gen : PMF (PK × SK)
  /-- Probabilistic signing with the secret key. -/
  sign : SK → M → PMF S
  /-- Deterministic verification with the public key. -/
  verify : PK → M → S → Bool

/-- **Correctness** of a signature scheme (Katz and Lindell, Definition 12.1): honest signatures
verify. -/
def SigScheme.Correct {M PK SK S : Type*} (Sg : SigScheme M PK SK S) : Prop :=
  ∀ kp ∈ Sg.gen.support, ∀ m, ∀ σ ∈ (Sg.sign kp.2 m).support, Sg.verify kp.1 m σ = true

/-- A forger against a signature scheme: from the public key and its coins, with access to the
signing oracle, it outputs a message and a signature. -/
structure SigForger (M PK S R : Type*) where
  /-- The distribution of the forger's random coins. -/
  coins : PMF R
  /-- The forger, as a function of the public key and its coins. -/
  forge : PK → R → OracleComp M S (M × S)

/-- The forger makes at most `q` signing queries. With `q = 1` this is the one-time setting of
Katz and Lindell, Section 12.6.1 (Lamport). -/
def SigForger.QueryBounded {M PK S R : Type*} (q : ℕ) (A : SigForger M PK S R) : Prop :=
  ∀ pk r, IsQueryBounded q (A.forge pk r)

section Sig

variable {M PK SK S R : Type*} [DecidableEq M]

/-- **`Sig-forge`** (Katz and Lindell, Definition 12.2): `(pk, sk) ← Gen`, the forger gets `pk`
and the oracle `Sign_sk` and outputs `(m, σ)`; the experiment outputs `1` when
`Vrfy_pk(m, σ) = 1` and `m` was never queried. -/
noncomputable def sigGame (Sg : SigScheme M PK SK S) (A : SigForger M PK S R) : PMF Bool :=
  Sg.gen.bind fun kp => A.coins.bind fun r =>
    (evalLog (Sg.sign kp.2) (A.forge kp.1 r)).map fun p =>
      Sg.verify kp.1 p.1.1 p.1.2 && decide (p.1.1 ∉ p.2.map Prod.fst)

/-- The forgery advantage `Pr[Sig-forge = 1]`. -/
noncomputable def sigAdvantage (Sg : SigScheme M PK SK S) (A : SigForger M PK S R) : ℝ :=
  winProb (sigGame Sg A)

end Sig

end Cslib.Crypto.Framework
