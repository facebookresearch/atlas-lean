/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic

/-!
# Pseudorandom generators and the stream cipher

A **pseudorandom generator** (Katz and Lindell, Definition 3.14) is a deterministic map
`G : S → Y` from seeds to longer strings such that no distinguisher tells `G s`, for a uniform
seed `s`, from a uniform `y : Y`.

* `Distinguisher Y R`: coins `coins : PMF R` and a guess `guess : Y → R → Bool`, the
  adversary shape of the framework (`CSLibExt.Crypto.Framework.Games`).
* `prgReal G D`, `prgRand D : PMF Bool` are the two worlds and `prgAdvantage G D` is the
  framework's distinguishing advantage between them.
* `PRGExpanding G`: expansion, `|S n| < |Y n|` for every `n` (Katz and Lindell's `ℓ(n) > n`
  for seeds of length `n` and outputs of length `ℓ(n)`).
* `PRGIndistinguishable G R Admissible`: the indistinguishability condition alone, asymptotic
  security against an admissible class of distinguisher families (`AsymptoticallySecure`).
* `PRGSecure G R Admissible`: the conjunction of expansion and indistinguishability. Without
  expansion the identity family would qualify (its advantage is `0`), although it does not
  stretch its seed; `not_prgSecure_of_card_le` rules out every family that fails to expand at
  some `n`.

**Relative to the admissible class; efficiency is not modelled.** `PRGIndistinguishable` and
`PRGSecure` are abstract relative-indistinguishability predicates, not Definition 3.14 verbatim.
The source conditions they omit:

* `G` is computed by a **deterministic polynomial-time** algorithm;
* the output length `ℓ(n)` is a **polynomial** (only `ℓ(n) > n` is kept, as `PRGExpanding`, by
  cardinality);
* the distinguishers are **probabilistic polynomial-time**.

The first two constrain `G` and are not imposed at all, so a noncomputable family, or one with
superpolynomial stretch, can satisfy `PRGSecure`. The third is whatever the caller's
`Admissible` encodes: the framework has no polynomial-time model for these adversaries (see
"What is deferred" in `CSLibExt.Crypto.Framework.Asymptotic`).

**The stream cipher** (Katz and Lindell, Construction 3.17). Over an additive group of messages
(bit strings under XOR are one), `streamCipher G` encrypts `m` under the seed `k` as `G k + m`:
the keystream `G k` used as a one-time pad. `streamCipher_correct` is correctness.

* `cpaAdvantage_streamCipher_eq` (Katz and Lindell, Theorem 3.18, as an exact **equality**):
  for every eavesdropper `A` (a CPA adversary making no queries, `CPAAdversary.QueryBounded 0`,
  which is the experiment `PrivK^eav` of Definition 3.8), the advantage of `A` against the stream
  cipher equals the PRG advantage of the explicit reduction `cpaReduction A`. The reduction runs
  `A` with the challenge `y + m_b`; with `y = G k` this is the real experiment
  (`cpaGame_streamCipher_eq_prgReal`, for every adversary), and with a uniform `y` the challenge
  is a one-time pad, so the reduction outputs `1` with probability exactly `1/2`
  (`prgRand_cpaReduction`).
* `eavSecure_streamCipher`: the asymptotic form. If the PRG family is indistinguishable
  (`PRGIndistinguishable`) against a class of distinguishers containing the reductions, the
  stream cipher is secure against the corresponding class of eavesdroppers. Expansion is not a
  hypothesis: it is what makes the key shorter than the message, not what makes the scheme
  secure, so the theorem also covers the one-time pad (the identity family).
  `eavSecure_streamCipher_of_prgSecure` is the source-shaped corollary from `PRGSecure`.

**The stream cipher is not CPA-secure.** Encryption is deterministic, and no deterministic
scheme is CPA-secure (Katz and Lindell, Section 3.4.2): `cpaAdvantage_replayAttack` exhibits an
adversary that asks for the encryption of `m₀` once and then wins the CPA game with probability
`1` (advantage `1/2`, the maximum), for **every** generator `G`, and
`not_polyQueryCPASecure_streamCipher` concludes that no stream cipher family over a nontrivial
message group is `PolyQueryCPASecure`. So "CPA security from PRG security" is false for this
construction; the CPA-secure constructions randomize encryption with a fresh value (Katz and
Lindell, Construction 3.30, formalized from a PRF in `CSLibExt.Crypto.SymmetricKey.PRF`).

Wave 2: migrate to Framework. The PRG game is not part of `CSLibExt.Crypto.Framework`; it is
defined here in the framework's style (coins as a `PMF`, games as `PMF Bool`, advantages as
`advantage`) so that moving it there is a rename.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.3 and 3.4 (Definitions 3.8, 3.14, 3.22, Construction 3.17, Theorem 3.18).
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.Crypto.Framework FreeM OracleComp

/-! ### The PRG game -/

/-- A distinguisher for a pseudorandom generator with outputs in `Y`: random coins and a guess
from the challenge string and the coins (Katz and Lindell, Definition 3.14). -/
structure Distinguisher (Y R : Type*) where
  /-- The distribution of the distinguisher's random coins. -/
  coins : PMF R
  /-- The guess: `true` for "pseudorandom". -/
  guess : Y → R → Bool

section Game

variable {S Y R : Type*} [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y]

/-- The real world of the PRG experiment: the distinguisher sees `G s` for a uniform seed `s`
(Katz and Lindell, Definition 3.14). -/
noncomputable def prgReal (G : S → Y) (D : Distinguisher Y R) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype S).bind fun s => D.coins.map (D.guess (G s))

/-- The random world of the PRG experiment: the distinguisher sees a uniform `y : Y`. -/
noncomputable def prgRand (D : Distinguisher Y R) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype Y).bind fun y => D.coins.map (D.guess y)

/-- The PRG advantage `|Pr[D(G(s)) = 1] - Pr[D(y) = 1]|` (Katz and Lindell, Definition 3.14). -/
noncomputable def prgAdvantage (G : S → Y) (D : Distinguisher Y R) : ℝ :=
  advantage (prgReal G D) (prgRand D)

end Game

/-- **Expansion** of a family `G n : S n → Y n`: at every security parameter there are fewer
seeds than outputs (Katz and Lindell, Definition 3.14, `ℓ(n) > n`, stated by cardinality so that
it applies to any finite seed and output types). -/
@[nolint unusedArguments]
def PRGExpanding {S Y : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Fintype (Y n)]
    (_G : (n : ℕ) → S n → Y n) : Prop :=
  ∀ n, Fintype.card (S n) < Fintype.card (Y n)

/-- **Indistinguishability relative to `Admissible`** of a family `G n : S n → Y n`: every
admissible family of distinguishers has negligible `prgAdvantage` (the pseudorandomness condition
of Katz and Lindell, Definition 3.14, with the class of admissible distinguishers as a parameter,
as for `PubCPASecure`). The coin types must be nonempty, or there would be no distinguishers.

This is an abstract relative-indistinguishability predicate: Definition 3.14 also requires `G` to
be deterministic polynomial-time computable and the distinguishers to be probabilistic
polynomial-time. Nothing here constrains how `G` is computed, and the restriction on
distinguishers is whatever `Admissible` encodes. -/
@[nolint unusedArguments]
def PRGIndistinguishable {S Y : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)] (G : (n : ℕ) → S n → Y n) (R : ℕ → Type*)
    [∀ n, Nonempty (R n)] (Admissible : ((n : ℕ) → Distinguisher (Y n) (R n)) → Prop) : Prop :=
  AsymptoticallySecure (fun n D => prgAdvantage (G n) D) Admissible

/-- **Asymptotic PRG security relative to `Admissible`** of a family `G n : S n → Y n`: the
family expands (`PRGExpanding`) and is indistinguishable from uniform against every admissible
family of distinguishers (`PRGIndistinguishable`).

This is the part of Katz and Lindell, Definition 3.14, expressible without a complexity model,
not the definition verbatim. Omitted source conditions: `G` deterministic polynomial-time
computable, output length `ℓ(n)` polynomial, distinguishers probabilistic polynomial-time. The
first two are not imposed, so a noncomputable family can satisfy `PRGSecure`; the third must be
supplied through `Admissible`. -/
def PRGSecure {S Y : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)] [∀ n, Fintype (Y n)]
    [∀ n, Nonempty (Y n)] (G : (n : ℕ) → S n → Y n) (R : ℕ → Type*) [∀ n, Nonempty (R n)]
    (Admissible : ((n : ℕ) → Distinguisher (Y n) (R n)) → Prop) : Prop :=
  PRGExpanding G ∧ PRGIndistinguishable G R Admissible

/-- A family that does not expand at some security parameter is not a PRG, whatever its
advantage (Katz and Lindell, Definition 3.14). In particular the identity family, which has
advantage `0` against every distinguisher, is not a PRG. -/
theorem not_prgSecure_of_card_le {S Y : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)] {G : (n : ℕ) → S n → Y n} {R : ℕ → Type*}
    [∀ n, Nonempty (R n)] {Admissible : ((n : ℕ) → Distinguisher (Y n) (R n)) → Prop} {n : ℕ}
    (h : Fintype.card (Y n) ≤ Fintype.card (S n)) : ¬ PRGSecure G R Admissible :=
  fun hG => (hG.1 n).not_ge h

/-! ### The stream cipher -/

section StreamCipher

variable {S Y R : Type*} [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] [AddCommGroup Y]

/-- **The stream cipher** from a PRG (Katz and Lindell, Construction 3.17, over an additive group
of messages): the key is a uniform seed `k`, `Enc_k(m) = G k + m` and `Dec_k(c) = c - G k`. -/
noncomputable def streamCipher (G : S → Y) : SymmEncScheme Y S Y where
  gen := Cslib.Probability.PMF.uniformOfFintype S
  enc k m := PMF.pure (G k + m)
  dec k c := some (c - G k)

omit [Fintype Y] [Nonempty Y] in
/-- **Correctness** of the stream cipher. -/
theorem streamCipher_correct (G : S → Y) : (streamCipher G).Correct := by
  intro k _ m c hc
  simp only [streamCipher, PMF.support_pure, Set.mem_singleton_iff] at hc
  simp [streamCipher, hc]

omit [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] in
/-- The CPA experiment against the stream cipher, run deterministically with keystream `y`:
oracle queries `m` are answered with `y + m`, and the challenge is `y + m_b`. -/
def expRun (A : CPAAdversary Y Y R) (y : Y) (b : Bool) (r : R) : Bool :=
  (((A.run r).run (y + ·)).2 (y + pick ((A.run r).run (y + ·)).1 b)).run (y + ·)

/-- The PRG distinguisher built from a CPA adversary against the stream cipher: with coins
`(b, r)` it runs the adversary with keystream `y` (the challenge string) and challenge bit `b`,
and outputs whether the adversary guessed `b`. -/
noncomputable def cpaReduction (A : CPAAdversary Y Y R) : Distinguisher Y (Bool × R) where
  coins := fairCoin.bind fun b => A.coins.map fun r => (b, r)
  guess y br := expRun A y br.1 br.2 == br.1

omit [Fintype Y] [Nonempty Y] in
/-- The left-or-right CPA experiment against the stream cipher, in closed form. -/
theorem cpaExp_streamCipher (G : S → Y) (A : CPAAdversary Y Y R) (b : Bool) :
    cpaExp (streamCipher G) A b =
      (Cslib.Probability.PMF.uniformOfFintype S).bind fun k => A.coins.map (expRun A (G k) b) := by
  simp only [cpaExp, streamCipher]
  refine congrArg _ (funext fun k => ?_)
  rw [PMF.map]
  refine congrArg _ (funext fun r => ?_)
  rw [OracleComp.evalPMF_pure_comp (fun m => G k + m), PMF.pure_bind, PMF.pure_bind,
    OracleComp.evalPMF_pure_comp (fun m => G k + m)]
  rfl

omit [Fintype Y] [Nonempty Y] in
/-- **The real world is the CPA game**: with keystream `G k`, the reduction runs the CPA
experiment against the stream cipher exactly, for every adversary. -/
theorem cpaGame_streamCipher_eq_prgReal (G : S → Y) (A : CPAAdversary Y Y R) :
    cpaGame (streamCipher G) A = prgReal G (cpaReduction A) := by
  simp only [cpaGame, bitGame, cpaExp_streamCipher, prgReal, cpaReduction, PMF.map_bind,
    PMF.map_comp]
  rw [PMF.bind_comm]
  rfl

omit [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] [AddCommGroup Y] in
/-- A computation that asks no queries has the same run against every oracle. -/
private theorem run_eq_of_isQueryBoundedWith_zero {X Z α : Type*} {cont : α → ℕ → Prop}
    {c : OracleComp X Z α} (hc : IsQueryBoundedWith cont 0 c) (O O' : X → Z) :
    c.run O = c.run O' := by
  obtain ⟨x, rfl, -⟩ := eq_pure_of_isQueryBoundedWith_zero hc
  rfl

omit [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] in
/-- An eavesdropper's run depends on the keystream only through the challenge ciphertext. -/
private theorem expRun_of_queryBounded_zero {A : CPAAdversary Y Y R} (hA : A.QueryBounded 0)
    (r : R) : ∃ (m : Y × Y) (g : Y → Bool), ∀ y b, expRun A y b r = g (y + pick m b) := by
  obtain ⟨x, hx, hcont⟩ := eq_pure_of_isQueryBoundedWith_zero (hA r)
  refine ⟨x.1, fun c => (x.2 c).run (fun _ => 0), fun y b => ?_⟩
  simp only [expRun, hx]
  exact run_eq_of_isQueryBoundedWith_zero (hcont _) _ _

/-- A guess compared with a uniform bit is a uniform bit. -/
private theorem fairCoin_map_beq (c : Bool) : fairCoin.map (fun b => c == b) = fairCoin := by
  have h : (fun b => c == b) = (Equiv.ofBijective _ (show Function.Bijective
      (fun b => c == b) by cases c <;> decide) : Bool ≃ Bool) := rfl
  rw [h, fairCoin, Cslib.Probability.PMF.uniformOfFintype_map_equiv]

omit [Fintype S] [Nonempty S] in
/-- **The random world**: for an eavesdropper, the challenge `y + m_b` with uniform `y` is a
one-time pad, so the reduction outputs `1` with probability exactly `1/2`. -/
theorem prgRand_cpaReduction {A : CPAAdversary Y Y R} (hA : A.QueryBounded 0) :
    prgRand (cpaReduction A) = fairCoin := by
  choose m g hmg using expRun_of_queryBounded_zero hA
  have hshift : ∀ (c : Y) (h : Y → Bool),
      (Cslib.Probability.PMF.uniformOfFintype Y).map (fun y => h (y + c)) =
        (Cslib.Probability.PMF.uniformOfFintype Y).map h := by
    intro c h
    rw [show (fun y => h (y + c)) = h ∘ (Equiv.addRight c : Y ≃ Y) from rfl, ← PMF.map_comp,
      Cslib.Probability.PMF.uniformOfFintype_map_equiv]
  calc prgRand (cpaReduction A)
      = fairCoin.bind fun b => A.coins.bind fun r =>
          (Cslib.Probability.PMF.uniformOfFintype Y).map fun y => g r (y + pick (m r) b) == b := by
        simp only [prgRand, cpaReduction, PMF.map_bind, PMF.map_comp, hmg]
        rw [PMF.bind_comm]
        refine congrArg _ (funext fun b => ?_)
        simp only [PMF.map]
        rw [PMF.bind_comm]
        rfl
    _ = fairCoin.bind fun b => A.coins.bind fun r =>
          (Cslib.Probability.PMF.uniformOfFintype Y).map fun z => g r z == b := by
        exact congrArg _ (funext fun b => congrArg _ (funext fun r =>
          hshift _ (fun z => g r z == b)))
    _ = A.coins.bind fun r => (Cslib.Probability.PMF.uniformOfFintype Y).bind fun z =>
          fairCoin.map fun b => g r z == b := by
        simp only [PMF.map]
        rw [PMF.bind_comm]
        refine congrArg _ (funext fun r => ?_)
        rw [PMF.bind_comm]
        rfl
    _ = fairCoin := by simp only [fairCoin_map_beq, PMF.bind_const]

/-- **The stream cipher is eavesdropping-secure if the PRG is pseudorandom** (Katz and Lindell,
Theorem 3.18), as an exact equality: for every eavesdropper `A` (a CPA adversary making no
queries), its advantage against the stream cipher is the PRG advantage of `cpaReduction A`. -/
theorem cpaAdvantage_streamCipher_eq (G : S → Y) {A : CPAAdversary Y Y R}
    (hA : A.QueryBounded 0) :
    cpaAdvantage (streamCipher G) A = prgAdvantage G (cpaReduction A) := by
  rw [cpaAdvantage, guessAdvantage_eq_advantage_fairCoin, prgAdvantage,
    cpaGame_streamCipher_eq_prgReal, prgRand_cpaReduction hA]

/-- **Asymptotic eavesdropping security of the stream cipher** (Katz and Lindell,
Theorem 3.18): if the generator family is indistinguishable from uniform against a class `AdmD`
of distinguisher families containing the reductions of all admissible eavesdroppers, the stream
cipher family is secure against the admissible eavesdroppers. Expansion is not needed for
security, so it is not a hypothesis; `eavSecure_streamCipher_of_prgSecure` is the corollary from
`PRGSecure`. -/
theorem eavSecure_streamCipher {S Y R : ℕ → Type*} [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)] [∀ n, AddCommGroup (Y n)] [∀ n, Nonempty (R n)]
    (G : (n : ℕ) → S n → Y n)
    (AdmA : ((n : ℕ) → CPAAdversary (Y n) (Y n) (R n)) → Prop)
    (AdmD : ((n : ℕ) → Distinguisher (Y n) (Bool × R n)) → Prop)
    (h0 : ∀ A, AdmA A → ∀ n, (A n).QueryBounded 0)
    (hred : ∀ A, AdmA A → AdmD fun n => cpaReduction (A n))
    (hG : PRGIndistinguishable G (fun n => Bool × R n) AdmD) :
    AsymptoticallySecure (fun n A => cpaAdvantage (streamCipher (G n)) A) AdmA :=
  AsymptoticallySecure.of_reduction (fun A n => cpaReduction (A n)) hred negligibleAdv_zero
    (fun A hA n => by rw [cpaAdvantage_streamCipher_eq (G n) (h0 A hA n), add_zero]) hG

/-- **Asymptotic eavesdropping security of the stream cipher from a PRG** (Katz and Lindell,
Theorem 3.18, in the source's shape): `eavSecure_streamCipher` with the hypothesis that the
family is `PRGSecure`, of which only the indistinguishability half is used. -/
theorem eavSecure_streamCipher_of_prgSecure {S Y R : ℕ → Type*} [∀ n, Fintype (S n)]
    [∀ n, Nonempty (S n)] [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)] [∀ n, AddCommGroup (Y n)]
    [∀ n, Nonempty (R n)] (G : (n : ℕ) → S n → Y n)
    (AdmA : ((n : ℕ) → CPAAdversary (Y n) (Y n) (R n)) → Prop)
    (AdmD : ((n : ℕ) → Distinguisher (Y n) (Bool × R n)) → Prop)
    (h0 : ∀ A, AdmA A → ∀ n, (A n).QueryBounded 0)
    (hred : ∀ A, AdmA A → AdmD fun n => cpaReduction (A n))
    (hG : PRGSecure G (fun n => Bool × R n) AdmD) :
    AsymptoticallySecure (fun n A => cpaAdvantage (streamCipher (G n)) A) AdmA :=
  eavSecure_streamCipher G AdmA AdmD h0 hred hG.2

/-! ### The stream cipher is not CPA-secure -/

omit [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] [AddCommGroup Y] in
/-- **The replay attack** on deterministic encryption: ask for the encryption `c₀` of `m₀`,
challenge with `(m₀, m₁)` and guess `1` exactly when the challenge differs from `c₀`. -/
noncomputable def replayAttack [DecidableEq Y] (m₀ m₁ : Y) : CPAAdversary Y Y Unit where
  coins := PMF.pure ()
  run _ := .liftBind m₀ fun c₀ => .pure ((m₀, m₁), fun c => .pure (decide (c ≠ c₀)))

omit [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y] [AddCommGroup Y] in
/-- The replay attack makes one encryption query. -/
theorem replayAttack_queryBounded [DecidableEq Y] (m₀ m₁ : Y) :
    (replayAttack m₀ m₁).QueryBounded 1 :=
  fun _ _ _ => trivial

omit [Fintype Y] [Nonempty Y] in
/-- **The stream cipher is not CPA-secure** (Katz and Lindell, Section 3.4.2: no deterministic
scheme is CPA-secure): for every generator `G` and messages `m₀ ≠ m₁`, the one-query replay
attack wins the CPA game with probability `1`, i.e. has advantage `1/2`. -/
theorem cpaAdvantage_replayAttack [DecidableEq Y] (G : S → Y) {m₀ m₁ : Y} (hm : m₀ ≠ m₁) :
    cpaAdvantage (streamCipher G) (replayAttack m₀ m₁) = 1 / 2 := by
  have hexp : ∀ b, cpaExp (streamCipher G) (replayAttack m₀ m₁) b = PMF.pure b := by
    intro b
    rw [cpaExp_streamCipher]
    have hrun : ∀ k, expRun (replayAttack m₀ m₁) (G k) b = fun _ => b := by
      intro k
      funext r
      change decide (G k + pick (m₀, m₁) b ≠ G k + m₀) = b
      cases b <;> simp [Ne.symm hm]
    have hmap : ∀ k, (replayAttack m₀ m₁).coins.map (expRun (replayAttack m₀ m₁) (G k) b) =
        PMF.pure b := fun k => by
      rw [hrun]
      simp [replayAttack, PMF.pure_map]
    simp only [hmap, PMF.bind_const]
  rw [cpaAdvantage_eq, hexp, hexp, advantage]
  simp

/-- **No stream cipher family is polynomial-query CPA-secure**: over nontrivial message groups,
the one-query replay attack has constant advantage `1/2`, which is not negligible. -/
theorem not_polyQueryCPASecure_streamCipher {S Y : ℕ → Type*} [∀ n, Fintype (S n)]
    [∀ n, Nonempty (S n)] [∀ n, AddCommGroup (Y n)] [∀ n, Nontrivial (Y n)]
    (G : (n : ℕ) → S n → Y n) :
    ¬ PolyQueryCPASecure (fun n => streamCipher (G n)) (fun _ => Unit) := by
  classical
  intro h
  have hA := h (fun n => replayAttack (0 : Y n) (exists_ne (0 : Y n)).choose)
    ⟨1, fun n => by simpa using replayAttack_queryBounded (0 : Y n) (exists_ne (0 : Y n)).choose⟩
  refine not_negligibleAdv_const (δ := 1 / 2) (by norm_num) (hA.mono fun n => ?_)
  dsimp only
  rw [cpaAdvantage_replayAttack (G n) (exists_ne (0 : Y n)).choose_spec.symm]

end StreamCipher

end Cslib.Crypto.PRG
