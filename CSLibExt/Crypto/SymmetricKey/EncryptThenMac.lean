/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games

/-!
# Encrypt-then-MAC: CCA security and ciphertext integrity

The encrypt-then-authenticate construction of Katz and Lindell (Section 4.5):
`Enc_{k₁,k₂}(m) = (c, Mac_{k₂}(c))` with `c ← Enc_{k₁}(m)`, and decryption rejects (`⊥`) unless
the tag verifies (`scheme`). Both security results are **concrete** bounds against the
framework's games (`CSLibExt.Crypto.Framework.Games`):

* `ctxtAdvantage_le` (**ciphertext integrity**, `INT-CTXT`): a forger with an encryption oracle
  that outputs a fresh valid ciphertext yields a MAC forger (`ctxtReduction`) with the same
  success probability bound: `ctxtAdvantage ≤ macAdvantage`. A `q`-query forger gives a
  `q`-query MAC forger (`ctxtReduction_queryBounded`). The game `ctxtGame` itself is generic and
  lives in `CSLibExt.Crypto.Framework.Games`.
* `ccaAdvantage_le` (**CCA security**): for a CCA adversary `A` making at most `q` queries,
  `ccaAdvantage (scheme E Mac) A ≤ cpaAdvantage E (cpaReduction A) +
  ∑_{j < q} macAdvantage Mac (forger A j)`. The sum is the textbook `q · ε_Mac` term: the
  forger `j` guesses that the `j`-th query is the first decryption query on a fresh valid
  ciphertext. The CPA reduction makes at most `q` queries (`cpaReduction_queryBounded`) and each
  forger at most `q + 1`, the extra query tagging the challenge (`forger_queryBounded`).

**Hypotheses on the components.** Framework adversaries are deterministic functions of coins
drawn up front, so a reduction can only run an algorithm whose randomness it can sample in
advance. Hence:
* the encryption scheme is a `coinScheme`: `Enc_k(m) = encR k m r` for `r ← ρ`, decrypting every
  encryption for every key and randomness (`hdec`); the reductions carry a random tape of
  `q` samples (`iid`) and `map_runTape_iid` shows that eager tapes equal fresh sampling;
* the MAC is a `detMac`: deterministic tags with canonical verification (Construction 4.5 and
  every PRF-based MAC). Such MACs are strongly unforgeable as soon as they are unforgeable, which
  is why the framework's (weak) `macGame` suffices; Katz and Lindell's theorem asks for a strongly
  secure MAC.

**Proof structure.** Every experiment is rewritten as a deterministic function of the same coins
(keys, adversary coins, a tape per phase and the challenge randomness, `coinDist`): the real CCA
experiment (`ccaExp_eq`), and a simulated experiment that answers decryption queries from the
table of encryption answers (`simDec`), which is exactly the CPA experiment against
`cpaReduction` (`cpaExp_eq`). The two agree unless a decryption query is a fresh ciphertext with
a valid tag (`realOut_eq_of_not_bad`, via the framework's difference lemma), and that bad event
is a forgery for the forger guessing its index (`exists_winsAt_of_bad`).

**Coexistence.** `simDec`, the random-tape semantics and the reductions are new; nothing here
modifies or duplicates an existing game.

**Deferred (not stated here).**
* Integration with `Cslib.Crypto.PRF`: this file does not import it, and there are no adapters
  presenting `Cslib.Crypto.PRF.encrypt` as a `coinScheme` or the PRF MAC as a `detMac`, nor lemmas
  relating its games to the framework's. `PRF.lean` states its CPA and MAC bounds for its own
  adversary and game definitions, so they cannot yet be plugged into `ccaAdvantage_le` or
  `ctxtAdvantage_le`.
* Authenticated encryption with associated data: the encrypt-then-MAC-with-AD construction
  (MAC over `(ad, c)`) is `scheme` applied to the scheme `(ad, m) ↦ (ad, Enc_{k₁}(m))` and a MAC
  on `AD × C`, so `ccaAdvantage_le` and `ctxtAdvantage_le` apply to it once an `AEAD` structure
  is related to `SymmEncScheme` by a ciphertext reassociation `(ad, (c, t)) ≃ ((ad, c), t)`
  (a transport lemma for `ccaExp` and `ctxtGame`), and single-AD challenges are related to CPA
  security of the underlying scheme.
* Negative results (Katz and Lindell, Section 4.5): encrypt-and-MAC with a deterministic MAC is
  not even CPA-secure (equal messages give equal tags), and MAC-then-encrypt over a malleable
  CPA scheme (`Enc_k(m) = (r, F_k(r) ⊕ m)` with padding checks) admits a padding-oracle CCA
  attack. The test file shows the related fact that encrypt-then-MAC with a forgeable MAC is
  CCA-insecure (advantage `1/2`).

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.7, 4.2, 4.3 and 4.5.
* M. Bellare and C. Namprempre, *Authenticated encryption: relations among notions and analysis
  of the generic composition paradigm*, ASIACRYPT 2000.
-/

@[expose] public section

namespace Cslib.Crypto.EncryptThenMac

open Cslib.Crypto.Framework FreeM OracleComp

universe u v w x

/-! ### Random tapes -/

section Tape

variable {Rnd : Type x}

/-- `n` independent samples of `ρ`, as a list (a random tape of length `n`). -/
noncomputable def iid (ρ : PMF Rnd) : ℕ → PMF (List Rnd)
  | 0 => PMF.pure []
  | n + 1 => ρ.bind fun r => (iid ρ n).map (r :: ·)

variable [Inhabited Rnd] {P : PFunctor.{u, v}} {α : Type w}

/-- Run an oracle computation on a random tape: each query `a` is answered by `h a r`, where
`r` is the next tape entry (`default` once the tape is used up). -/
def runTape (h : (a : P.A) → Rnd → P.B a) : P.FreeM α → List Rnd → α
  | .pure x, _ => x
  | .liftBind a k, ω => runTape h (k (h a (ω.headD default))) ω.tail

/-- **Eager sampling**: running an `n`-query computation on a tape of at least `n` independent
samples of `ρ` is running it against the oracle `a ↦ h a <$> ρ` with fresh samples. -/
theorem map_runTape_iid (ρ : PMF Rnd) (h : (a : P.A) → Rnd → P.B a) :
    ∀ {n : ℕ} (m : ℕ) {c : P.FreeM α}, IsQueryBounded n c →
      (iid ρ (n + m)).map (runTape h c) = evalPMF (fun a => ρ.map (h a)) c
  | n, m, .pure x, _ => by
    change (iid ρ (n + m)).map (Function.const _ x) = _
    rw [PMF.map_const, evalPMF_pure']
  | 0, _, .liftBind _ _, hc => hc.elim
  | n + 1, m, .liftBind a k, hc => by
    rw [show n + 1 + m = (n + m) + 1 by omega, iid, PMF.map_bind, evalPMF_liftBind,
      PMF.bind_map]
    congr 1
    funext r
    rw [PMF.map_comp]
    exact map_runTape_iid ρ h m (hc (h a r))

/-- A two-phase query bound bounds the budget left at the output of a tape run. -/
theorem exists_cont_runTape {cont : α → ℕ → Prop} (h : (a : P.A) → Rnd → P.B a) :
    ∀ {n : ℕ} {c : P.FreeM α} (ω : List Rnd), IsQueryBoundedWith cont n c →
      ∃ j ≤ n, cont (runTape h c ω) j
  | n, .pure x, _, hc => ⟨n, le_rfl, hc⟩
  | 0, .liftBind _ _, _, hc => hc.elim
  | _ + 1, .liftBind a k, ω, hc => by
    obtain ⟨j, hj, h'⟩ := exists_cont_runTape h ω.tail (hc (h a (ω.headD default)))
    exact ⟨j, by omega, h'⟩

/-- `runTape` that also records the transcript of `(query, answer)` pairs (single oracle). -/
def runTapeLog {X Y : Type*} (h : X → Rnd → Y) :
    OracleComp X Y α → List Rnd → α × List (X × Y)
  | .pure a, _ => (a, [])
  | .liftBind q k, ω =>
    let y := h q (ω.headD default)
    let p := runTapeLog h (k y) ω.tail
    (p.1, (q, y) :: p.2)

/-- **Eager sampling with transcripts**: the `evalLog` form of `map_runTape_iid`. -/
theorem map_runTapeLog_iid {X Y : Type*} (ρ : PMF Rnd) (h : X → Rnd → Y) :
    ∀ {n : ℕ} (m : ℕ) {c : OracleComp X Y α}, IsQueryBounded n c →
      (iid ρ (n + m)).map (runTapeLog h c) = evalLog (fun q => ρ.map (h q)) c
  | n, m, .pure x, _ => by
    change (iid ρ (n + m)).map (Function.const _ (x, [])) = _
    rw [PMF.map_const, evalLog_pure]
  | 0, _, .liftBind _ _, hc => hc.elim
  | n + 1, m, .liftBind q k, hc => by
    rw [show n + 1 + m = (n + m) + 1 by omega, iid, PMF.map_bind, evalLog_liftBind,
      PMF.bind_map]
    congr 1
    funext r
    rw [PMF.map_comp]
    simp only [Function.comp_apply]
    rw [← map_runTapeLog_iid ρ h m (hc (h q r)), PMF.map_comp]
    rfl

/-- Running against a deterministic oracle and logging is a point mass. -/
theorem evalLog_pure_comp {X Y : Type*} (O : X → Y) :
    ∀ c : OracleComp X Y α,
      evalLog (fun q => PMF.pure (O q)) c = PMF.pure (c.run O, (c.queries O).map fun q => (q, O q))
  | .pure _ => rfl
  | .liftBind q k => by
    rw [evalLog_liftBind, PMF.pure_bind, evalLog_pure_comp O (k (O q)), PMF.pure_map]
    rfl

end Tape

/-! ### Probability comparisons -/

section Compare

variable {α : Type*}

/-- Pointwise domination of the continuations dominates `Pr[· = 1]` of a bind. -/
theorem apply_true_bind_le (μ : PMF α) {f g : α → PMF Bool} (h : ∀ a, f a true ≤ g a true) :
    μ.bind f true ≤ μ.bind g true := by
  simp only [PMF.bind_apply]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

/-- If `f a = 1` implies `g a = 1`, then `Pr[f = 1] ≤ Pr[g = 1]`. -/
theorem apply_true_map_le (μ : PMF α) {f g : α → Bool} (h : ∀ a, f a = true → g a = true) :
    μ.map f true ≤ μ.map g true := by
  simp only [PMF.map_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hf : f a = true
  · simp [hf, h a hf]
  · simp only [Bool.not_eq_true] at hf
    simp [hf]

/-- Point masses on booleans, ordered by implication. -/
theorem pure_true_le {a b : Bool} (h : a = true → b = true) :
    PMF.pure a true ≤ PMF.pure b true := by
  cases a
  · simp
  · simp [h rfl]

/-- **Union bound** over a finite family of events. -/
theorem apply_true_map_le_sum (μ : PMF α) {f : α → Bool} {g : ℕ → α → Bool} {q : ℕ}
    (h : ∀ a, f a = true → ∃ j < q, g j a = true) :
    μ.map f true ≤ ∑ j ∈ Finset.range q, μ.map (g j) true := by
  simp only [PMF.map_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hf : f a = true
  · obtain ⟨j, hj, hg⟩ := h a hf
    simp only [hf, ite_true]
    convert Finset.single_le_sum (f := fun i => if true = g i a then μ a else 0)
      (fun _ _ => bot_le) (Finset.mem_range.mpr hj) using 1
    · simp [hg]
    · exact Finset.sum_congr rfl fun _ _ => by congr
  · simp only [Bool.not_eq_true] at hf
    simp [hf]

/-- Binding a fair coin averages the two branches. -/
theorem fairCoin_bind_apply (f : Bool → PMF Bool) :
    fairCoin.bind f true = (f true true + f false true) / 2 := by
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [fairCoin, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    Nat.cast_ofNat]
  rw [← mul_add, ENNReal.div_eq_inv_mul]

/-- `winProb` is monotone. -/
theorem winProb_mono {G H : PMF Bool} (h : G true ≤ H true) : winProb G ≤ winProb H :=
  ENNReal.toReal_mono (PMF.apply_ne_top _ _) h

end Compare

/-! ### The schemes -/

section Schemes

variable {M K C T Rnd : Type*}

/-- A private-key encryption scheme with **explicit encryption randomness**:
`Enc_k(m) = encR k m r` for `r ← ρ`. Every scheme whose encryption algorithm reads a random tape
has this form; reductions in the framework are deterministic after their coins, so they can
only simulate encryption when its randomness is explicit. -/
noncomputable def coinScheme (gen : PMF K) (ρ : PMF Rnd) (encR : K → M → Rnd → C)
    (dec : K → C → Option M) : SymmEncScheme M K C where
  gen := gen
  enc k m := ρ.map (encR k m)
  dec := dec

/-- Key generation of a `coinScheme`. -/
@[simp] theorem coinScheme_gen (gen : PMF K) (ρ : PMF Rnd) (encR : K → M → Rnd → C)
    (dec : K → C → Option M) : (coinScheme gen ρ encR dec).gen = gen := rfl

/-- A `coinScheme` that decrypts every encryption, for every key and every randomness, is
correct (Katz and Lindell, Definition 3.7). -/
theorem correct_coinScheme {gen : PMF K} {ρ : PMF Rnd} {encR : K → M → Rnd → C}
    {dec : K → C → Option M} (h : ∀ k m r, dec k (encR k m r) = some m) :
    (coinScheme gen ρ encR dec).Correct := by
  intro k _ m c hc
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  exact h k m r

/-- A **deterministic MAC with canonical verification** (Katz and Lindell, Section 4.2 and
Construction 4.5): `Mac_k(m) = tagF k m`, and `Vrfy_k(m, t) = 1` iff `t = tagF k m`. For such
MACs existential unforgeability is already strong unforgeability (Katz and Lindell,
Section 4.2), which is why the framework's `macGame` suffices below. -/
noncomputable def detMac [DecidableEq T] (gen : PMF K) (tagF : K → M → T) : MACScheme M K T where
  gen := gen
  tag k m := PMF.pure (tagF k m)
  verify k m t := decide (t = tagF k m)

/-- Key generation of a `detMac`. -/
@[simp] theorem detMac_gen [DecidableEq T] (gen : PMF K) (tagF : K → M → T) :
    (detMac gen tagF).gen = gen := rfl

/-- Tagging of a `detMac` is deterministic. -/
@[simp] theorem detMac_tag [DecidableEq T] (gen : PMF K) (tagF : K → M → T) (k : K) :
    (detMac gen tagF).tag k = fun m => PMF.pure (tagF k m) := rfl

/-- Verification of a `detMac` recomputes the tag. -/
@[simp] theorem detMac_verify [DecidableEq T] (gen : PMF K) (tagF : K → M → T) (k : K) (m : M)
    (t : T) : (detMac gen tagF).verify k m t = decide (t = tagF k m) := rfl

/-- A deterministic MAC with canonical verification is correct (Katz and Lindell,
Definition 4.1). -/
theorem correct_detMac [DecidableEq T] (gen : PMF K) (tagF : K → M → T) :
    (detMac gen tagF).Correct := by
  intro k _ m t ht
  simp only [detMac, PMF.support_pure, Set.mem_singleton_iff] at ht
  simp [detMac, ht]

end Schemes

section EtM

variable {M K₁ K₂ C T : Type*}

/-- **Encrypt-then-authenticate** (Katz and Lindell, Section 4.5): with independent keys
`k₁, k₂`, `Enc_{k₁,k₂}(m) = (c, Mac_{k₂}(c))` for `c ← Enc_{k₁}(m)`; decryption returns `⊥`
unless the tag verifies, and then decrypts `c`. -/
noncomputable def scheme (E : SymmEncScheme M K₁ C) (Mac : MACScheme C K₂ T) :
    SymmEncScheme M (K₁ × K₂) (C × T) where
  gen := E.gen.bind fun k₁ => Mac.gen.map fun k₂ => (k₁, k₂)
  enc k m := (E.enc k.1 m).bind fun c => (Mac.tag k.2 c).map fun t => (c, t)
  dec k ct := if Mac.verify k.2 ct.1 ct.2 then E.dec k.1 ct.1 else none

/-- Key generation of encrypt-then-MAC samples independent keys. -/
@[simp] theorem scheme_gen (E : SymmEncScheme M K₁ C) (Mac : MACScheme C K₂ T) :
    (scheme E Mac).gen = E.gen.bind fun k₁ => Mac.gen.map fun k₂ => (k₁, k₂) := rfl

/-- Decryption of encrypt-then-MAC. -/
@[simp] theorem scheme_dec (E : SymmEncScheme M K₁ C) (Mac : MACScheme C K₂ T) (k : K₁ × K₂)
    (ct : C × T) :
    (scheme E Mac).dec k ct = if Mac.verify k.2 ct.1 ct.2 then E.dec k.1 ct.1 else none := rfl

/-- Encrypt-then-MAC of a correct scheme and a correct MAC is correct. -/
theorem correct_scheme {E : SymmEncScheme M K₁ C} {Mac : MACScheme C K₂ T} (hE : E.Correct)
    (hM : Mac.Correct) : (scheme E Mac).Correct := by
  rintro ⟨k₁, k₂⟩ hk m ⟨c, t⟩ hct
  simp only [scheme, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image,
    Prod.mk.injEq] at hk hct
  obtain ⟨k₁', hk₁, k₂', hk₂, rfl, rfl⟩ := hk
  obtain ⟨c', hc, t', ht, rfl, rfl⟩ := hct
  simp [scheme, hM _ hk₂ _ _ ht, hE _ hk₁ _ _ hc]

variable {Rnd : Type*} [DecidableEq T]

/-- The answer of the encrypt-then-MAC encryption of `m` on randomness `r`. -/
def encAns (encR : K₁ → M → Rnd → C) (tagF : K₂ → C → T) (k : K₁ × K₂) (m : M) (r : Rnd) :
    C × T :=
  (encR k.1 m r, tagF k.2 (encR k.1 m r))

/-- Encrypt-then-MAC of a `coinScheme` and a `detMac` has explicit randomness too. -/
theorem enc_scheme (gen₁ : PMF K₁) (ρ : PMF Rnd) (encR : K₁ → M → Rnd → C)
    (dec₁ : K₁ → C → Option M) (gen₂ : PMF K₂) (tagF : K₂ → C → T) (k : K₁ × K₂) :
    (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)).enc k =
      fun m => ρ.map (encAns encR tagF k m) := by
  funext m
  simp only [scheme, coinScheme, detMac, PMF.pure_map, PMF.bind_map]
  rfl

end EtM

/-! ### Ciphertext integrity -/

section Ctxt

variable {M C R K₁ K₂ T Rnd : Type*} [Inhabited Rnd] [DecidableEq T]

/-- The MAC forger's simulation of a ciphertext forger on the random tape `ω`: encryption
queries are answered by encrypting with `k₁` and querying the MAC oracle on the result. -/
def ctxtSim (encR : K₁ → M → Rnd → C) (k₁ : K₁) :
    OracleComp M (C × T) (C × T) → List Rnd → OracleComp C T (C × T)
  | .pure ct, _ => .pure ct
  | .liftBind m k, ω =>
    .liftBind (encR k₁ m (ω.headD default)) fun t =>
      ctxtSim encR k₁ (k (encR k₁ m (ω.headD default), t)) ω.tail

/-- The **MAC forger** built from a ciphertext forger making at most `q` queries: sample
`k₁ ← Gen₁` and a tape of `q` encryption randomness values, simulate, output the forged
ciphertext. -/
noncomputable def ctxtReduction (gen₁ : PMF K₁) (ρ : PMF Rnd) (encR : K₁ → M → Rnd → C)
    (q : ℕ) (A : CtxtForger M (C × T) R) : MACForger C T (K₁ × R × List Rnd) where
  coins := gen₁.bind fun k₁ => A.coins.bind fun r => (iid ρ q).map fun ω => (k₁, r, ω)
  forge w := ctxtSim encR w.1 (A.forge w.2.1) w.2.2

omit [DecidableEq T] in
/-- The simulation asks the MAC oracle once per encryption query of the forger, so it inherits
the forger's query bound. -/
theorem isQueryBounded_ctxtSim (encR : K₁ → M → Rnd → C) (k₁ : K₁) :
    ∀ {n : ℕ} {c : OracleComp M (C × T) (C × T)} (ω : List Rnd), IsQueryBounded n c →
      IsQueryBounded n (ctxtSim encR k₁ c ω)
  | _, .pure _, _, _ => trivial
  | 0, .liftBind _ _, _, hc => hc.elim
  | _ + 1, .liftBind m _, ω, hc => fun t =>
    isQueryBounded_ctxtSim encR k₁ ω.tail (hc (encR k₁ m (ω.headD default), t))

omit [DecidableEq T] in
/-- **Query bound of the INT-CTXT reduction**: for a ciphertext forger making at most `q`
encryption queries, `ctxtReduction` makes at most `q` tagging queries (for every tape length),
so it is an admissible forger for `q`-query MAC security. -/
theorem ctxtReduction_queryBounded (gen₁ : PMF K₁) (ρ : PMF Rnd) (encR : K₁ → M → Rnd → C)
    (n : ℕ) {q : ℕ} {A : CtxtForger M (C × T) R} (hA : A.QueryBounded q) :
    (ctxtReduction gen₁ ρ encR n A).QueryBounded q := fun w =>
  isQueryBounded_ctxtSim encR w.1 w.2.2 (hA w.2.1)

omit [DecidableEq T] in
/-- The simulation runs the forger exactly: same output, the tagged values are the first
components of the answers, and every answer carries the valid tag. -/
theorem run_ctxtSim (encR : K₁ → M → Rnd → C) (tagF : K₂ → C → T) (k : K₁ × K₂) :
    ∀ (c : OracleComp M (C × T) (C × T)) (ω : List Rnd),
      (ctxtSim encR k.1 c ω).run (tagF k.2) = (runTapeLog (encAns encR tagF k) c ω).1 ∧
        (ctxtSim encR k.1 c ω).queries (tagF k.2) =
          (runTapeLog (encAns encR tagF k) c ω).2.map (fun e => e.2.1) ∧
        ∀ e ∈ (runTapeLog (encAns encR tagF k) c ω).2, e.2.2 = tagF k.2 e.2.1
  | .pure _, _ => ⟨rfl, rfl, by simp [runTapeLog]⟩
  | .liftBind m k', ω => by
    obtain ⟨h1, h2, h3⟩ := run_ctxtSim encR tagF k (k' (encAns encR tagF k m (ω.headD default)))
      ω.tail
    refine ⟨h1, congrArg (_ :: ·) h2, ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact h3 e he

/-- **Encrypt-then-MAC has ciphertext integrity** (Katz and Lindell, Section 4.5): for every
ciphertext forger making at most `q` encryption queries, its advantage is at most the
existential-forgery advantage of `ctxtReduction` against the MAC. No guessing factor: a fresh
valid ciphertext is a valid tag on a never-tagged value. -/
theorem ctxtAdvantage_le (gen₁ : PMF K₁) (ρ : PMF Rnd) (encR : K₁ → M → Rnd → C)
    (dec₁ : K₁ → C → Option M) (gen₂ : PMF K₂) (tagF : K₂ → C → T) [DecidableEq C] {q : ℕ}
    (A : CtxtForger M (C × T) R) (hA : A.QueryBounded q) :
    ctxtAdvantage (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A ≤
      macAdvantage (detMac gen₂ tagF) (ctxtReduction gen₁ ρ encR q A) := by
  refine winProb_mono ?_
  simp only [ctxtGame, macGame, ctxtReduction, enc_scheme, scheme_gen, coinScheme_gen,
    detMac_gen, detMac_tag, PMF.bind_bind, PMF.bind_map, Function.comp_def, evalLog_pure_comp,
    PMF.pure_map]
  rw [PMF.bind_comm gen₂ gen₁]
  refine apply_true_bind_le _ fun k₁ => apply_true_bind_le _ fun k₂ =>
    apply_true_bind_le _ fun r => ?_
  have hL := map_runTapeLog_iid ρ (encAns encR tagF (k₁, k₂)) 0 (hA r)
  rw [Nat.add_zero] at hL
  rw [← hL, PMF.map_comp, ← PMF.bind_pure_comp]
  refine apply_true_bind_le _ fun ω => pure_true_le fun hwin => ?_
  simp only [Function.comp_apply, scheme_dec, detMac_verify, Bool.and_eq_true,
    decide_eq_true_eq] at hwin
  obtain ⟨h1, h2, h3⟩ := run_ctxtSim encR tagF (k₁, k₂) (A.forge r) ω
  set o := (runTapeLog (encAns encR tagF (k₁, k₂)) (A.forge r) ω).1
  set log := (runTapeLog (encAns encR tagF (k₁, k₂)) (A.forge r) ω).2
  obtain ⟨hdec, hfresh⟩ := hwin
  have hv : o.2 = tagF k₂ o.1 := by
    by_contra hne
    simp [hne] at hdec
  rw [h1, h2]
  simp only [List.map_map, Function.comp_def, Bool.and_eq_true, decide_eq_true_eq, List.mem_map,
    not_exists, not_and, detMac_verify]
  refine ⟨hv, fun e he heq => hfresh ?_⟩
  refine List.mem_map.mpr ⟨e, he, ?_⟩
  rw [Prod.ext_iff]
  exact ⟨heq, by rw [h3 e he, heq, hv]⟩

end Ctxt

/-! ### CCA security -/

section CCA

variable {M C T R K₁ K₂ : Type u} {Rnd : Type*} [DecidableEq C] [DecidableEq T] [Inhabited Rnd]
  (encR : K₁ → M → Rnd → C) (dec₁ : K₁ → C → Option M) (tagF : K₂ → C → T)

/-- Look up a ciphertext in a table of `(ciphertext, message)` pairs. -/
def lookupCt (ct : C × T) : List ((C × T) × M) → Option M
  | [] => none
  | e :: t => if e.1 = ct then some e.2 else lookupCt ct t

/-- A successful lookup finds an entry of the table. -/
theorem mem_of_lookupCt {ct : C × T} {m : M} :
    ∀ {tbl : List ((C × T) × M)}, lookupCt ct tbl = some m → (ct, m) ∈ tbl
  | [], h => by cases h
  | e :: t, h => by
    unfold lookupCt at h
    split_ifs at h with he
    · cases h
      exact List.mem_cons.mpr (Or.inl (by rw [← he]))
    · exact List.mem_cons_of_mem _ (mem_of_lookupCt h)

/-- A failed lookup means the ciphertext is not in the table. -/
theorem ne_of_lookupCt_eq_none {ct : C × T} :
    ∀ {tbl : List ((C × T) × M)}, lookupCt ct tbl = none → ∀ e ∈ tbl, e.1 ≠ ct
  | [], _, _, he => by cases he
  | e :: t, h, e', he' => by
    unfold lookupCt at h
    split_ifs at h with he
    rcases List.mem_cons.mp he' with rfl | he'
    · exact he
    · exact ne_of_lookupCt_eq_none h e' he'

/-- The simulated decryption oracle (Katz and Lindell's reduction in Section 4.5): `⊥` on the
challenge, otherwise the message recorded when the ciphertext was returned by the encryption
oracle, and `⊥` for every other ciphertext. -/
def simDec (ch : Option (C × T)) (tbl : List ((C × T) × M)) (ct : C × T) : Option M :=
  if ch = some ct then none else lookupCt ct tbl

/-- The answer of the real CCA oracles of encrypt-then-MAC on randomness `r` (decryption
ignores `r`). -/
def realAns (k : K₁ × K₂) (ch : Option (C × T)) :
    (a : M ⊕ (C × T)) → Rnd → (CCASig M (C × T)).B a
  | .inl m, r => encAns encR tagF k m r
  | .inr ct, _ => if ch = some ct then none else
      if ct.2 = tagF k.2 ct.1 then dec₁ k.1 ct.1 else none

omit [Inhabited Rnd] in
/-- The CCA oracles of encrypt-then-MAC have explicit randomness. -/
theorem ccaOracle_scheme (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂) (k : K₁ × K₂)
    (ch : Option (C × T)) :
    ccaOracle (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) k ch =
      fun a => ρ.map (realAns encR dec₁ tagF k ch a) := by
  funext a
  rcases a with m | ct
  · exact congrFun (enc_scheme gen₁ ρ encR dec₁ gen₂ tagF k) m
  · change PMF.pure _ = ρ.map (Function.const _ _)
    rw [PMF.map_const]
    congr 1
    change (if ch = some ct then none else _) =
      (if ch = some ct then none else if ct.2 = tagF k.2 ct.1 then dec₁ k.1 ct.1 else none)
    by_cases hch : ch = some ct
    · simp [hch]
    · simp [hch, scheme_dec, detMac_verify, coinScheme]

/-- The state of the simulation: the table of encryption answers, the query counter and the
index of the first **bad** query (a decryption query on a fresh ciphertext with a valid tag). -/
abbrev SimState (M C T : Type u) := List ((C × T) × M) × ℕ × Option ℕ

/-- The simulated game on a random tape: encryption queries as in the real game, decryption
queries answered by `simDec`, and the first bad query recorded. -/
def simRun {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) :
    (CCASig M (C × T)).FreeM α → SimState M C T → List Rnd → α × SimState M C T
  | .pure a, s, _ => (a, s)
  | .liftBind (.inl m) k', s, ω =>
    simRun k ch (k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: s.1, s.2.1 + 1, s.2.2) ω.tail
  | .liftBind (.inr ct) k', s, ω =>
    simRun k ch (k' (simDec ch s.1 ct))
      (s.1, s.2.1 + 1, s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail

/-- Once a bad query is recorded it stays recorded. -/
theorem simRun_bad_some {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) (j : ℕ) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (tbl : List ((C × T) × M)) (n : ℕ) (ω : List Rnd),
      (simRun encR tagF k ch c (tbl, n, some j) ω).2.2.2 = some j
  | .pure _, _, _, _ => rfl
  | .liftBind (.inl m) k', tbl, n, ω =>
    simRun_bad_some k ch j (k' (encAns encR tagF k m (ω.headD default))) _ _ ω.tail
  | .liftBind (.inr ct) k', tbl, n, ω => by
    simp only [simRun, Option.some_or]
    exact simRun_bad_some k ch j (k' (simDec ch tbl ct)) _ _ ω.tail

/-- The table invariant: every entry carries a valid tag and decrypts to its message. -/
def TblInv (k : K₁ × K₂) (tbl : List ((C × T) × M)) : Prop :=
  ∀ e ∈ tbl, e.1.2 = tagF k.2 e.1.1 ∧ dec₁ k.1 e.1.1 = some e.2

/-- **Identical until bad**: if the simulation records no bad query, the real game on the same
tape produces the same output, and the table invariant is maintained. -/
theorem runTape_eq_simRun (hdec : ∀ k₁ m r, dec₁ k₁ (encR k₁ m r) = some m) {α : Type w}
    (k : K₁ × K₂) (ch : Option (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (tbl : List ((C × T) × M)) (n : ℕ) (ω : List Rnd),
      TblInv dec₁ tagF k tbl → (simRun encR tagF k ch c (tbl, n, none) ω).2.2.2 = none →
      runTape (realAns encR dec₁ tagF k ch) c ω = (simRun encR tagF k ch c (tbl, n, none) ω).1 ∧
        TblInv dec₁ tagF k (simRun encR tagF k ch c (tbl, n, none) ω).2.1
  | .pure _, _, _, _, hinv, _ => ⟨rfl, hinv⟩
  | .liftBind (.inl m) k', tbl, n, ω, hinv, hbad => by
    refine runTape_eq_simRun hdec k ch (k' _) _ (n + 1) ω.tail ?_ hbad
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨rfl, hdec _ _ _⟩
    · exact hinv e he
  | .liftBind (.inr ct) k', tbl, n, ω, hinv, hbad => by
    by_cases hb : ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct tbl = none
    · have := simRun_bad_some encR tagF k ch n (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail
      simp only [simRun, hb, Option.none_or] at hbad
      simp only [ne_eq, hb, not_false_eq_true, and_self, ite_true] at hbad
      rw [this] at hbad
      cases hbad
    · have hans : realAns encR dec₁ tagF k ch (.inr ct) (ω.headD default) = simDec ch tbl ct := by
        simp only [realAns, simDec]
        by_cases hch : ch = some ct
        · simp [hch]
        rcases hl : lookupCt ct tbl with _ | m
        · have : ¬ ct.2 = tagF k.2 ct.1 := fun hv => hb ⟨hch, hv, hl⟩
          simp [hch, this]
        · obtain ⟨hv, hd⟩ := hinv _ (mem_of_lookupCt hl)
          simp only at hv hd
          simp [hch, hv, hd]
      simp only [simRun, hb, ite_false, Option.or_none] at hbad ⊢
      change runTape _ (k' (realAns encR dec₁ tagF k ch (.inr ct) (ω.headD default))) ω.tail = _ ∧ _
      rw [hans]
      exact runTape_eq_simRun hdec k ch _ tbl (n + 1) ω.tail hinv hbad

/-- The query counter only grows. -/
theorem le_simRun_count {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (s : SimState M C T) (ω : List Rnd),
      s.2.1 ≤ (simRun encR tagF k ch c s ω).2.2.1
  | .pure _, _, _ => le_rfl
  | .liftBind (.inl m) k', s, ω =>
    (Nat.le_succ _).trans (le_simRun_count k ch (k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: s.1, s.2.1 + 1, s.2.2) ω.tail)
  | .liftBind (.inr ct) k', s, ω =>
    (Nat.le_succ _).trans (le_simRun_count k ch (k' (simDec ch s.1 ct)) (s.1, s.2.1 + 1,
      s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail)

/-- The table only grows. -/
theorem subset_simRun_tbl {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (s : SimState M C T) (ω : List Rnd),
      ∀ e ∈ s.1, e ∈ (simRun encR tagF k ch c s ω).2.1
  | .pure _, _, _, _, he => he
  | .liftBind (.inl m) k', _, ω, e, he =>
    subset_simRun_tbl k ch (k' (encAns encR tagF k m (ω.headD default))) _ ω.tail e
      (List.mem_cons_of_mem _ he)
  | .liftBind (.inr ct) k', s, ω, e, he =>
    subset_simRun_tbl k ch (k' (simDec ch s.1 ct)) (s.1, s.2.1 + 1,
      s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail e he

/-- A query bound bounds the query counter, and the budget left at the output. -/
theorem simRun_count {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) {cont : α → ℕ → Prop} :
    ∀ {N : ℕ} {c : (CCASig M (C × T)).FreeM α} (s : SimState M C T) (ω : List Rnd),
      IsQueryBoundedWith cont N c →
      ∃ j, (simRun encR tagF k ch c s ω).2.2.1 + j ≤ s.2.1 + N ∧
        cont (simRun encR tagF k ch c s ω).1 j
  | N, .pure _, _, _, hc => ⟨N, le_rfl, hc⟩
  | 0, .liftBind _ _, _, _, hc => hc.elim
  | N + 1, .liftBind (.inl m) k', s, ω, hc => by
    obtain ⟨j, hj, h⟩ := simRun_count k ch (c := k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: s.1, s.2.1 + 1, s.2.2) ω.tail (hc _)
    exact ⟨j, by simp only [simRun] at hj ⊢; omega, h⟩
  | N + 1, .liftBind (.inr ct) k', s, ω, hc => by
    obtain ⟨j, hj, h⟩ := simRun_count k ch (c := k' (simDec ch s.1 ct)) (s.1, s.2.1 + 1,
      s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail (hc _)
    exact ⟨j, by simp only [simRun] at hj ⊢; omega, h⟩

/-- The first bad index lies between the counter at the start and at the end. -/
theorem simRun_bad_lt {α : Type w} (k : K₁ × K₂) (ch : Option (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (tbl : List ((C × T) × M)) (n : ℕ) (ω : List Rnd) (i : ℕ),
      (simRun encR tagF k ch c (tbl, n, none) ω).2.2.2 = some i →
        n ≤ i ∧ i < (simRun encR tagF k ch c (tbl, n, none) ω).2.2.1
  | .pure _, _, _, _, _, h => by cases h
  | .liftBind (.inl m) k', tbl, n, ω, i, h => by
    have := simRun_bad_lt k ch (k' (encAns encR tagF k m (ω.headD default))) _ (n + 1) ω.tail i h
    exact ⟨by omega, this.2⟩
  | .liftBind (.inr ct) k', tbl, n, ω, i, h => by
    by_cases hb : ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct tbl = none
    · have hs := simRun_bad_some encR tagF k ch n (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail
      have hc := le_simRun_count encR tagF k ch (k' (simDec ch tbl ct)) (tbl, n + 1, some n) ω.tail
      simp only [simRun, hb, Option.none_or] at h ⊢
      simp only [ne_eq, hb, not_false_eq_true, and_self, ite_true] at h ⊢
      rw [hs] at h
      cases h
      exact ⟨le_rfl, by simpa using hc⟩
    · simp only [simRun, hb, ite_false, Option.or_none] at h ⊢
      have := simRun_bad_lt k ch (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail i h
      exact ⟨by omega, this.2⟩

/-! #### The MAC forgers -/

/-- The MAC forger's simulation of the CCA game (continuation-passing): encryption queries are
encrypted with `k₁` and tagged through the MAC oracle; decryption queries are answered by
`simDec`; the forger stops at the query with index `j` if it is a decryption query and outputs
that ciphertext as its forgery. -/
def fsim (j : ℕ) (k₁ : K₁) (ch : Option (C × T)) {α : Type w}
    (fin : α → List ((C × T) × M) → ℕ → OracleComp C T (C × T)) :
    (CCASig M (C × T)).FreeM α → List ((C × T) × M) → ℕ → List Rnd → OracleComp C T (C × T)
  | .pure a, tbl, n, _ => fin a tbl n
  | .liftBind (.inl m) k', tbl, n, ω =>
    .liftBind (encR k₁ m (ω.headD default)) fun t =>
      fsim j k₁ ch fin (k' (encR k₁ m (ω.headD default), t))
        (((encR k₁ m (ω.headD default), t), m) :: tbl) (n + 1) ω.tail
  | .liftBind (.inr ct) k', tbl, n, ω =>
    if n = j then .pure ct else fsim j k₁ ch fin (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail

/-- Before the guessed index, the forger runs the simulation exactly, tagging only values it
records in the table. -/
theorem fsim_of_lt {α : Type w} (j : ℕ) (k : K₁ × K₂) (ch : Option (C × T))
    (fin : α → List ((C × T) × M) → ℕ → OracleComp C T (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (s : SimState M C T) (ω : List Rnd),
      (simRun encR tagF k ch c s ω).2.2.1 ≤ j →
      let p := simRun encR tagF k ch c s ω
      (fsim encR j k.1 ch fin c s.1 s.2.1 ω).run (tagF k.2) =
          (fin p.1 p.2.1 p.2.2.1).run (tagF k.2) ∧
        ∃ Q, (fsim encR j k.1 ch fin c s.1 s.2.1 ω).queries (tagF k.2) =
            Q ++ (fin p.1 p.2.1 p.2.2.1).queries (tagF k.2) ∧ ∀ v ∈ Q, ∃ e ∈ p.2.1, e.1.1 = v
  | .pure _, _, _, _ => ⟨rfl, [], rfl, by simp⟩
  | .liftBind (.inl m) k', s, ω, hj => by
    obtain ⟨h1, Q, h2, h3⟩ := fsim_of_lt j k ch fin
      (k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: s.1, s.2.1 + 1, s.2.2) ω.tail hj
    refine ⟨h1, encR k.1 m (ω.headD default) :: Q, congrArg (_ :: ·) h2, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨_, subset_simRun_tbl encR tagF k ch _ _ ω.tail _ List.mem_cons_self, rfl⟩
    · exact h3 v hv
  | .liftBind (.inr ct) k', s, ω, hj => by
    have hc := le_simRun_count encR tagF k ch (k' (simDec ch s.1 ct)) (s.1, s.2.1 + 1,
      s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail
    have hn : s.2.1 ≠ j := by
      simp only [simRun] at hj hc
      omega
    simp only [fsim, hn, ite_false]
    exact fsim_of_lt j k ch fin (k' (simDec ch s.1 ct)) _ ω.tail hj

/-- At the first bad query, the forger guessing its index outputs a valid tag on a value it
never tagged, distinct from every tabled ciphertext and from the challenge. -/
theorem fsim_of_bad {α : Type w} (j : ℕ) (k : K₁ × K₂) (ch : Option (C × T))
    (hch : ∀ ct₀, ch = some ct₀ → ct₀.2 = tagF k.2 ct₀.1)
    (fin : α → List ((C × T) × M) → ℕ → OracleComp C T (C × T)) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (tbl : List ((C × T) × M)) (n : ℕ) (ω : List Rnd),
      (∀ e ∈ tbl, e.1.2 = tagF k.2 e.1.1) →
      (simRun encR tagF k ch c (tbl, n, none) ω).2.2.2 = some j →
      let o := (fsim encR j k.1 ch fin c tbl n ω).run (tagF k.2)
      o.2 = tagF k.2 o.1 ∧ o.1 ∉ (fsim encR j k.1 ch fin c tbl n ω).queries (tagF k.2) ∧
        (∀ e ∈ tbl, e.1.1 ≠ o.1) ∧ ∀ ct₀, ch = some ct₀ → ct₀.1 ≠ o.1
  | .pure _, _, _, _, _, h => by cases h
  | .liftBind (.inl m) k', tbl, n, ω, hinv, h => by
    obtain ⟨h1, h2, h3, h4⟩ := fsim_of_bad j k ch hch fin
      (k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: tbl) (n + 1) ω.tail
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · exact hinv e he) h
    refine ⟨h1, ?_, fun e he => h3 e (List.mem_cons_of_mem _ he), h4⟩
    intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · exact h3 _ List.mem_cons_self heq.symm
    · exact h2 hmem
  | .liftBind (.inr ct) k', tbl, n, ω, hinv, h => by
    by_cases hb : ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct tbl = none
    · have hs := simRun_bad_some encR tagF k ch n (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail
      simp only [simRun, Option.none_or] at h
      simp only [ne_eq, hb, not_false_eq_true, and_self, ite_true] at h
      rw [hs] at h
      cases h
      obtain ⟨hch', hv, hl⟩ := hb
      simp only [fsim, ite_true, run, queries]
      refine ⟨hv, List.not_mem_nil, fun e he heq => ?_, fun ct₀ h0 heq => ?_⟩
      · refine ne_of_lookupCt_eq_none hl e he (Prod.ext heq ?_)
        rw [hinv e he, heq, hv]
      · refine hch' ?_
        rw [h0, Prod.ext heq (by rw [hch ct₀ h0, heq, hv])]
    · simp only [simRun, hb, ite_false, Option.or_none] at h
      have hn : n ≠ j := by
        have := simRun_bad_lt encR tagF k ch (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail j h
        omega
      simp only [fsim, hn, ite_false]
      exact fsim_of_bad j k ch hch fin (k' (simDec ch tbl ct)) tbl (n + 1) ω.tail hinv h

/-- The forger's simulation asks the MAC oracle only on encryption queries, so a two-phase query
bound on the adversary, together with a bound on the final stage `fin` with `e` extra queries,
bounds the simulation. -/
theorem isQueryBounded_fsim (j : ℕ) (k₁ : K₁) (ch : Option (C × T)) {α : Type w}
    (fin : α → List ((C × T) × M) → ℕ → OracleComp C T (C × T)) {cont : α → ℕ → Prop} {e : ℕ}
    (hfin : ∀ a tbl n i, cont a i → IsQueryBounded (i + e) (fin a tbl n)) :
    ∀ {N : ℕ} {c : (CCASig M (C × T)).FreeM α} (tbl : List ((C × T) × M)) (n : ℕ)
      (ω : List Rnd), IsQueryBoundedWith cont N c →
      IsQueryBounded (N + e) (fsim encR j k₁ ch fin c tbl n ω)
  | N, .pure a, tbl, n, _, hc => hfin a tbl n N hc
  | 0, .liftBind _ _, _, _, _, hc => hc.elim
  | N + 1, .liftBind (.inl m) k', tbl, n, ω, hc => by
    rw [show N + 1 + e = N + e + 1 by omega]
    exact fun t => isQueryBounded_fsim j k₁ ch fin hfin _ (n + 1) ω.tail
      (hc (encR k₁ m (ω.headD default), t))
  | N + 1, .liftBind (.inr ct) k', tbl, n, ω, hc => by
    by_cases hn : n = j
    · simp only [fsim, hn, ↓reduceIte]
      exact isQueryBounded_pure _ _
    · simp only [fsim, hn, ↓reduceIte]
      exact IsQueryBounded.mono (by omega)
        (isQueryBounded_fsim j k₁ ch fin hfin tbl (n + 1) ω.tail (hc (simDec ch tbl ct)))

/-! #### The CPA reduction -/

/-- The CPA adversary's simulation of the CCA adversary (continuation-passing): encryption
queries are forwarded to the CPA encryption oracle and tagged with the reduction's own MAC key
`k₂`; a decryption query is answered by `simDec` and costs one dummy encryption query, so that
the reduction consumes randomness exactly like the CCA game. -/
def simB [Inhabited M] (k₂ : K₂) (ch : Option (C × T)) {α : Type w} {β : Type x}
    (fin : α → List ((C × T) × M) → β) :
    (CCASig M (C × T)).FreeM α → List ((C × T) × M) → OracleComp M C β
  | .pure a, tbl => .pure (fin a tbl)
  | .liftBind (.inl m) k', tbl =>
    .liftBind m fun c => simB k₂ ch fin (k' (c, tagF k₂ c)) (((c, tagF k₂ c), m) :: tbl)
  | .liftBind (.inr ct) k', tbl =>
    .liftBind default fun _ => simB k₂ ch fin (k' (simDec ch tbl ct)) tbl

/-- On the same tape, the reduction's run is the simulated game. -/
theorem runTape_simB [Inhabited M] (k : K₁ × K₂) (ch : Option (C × T)) {α : Type w} {β : Type x}
    (fin : α → List ((C × T) × M) → β) :
    ∀ (c : (CCASig M (C × T)).FreeM α) (s : SimState M C T) (ω : List Rnd),
      runTape (encR k.1) (simB tagF k.2 ch fin c s.1) ω =
        fin (simRun encR tagF k ch c s ω).1 (simRun encR tagF k ch c s ω).2.1
  | .pure _, _, _ => rfl
  | .liftBind (.inl m) k', s, ω =>
    runTape_simB k ch fin (k' (encAns encR tagF k m (ω.headD default)))
      ((encAns encR tagF k m (ω.headD default), m) :: s.1, s.2.1 + 1, s.2.2) ω.tail
  | .liftBind (.inr ct) k', s, ω =>
    runTape_simB k ch fin (k' (simDec ch s.1 ct)) (s.1, s.2.1 + 1,
      s.2.2.or (if ch ≠ some ct ∧ ct.2 = tagF k.2 ct.1 ∧ lookupCt ct s.1 = none
        then some s.2.1 else none)) ω.tail

/-- The reduction makes as many queries as the CCA adversary. -/
theorem isQueryBoundedWith_simB [Inhabited M] (k₂ : K₂) (ch : Option (C × T)) {α : Type w}
    {β : Type x}
    (fin : α → List ((C × T) × M) → β) {cont : α → ℕ → Prop} {cont' : β → ℕ → Prop}
    (hfin : ∀ a tbl j, cont a j → cont' (fin a tbl) j) :
    ∀ {N : ℕ} {c : (CCASig M (C × T)).FreeM α} (tbl : List ((C × T) × M)),
      IsQueryBoundedWith cont N c → IsQueryBoundedWith cont' N (simB tagF k₂ ch fin c tbl)
  | _, .pure a, tbl, hc => hfin a tbl _ hc
  | 0, .liftBind _ _, _, hc => hc.elim
  | _ + 1, .liftBind (.inl _) _, _, hc => fun c =>
    isQueryBoundedWith_simB k₂ ch fin hfin _ (hc (c, tagF k₂ c))
  | _ + 1, .liftBind (.inr ct) _, tbl, hc => fun _ =>
    isQueryBoundedWith_simB k₂ ch fin hfin _ (hc (simDec ch tbl ct))

/-- **The CPA reduction** (Katz and Lindell's adversary `A_Enc`, Section 4.5): sample a MAC key
`k₂`, run the CCA adversary with encryption queries forwarded to the CPA oracle and tagged with
`k₂`, and decryption queries answered from the table of answers; the challenge ciphertext `c`
is completed to `(c, Mac_{k₂}(c))`. -/
noncomputable def cpaReduction [Inhabited M] (gen₂ : PMF K₂) {R : Type u}
    (A : CCAAdversary M (C × T) R) : CPAAdversary M C (K₂ × R) where
  coins := gen₂.bind fun k₂ => A.coins.map fun r => (k₂, r)
  run w := simB tagF w.1 none (fun out tbl => (out.1, fun c =>
      simB tagF w.1 (some (c, tagF w.1 c)) (fun b _ => b) (out.2 (c, tagF w.1 c)) tbl))
    (A.run w.2) []

/-- The coins of the CPA reduction: a MAC key and the CCA adversary's coins. -/
@[simp] theorem cpaReduction_coins [Inhabited M] (gen₂ : PMF K₂) {R : Type u}
    (A : CCAAdversary M (C × T) R) :
    (cpaReduction tagF gen₂ A).coins = gen₂.bind fun k₂ => A.coins.map fun r => (k₂, r) := rfl

/-- The CPA reduction of a `q`-query CCA adversary makes at most `q` queries. -/
theorem cpaReduction_queryBounded [Inhabited M] (gen₂ : PMF K₂) {R : Type u}
    {A : CCAAdversary M (C × T) R} {q : ℕ} (hA : A.QueryBounded q) :
    (cpaReduction tagF gen₂ A).QueryBounded q := fun w =>
  isQueryBoundedWith_simB tagF w.1 none _
    (fun _ _ _ h _ => isQueryBoundedWith_simB tagF w.1 _ _ (fun _ _ _ _ => trivial) _ (h _)) _
    (hA w.2)

/-! #### The hybrid argument -/

variable [Inhabited M] {R : Type u} (A : CCAAdversary M (C × T) R)

/-- The coins of the hybrid argument: the two keys, the adversary's coins, a tape for each
phase and the challenge randomness. -/
noncomputable def coinDist (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂) (q : ℕ) :
    PMF ((K₁ × K₂) × R × List Rnd × Rnd × List Rnd) :=
  (gen₁.bind fun k₁ => gen₂.map fun k₂ => (k₁, k₂)).bind fun k => A.coins.bind fun r =>
    (iid ρ q).bind fun ω₁ => ρ.bind fun x => (iid ρ q).map fun ω₂ => (k, r, ω₁, x, ω₂)

/-- The real CCA experiment with challenge bit `b`, as a function of the coins. -/
def realOut (b : Bool) (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) : Bool :=
  let out := runTape (realAns encR dec₁ tagF w.1 none) (A.run w.2.1) w.2.2.1
  let ct := encAns encR tagF w.1 (pick out.1 b) w.2.2.2.1
  runTape (realAns encR dec₁ tagF w.1 (some ct)) (out.2 ct) w.2.2.2.2

/-- The first phase of the simulated experiment. -/
def simPhase1 (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) :
    ((M × M) × (C × T → (CCASig M (C × T)).FreeM Bool)) × SimState M C T :=
  simRun encR tagF w.1 none (A.run w.2.1) ([], 0, none) w.2.2.1

/-- The second phase of the simulated experiment with challenge bit `b`. -/
def simPhase2 (b : Bool) (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) :
    Bool × SimState M C T :=
  let p := simPhase1 encR tagF A w
  simRun encR tagF w.1 (some (encAns encR tagF w.1 (pick p.1.1 b) w.2.2.2.1))
    (p.1.2 (encAns encR tagF w.1 (pick p.1.1 b) w.2.2.2.1)) p.2 w.2.2.2.2

/-- The bad event of the simulated experiment: some decryption query was a fresh ciphertext
with a valid tag. -/
def simBad (b : Bool) (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) : Bool :=
  (simPhase2 encR tagF A b w).2.2.2.isSome

omit [Inhabited M] in
/-- Real and simulated experiments agree unless the bad event occurs. -/
theorem realOut_eq_of_not_bad (hdec : ∀ k₁ m r, dec₁ k₁ (encR k₁ m r) = some m) (b : Bool)
    (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) (hw : simBad encR tagF A b w = false) :
    realOut encR dec₁ tagF A b w = (simPhase2 encR tagF A b w).1 := by
  obtain ⟨k, r, ω₁, x, ω₂⟩ := w
  simp only [simBad, simPhase2, simPhase1, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    at hw
  simp only [realOut, simPhase2, simPhase1]
  rcases h1 : simRun encR tagF k none (A.run r) ([], 0, none) ω₁ with ⟨out, tbl, n, bad⟩
  rw [h1] at hw
  cases bad with
  | some j =>
    rw [simRun_bad_some] at hw
    cases hw
  | none =>
    have hb1 : (simRun encR tagF k none (A.run r) ([], 0, none) ω₁).2.2.2 = none := by rw [h1]
    obtain ⟨he1, hi1⟩ := runTape_eq_simRun encR dec₁ tagF hdec k none (A.run r) [] 0 ω₁
      (by simp [TblInv]) hb1
    rw [h1] at he1 hi1
    rw [he1]
    exact (runTape_eq_simRun encR dec₁ tagF hdec k _ _ tbl n ω₂ hi1 hw).1

omit [Inhabited M] in
/-- The real CCA experiment against encrypt-then-MAC, written on random tapes. -/
theorem ccaExp_eq (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂) {q : ℕ} (hA : A.QueryBounded q)
    (b : Bool) :
    ccaExp (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A b =
      (coinDist A gen₁ ρ gen₂ q).map (realOut encR dec₁ tagF A b) := by
  simp only [ccaExp, coinDist, scheme_gen, coinScheme_gen, detMac_gen, ccaOracle_scheme,
    enc_scheme, PMF.map_bind, PMF.map_comp]
  congr 1
  funext k
  congr 1
  funext r
  have h1 := map_runTape_iid ρ (realAns encR dec₁ tagF k none) 0
    ((hA r).mono fun _ _ _ => trivial)
  rw [Nat.add_zero] at h1
  rw [← h1, PMF.bind_map]
  congr 1
  funext ω₁
  rw [Function.comp_apply, PMF.bind_map]
  congr 1
  funext x
  obtain ⟨j, hj, hcont⟩ := exists_cont_runTape (realAns encR dec₁ tagF k none) ω₁ (hA r)
  have h2 := map_runTape_iid ρ (realAns encR dec₁ tagF k (some (encAns encR tagF k
    (pick (runTape (realAns encR dec₁ tagF k none) (A.run r) ω₁).1 b) x))) 0
    ((hcont (encAns encR tagF k
      (pick (runTape (realAns encR dec₁ tagF k none) (A.run r) ω₁).1 b) x)).mono hj)
  rw [Nat.add_zero] at h2
  rw [Function.comp_apply, ← h2]
  rfl

/-- The CPA experiment against the reduction, written on random tapes: it is the simulated
experiment. -/
theorem cpaExp_eq (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂) {q : ℕ} (hA : A.QueryBounded q)
    (b : Bool) :
    cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) b =
      (coinDist A gen₁ ρ gen₂ q).map fun w => (simPhase2 encR tagF A b w).1 := by
  simp only [cpaExp, coinDist, cpaReduction_coins, coinScheme_gen, PMF.map_bind, PMF.map_comp,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext k₁
  congr 1
  funext k₂
  congr 1
  funext r
  have hB := cpaReduction_queryBounded tagF gen₂ hA (k₂, r)
  have h1 := map_runTape_iid ρ (encR k₁) 0 (hB.mono fun _ _ _ => trivial)
  rw [Nat.add_zero] at h1
  change (evalPMF (P := OracleSig M C) (fun m => ρ.map (encR k₁ m)) _).bind _ = _
  rw [← h1, PMF.bind_map]
  congr 1
  funext ω₁
  obtain ⟨j, hj, hcont⟩ := exists_cont_runTape (encR k₁) ω₁ hB
  rw [Function.comp_apply]
  change (ρ.map (encR k₁ _)).bind _ = _
  rw [PMF.bind_map]
  congr 1
  funext x
  have h2 := map_runTape_iid ρ (encR k₁) 0 ((hcont (encR k₁ (pick
    (runTape (encR k₁) ((cpaReduction tagF gen₂ A).run (k₂, r)) ω₁).1 b) x)).mono hj)
  rw [Nat.add_zero] at h2
  rw [Function.comp_apply]
  change evalPMF (P := OracleSig M C) (fun m => ρ.map (encR k₁ m)) _ = _
  rw [← h2]
  congr 1
  funext ω₂
  have e1 := runTape_simB encR tagF (k₁, k₂) none (fun out tbl => (out.1, fun c =>
      simB tagF k₂ (some (c, tagF k₂ c)) (fun b _ => b) (out.2 (c, tagF k₂ c)) tbl))
    (A.run r) ([], 0, none) ω₁
  have e1' : runTape (encR k₁) ((cpaReduction tagF gen₂ A).run (k₂, r)) ω₁ = _ := e1
  rw [e1']
  simp only [simPhase2, simPhase1]
  exact runTape_simB encR tagF (k₁, k₂) _ (fun b _ => b) _ _ ω₂

/-- The run of the MAC forger guessing that the query with index `j` is the first bad one, on
coins `(k₁, b, r, ω₁, x, ω₂)`: it simulates the CCA experiment with challenge bit `b`, tagging
through its MAC oracle (including the challenge), and outputs the `j`-th query if it is a
decryption query (otherwise the challenge ciphertext, which loses). -/
def forgeRun (j : ℕ) (w : K₁ × Bool × R × List Rnd × Rnd × List Rnd) :
    OracleComp C T (C × T) :=
  fsim encR j w.1 none (fun out tbl n =>
      .liftBind (encR w.1 (pick out.1 w.2.1) w.2.2.2.2.1) fun t =>
        fsim encR j w.1 (some (encR w.1 (pick out.1 w.2.1) w.2.2.2.2.1, t))
          (fun _ _ _ => .pure (encR w.1 (pick out.1 w.2.1) w.2.2.2.2.1, t))
          (out.2 (encR w.1 (pick out.1 w.2.1) w.2.2.2.2.1, t)) tbl n w.2.2.2.2.2)
    (A.run w.2.2.1) [] 0 w.2.2.2.1

/-- **The MAC forger** (Katz and Lindell's adversary `A_Mac`, Section 4.5) with guessed index
`j`: sample `k₁ ← Gen₁`, a challenge bit, the adversary's coins and the encryption randomness,
and run `forgeRun`. -/
noncomputable def forger (gen₁ : PMF K₁) (ρ : PMF Rnd) (q j : ℕ) :
    MACForger C T (K₁ × Bool × R × List Rnd × Rnd × List Rnd) where
  coins := gen₁.bind fun k₁ => fairCoin.bind fun b => A.coins.bind fun r =>
    (iid ρ q).bind fun ω₁ => ρ.bind fun x => (iid ρ q).map fun ω₂ => (k₁, b, r, ω₁, x, ω₂)
  forge := forgeRun encR A j

omit [Inhabited M] in
/-- **Query bound of the MAC forgers**: for a CCA adversary making at most `q` queries, every
`forger` (any tape length `n`, any guessed index `j`) makes at most `q + 1` tagging queries: one
per encryption query of the adversary, and one to tag the challenge. So the forgers of
`ccaAdvantage_le` are admissible for `(q + 1)`-query MAC security. -/
theorem forger_queryBounded (gen₁ : PMF K₁) (ρ : PMF Rnd) {q : ℕ} (hA : A.QueryBounded q)
    (n j : ℕ) : (forger encR A gen₁ ρ n j).QueryBounded (q + 1) := by
  intro w
  change IsQueryBounded (q + 1) (forgeRun encR A j w)
  refine isQueryBounded_fsim encR j w.1 none _ (e := 1) ?_ [] 0 w.2.2.2.1 (hA w.2.2.1)
  intro out tbl m i hi t
  refine isQueryBounded_fsim encR j w.1 _ _ (e := 0) ?_ tbl m w.2.2.2.2.2 (hi _)
  intros
  trivial

/-- Whether the forger with guessed index `j` and challenge bit `b` wins on the coins `w` of
the hybrid argument (which contain the MAC key). -/
def winsAt (j : ℕ) (b : Bool) (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd) : Bool :=
  let F := forgeRun encR A j (w.1.1, b, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2)
  decide ((F.run (tagF w.1.2)).2 = tagF w.1.2 (F.run (tagF w.1.2)).1) &&
    decide ((F.run (tagF w.1.2)).1 ∉ F.queries (tagF w.1.2))

omit [Inhabited M] in
/-- **The bad event is a forgery**: if the simulated experiment of a `q`-query adversary has a
bad query, its index `j` is below `q` and the forger guessing `j` wins. -/
theorem exists_winsAt_of_bad (hdec : ∀ k₁ m r, dec₁ k₁ (encR k₁ m r) = some m) {q : ℕ}
    (hA : A.QueryBounded q) (b : Bool) (w : (K₁ × K₂) × R × List Rnd × Rnd × List Rnd)
    (hw : simBad encR tagF A b w = true) : ∃ j < q, winsAt encR tagF A j b w = true := by
  obtain ⟨⟨k₁, k₂⟩, r, ω₁, x, ω₂⟩ := w
  obtain ⟨j₁, hj₁, hcont⟩ := simRun_count encR tagF (k₁, k₂) none ([], 0, none) ω₁ (hA r)
  simp only [simBad, simPhase2, simPhase1] at hw
  rcases h1 : simRun encR tagF (k₁, k₂) none (A.run r) ([], 0, none) ω₁ with
    ⟨out, tbl, n, bad⟩
  rw [h1] at hw hj₁ hcont
  simp only at hj₁
  cases bad with
  | some j =>
    have hb1 : (simRun encR tagF (k₁, k₂) none (A.run r) ([], 0, none) ω₁).2.2.2 = some j := by
      rw [h1]
    have hlt := simRun_bad_lt encR tagF (k₁, k₂) none (A.run r) [] 0 ω₁ j hb1
    rw [h1] at hlt
    obtain ⟨hv, hf, -, -⟩ := fsim_of_bad encR tagF j (k₁, k₂) none (by simp) _ (A.run r) [] 0 ω₁
      (by simp) hb1
    refine ⟨j, by simp only at hlt; omega, ?_⟩
    simp only [winsAt, forgeRun, Bool.and_eq_true]
    exact ⟨decide_eq_true hv, decide_eq_true hf⟩
  | none =>
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hw
    have hb1 : (simRun encR tagF (k₁, k₂) none (A.run r) ([], 0, none) ω₁).2.2.2 = none := by
      rw [h1]
    obtain ⟨-, hinv⟩ := runTape_eq_simRun encR dec₁ tagF hdec (k₁, k₂) none (A.run r) [] 0 ω₁
      (by simp [TblInv]) hb1
    rw [h1] at hinv
    have hlt := simRun_bad_lt encR tagF (k₁, k₂) _ _ tbl n ω₂ j hj
    obtain ⟨j₂, hj₂, -⟩ := simRun_count encR tagF (k₁, k₂)
      (some (encAns encR tagF (k₁, k₂) (pick out.1 b) x))
      (c := out.2 (encAns encR tagF (k₁, k₂) (pick out.1 b) x)) (tbl, n, none) ω₂
      (hcont (encAns encR tagF (k₁, k₂) (pick out.1 b) x))
    obtain ⟨hr1, Q, hq1, hQ⟩ := fsim_of_lt encR tagF j (k₁, k₂) none (fun out tbl n =>
      .liftBind (encR k₁ (pick out.1 b) x) fun t =>
        fsim encR j k₁ (some (encR k₁ (pick out.1 b) x, t))
          (fun _ _ _ => .pure (encR k₁ (pick out.1 b) x, t))
          (out.2 (encR k₁ (pick out.1 b) x, t)) tbl n ω₂) (A.run r) ([], 0, none) ω₁
      (by rw [h1]; exact hlt.1)
    rw [h1] at hr1 hq1 hQ
    obtain ⟨hv, hf, h3, h4⟩ := fsim_of_bad encR tagF j (k₁, k₂)
      (some (encAns encR tagF (k₁, k₂) (pick out.1 b) x)) (by simp [encAns])
      (fun _ _ _ => .pure (encAns encR tagF (k₁, k₂) (pick out.1 b) x))
      (out.2 (encAns encR tagF (k₁, k₂) (pick out.1 b) x)) tbl n ω₂
      (fun e he => (hinv e he).1) hj
    refine ⟨j, by simp only at hlt hj₂; omega, ?_⟩
    simp only [winsAt, forgeRun, Bool.and_eq_true]
    refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
    · rw [hr1]
      exact hv
    rw [hr1, hq1]
    simp only [List.mem_append, not_or]
    refine ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨e, he, heq⟩ := hQ _ hmem
      exact h3 e he heq
    · intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · exact h4 _ rfl heq.symm
      · exact hf hmem

omit [Inhabited M] in
/-- The forger's success probability averages the two challenge bits. -/
theorem macGame_forger_apply (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂) (q j : ℕ) :
    macGame (detMac gen₂ tagF) (forger encR A gen₁ ρ q j) true =
      ((coinDist A gen₁ ρ gen₂ q).map (winsAt encR tagF A j true) true +
        (coinDist A gen₁ ρ gen₂ q).map (winsAt encR tagF A j false) true) / 2 := by
  rw [← fairCoin_bind_apply (fun b => (coinDist A gen₁ ρ gen₂ q).map (winsAt encR tagF A j b))]
  congr 1
  simp only [macGame, forger, coinDist, detMac_gen, detMac_tag, evalLog_pure_comp, PMF.pure_map,
    PMF.bind_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm gen₂ gen₁]
  simp_rw [PMF.bind_comm gen₂ fairCoin]
  rw [PMF.bind_comm gen₁ fairCoin]
  congr 1; funext b; congr 1; funext k₁; congr 1; funext k₂; congr 1; funext r
  congr 1; funext ω₁; congr 1; funext x
  rw [← PMF.bind_pure_comp]
  congr 1; funext ω₂
  simp only [Function.comp_apply, winsAt, detMac_verify, List.map_map, Function.comp_def,
    List.map_id']

/-- **Encrypt-then-MAC is CCA-secure** (Katz and Lindell, Section 4.5, encrypt-then-authenticate
with a CPA-secure scheme and a MAC with unique tags): for every CCA adversary making at most `q`
oracle queries,
`ccaAdvantage ≤ cpaAdvantage (cpaReduction A) + ∑_{j < q} macAdvantage (forger j)`.
The sum is Katz and Lindell's `q · ε_Mac` factor, with the guessed index made explicit.
The reductions are admissible query-bounded adversaries: `cpaReduction` makes at most `q`
encryption queries (`cpaReduction_queryBounded`) and every `forger` at most `q + 1` tagging
queries (`forger_queryBounded`).

Hypotheses on the components (needed because framework adversaries are deterministic after
their coins, so the reductions must run them): the encryption scheme has explicit randomness and
decrypts every encryption (`hdec`), and the MAC is deterministic with canonical verification. -/
theorem ccaAdvantage_le (gen₁ : PMF K₁) (ρ : PMF Rnd) (gen₂ : PMF K₂)
    (hdec : ∀ k₁ m r, dec₁ k₁ (encR k₁ m r) = some m) {q : ℕ} (hA : A.QueryBounded q) :
    ccaAdvantage (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A ≤
      cpaAdvantage (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) +
        ∑ j ∈ Finset.range q, macAdvantage (detMac gen₂ tagF) (forger encR A gen₁ ρ q j) := by
  set μ := coinDist A gen₁ ρ gen₂ q
  have hb : ∀ b, advantage (ccaExp (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A b)
      (cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) b) ≤
        winProb (μ.map (simBad encR tagF A b)) := by
    intro b
    rw [ccaExp_eq encR dec₁ tagF A gen₁ ρ gen₂ hA, cpaExp_eq encR dec₁ tagF A gen₁ ρ gen₂ hA]
    exact advantage_le_winProb_of_eq_of_not_bad _ _ _ _ fun w hw =>
      realOut_eq_of_not_bad encR dec₁ tagF A hdec b w hw
  have hu : ∀ b, μ.map (simBad encR tagF A b) true ≤
      ∑ j ∈ Finset.range q, μ.map (winsAt encR tagF A j b) true := fun b =>
    apply_true_map_le_sum μ (exists_winsAt_of_bad encR dec₁ tagF A hdec hA b)
  have hfin : ∀ (G : PMF Bool), G true ≠ ⊤ := fun G => PMF.apply_ne_top _ _
  have hm : winProb (μ.map (simBad encR tagF A true)) + winProb (μ.map (simBad encR tagF A false))
      ≤ 2 * ∑ j ∈ Finset.range q, macAdvantage (detMac gen₂ tagF) (forger encR A gen₁ ρ q j) := by
    have hsum : ∀ j, 2 * macGame (detMac gen₂ tagF) (forger encR A gen₁ ρ q j) true =
        μ.map (winsAt encR tagF A j true) true + μ.map (winsAt encR tagF A j false) true := by
      intro j
      rw [macGame_forger_apply, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
    have hE : μ.map (simBad encR tagF A true) true + μ.map (simBad encR tagF A false) true ≤
        ∑ j ∈ Finset.range q, 2 * macGame (detMac gen₂ tagF) (forger encR A gen₁ ρ q j) true := by
      simp_rw [hsum]
      rw [Finset.sum_add_distrib]
      exact add_le_add (hu true) (hu false)
    have := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun j _ =>
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hfin _)) hE
    rw [ENNReal.toReal_add (hfin _) (hfin _), ENNReal.toReal_sum fun j _ =>
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hfin _)] at this
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
    rw [Finset.mul_sum]
    exact this
  have hb' := hb false
  rw [advantage_comm] at hb'
  have t1 := advantage_triangle
    (ccaExp (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A true)
    (cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) true)
    (ccaExp (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A false)
  have t2 := advantage_triangle
    (cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) true)
    (cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ A) false)
    (ccaExp (scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)) A false)
  rw [ccaAdvantage_eq, cpaAdvantage_eq]
  linarith [hb true]

end CCA

end Cslib.Crypto.EncryptThenMac
