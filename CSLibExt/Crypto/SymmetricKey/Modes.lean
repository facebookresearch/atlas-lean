/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.SymmetricKey.PRF
public import CSLibExt.Crypto.SymmetricKey.PRP

/-!
# Modes of operation: counter mode and CBC

Block-cipher modes of operation (Katz and Lindell, Section 3.6.2) as framework `SymmEncScheme`s
(`CSLibExt.Crypto.Framework.Games`), with concrete CPA bounds in the framework's `cpaAdvantage`.

**Block ciphers.** `BlockCipher K X` is the canonical keyed-permutation type `K → Equiv.Perm X`
(Katz and Lindell, Section 3.5.1): `F_k = E k`, `F_k⁻¹ = (E k).symm`. The PRP experiment is
`Cslib.Crypto.PRP.prpReal`, `prpRand` and `prpAdvantage` (`CSLibExt.Crypto.SymmetricKey.PRP`):
a distinguisher with uniform coins queries `F_k` or a uniformly random permutation.

**Eager sampling** is framework infrastructure: `OracleComp.runTape`, the eager-sampling lemmas
and `OracleComp.simTape` live in `CSLibExt.Crypto.Framework.Oracle`, and the eagerly sampled CPA
game `cpaGame_eq_tape`, the guess `cpaTapeGuess` and the generic reduction `cpaTapeReduction` in
`CSLibExt.Crypto.Framework.Games`. This file only specializes them to counter and CBC mode.

**Counter mode** (`ctrScheme ℓ F`, messages of `ℓ` blocks in an additive group `Y`, counters in
`ZMod N`): `Enc_k(m) = (ctr, (mᵢ + F_k (ctr + i))ᵢ)` for a uniform counter `ctr`.
* `ctrScheme_correct`.
* `ctr_cpaGame_eq_prfReal`: with the PRF oracle `F_k`, the reduction `ctrReduction` runs the CPA
  game exactly.
* `ctr_prfRand_le`: with a random function, the reduction's success probability is within
  `q (2ℓ - 1) / (2 N)` of `1/2`. If the challenge counter range is disjoint from the ranges of
  the `q` queries (`CtrFresh`), shifting the random function on the challenge range by the
  difference of the challenge messages and flipping the bit leaves the adversary's view unchanged
  (`ctr_cpaGuess_flip`), so exactly half of the cases are wins (`ctr_two_mul_card_wins`); at most
  `q (2ℓ - 1)` challenge counters overlap (`card_not_ctrFresh`).
* `ctr_cpaAdvantage_le` (Katz and Lindell, Theorem 3.32): for `ℓ ≤ N`,
  `cpaAdvantage (ctrScheme ℓ F) A ≤ prfAdvantage F (ctrReduction A q) + q (2ℓ - 1) / (2 N)`.
  The hypothesis `ℓ ≤ N` is needed: a longer message reuses a counter, and the keystream repeats.

**CBC mode** (`cbcScheme ℓ E`, from a block cipher `E` on an additive group `X`):
`c₀ = IV`, `cᵢ = F_k (cᵢ₋₁ + mᵢ)` for a uniform `IV`.
* `cbcScheme_correct`.
* `cbc_cpaGame_eq_prpReal`: with the oracle `F_k`, the reduction `cbcReduction` runs the CPA game
  exactly; `cbc_cpaAdvantage_le`: the CPA advantage is at most the PRP advantage of the reduction
  plus the guessing advantage of the same reduction against a uniformly random permutation.

**Deferred.** The bound on that ideal-world term for CBC is not proved here; neither is CBC-MAC
security (`CSLibExt.Crypto.SymmetricKey.CBCMAC`). The lazy-sampling step is available:
`CSLibExt.Crypto.Framework.LazySampling` has the adaptive lazy random function and permutation
(`lazyRF`, `lazyRP`) and the PRP/PRF switching lemma (`switching_lemma`, `switching_lemma_le`: a
distinguisher making at most `q` queries tells a uniformly random permutation of `X` from a
uniformly random function with advantage at most `q (q - 1) / (2 |X|)`), and
`Cslib.Crypto.PRP.abs_prfRand_sub_prpRand_le` averages it over a distinguisher's uniform coins.
What remains is
* the query bound for the reduction: for `Adv.QueryBounded q`, every `cbcReduction Adv q s` makes
  at most `(q + 1) ℓ` queries (`FreeM.IsQueryBounded`); with it,
  `abs_prfRand_sub_prpRand_le` replaces the permutation in `PRP.prpRand` by a random function;
* the collision analysis of CBC chaining against a random function: unless two of the
  `(q + 1) ℓ` chaining inputs `cᵢ₋₁ + mᵢ` collide, every ciphertext block is a fresh uniform
  value, so the guess is independent of the challenge bit.

**Known simplifications.** Adversaries have uniform coins on a finite type (the reductions are
`OracleComp` distinguishers with uniform coins, as `Cslib.Crypto.PRF.prfAdvantage` requires).
The keystream of counter mode starts at `ctr` rather than `ctr + 1`.

**Coexistence.** `Cslib.Crypto.PRF.cpaAdvantage_le` is the one-block analogue of
`ctr_cpaAdvantage_le` (Construction 3.30), in that file's own CPA game with randomness drawn up
front; migrating it onto the framework game is a later Wave-2 step.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.5.1 and 3.6.2 (Theorem 3.32).
-/

@[expose] public section

namespace Cslib.Crypto.Modes

open Finset Cslib.Crypto.Framework Cslib.Crypto.Framework.OracleComp

local notation "U" => Cslib.Probability.PMF.uniformOfFintype

/-! ### Block ciphers and pseudorandom permutations -/

/-- A **block cipher** (Katz and Lindell, Section 3.5.1): a keyed permutation of the block space
`X`, in the canonical representation `K → Equiv.Perm X`. The forward direction `F_k` is `E k`,
the inverse `F_k⁻¹` is `(E k).symm`, and the inverse laws are the `Equiv` lemmas. This is the
representation of `Cslib.Crypto.PRP`, so `Cslib.Crypto.PRP.prpAdvantage E D` is the PRP
advantage of a block cipher `E`. -/
abbrev BlockCipher (K X : Type*) := K → Equiv.Perm X

/-! ### Counter mode -/

section CTR

variable {N ℓ : ℕ} {Y : Type*}

/-- The keystream of counter mode: `F_k(ctr), F_k(ctr + 1), …, F_k(ctr + ℓ - 1)`. -/
def keystream (f : ZMod N → Y) (ctr : ZMod N) : Fin ℓ → Y := fun i => f (ctr + (i : ℕ))

variable [AddCommGroup Y]

/-- Randomized counter-mode encryption (Katz and Lindell, Section 3.6.2, over an additive group
of blocks): with initial counter `ctr`, the ciphertext is
`(ctr, m + keystream)`. The keystream starts at `ctr` itself rather than at `ctr + 1`. -/
def ctrEncrypt (f : ZMod N → Y) (m : Fin ℓ → Y) (ctr : ZMod N) : ZMod N × (Fin ℓ → Y) :=
  (ctr, keystream f ctr + m)

/-- Counter-mode decryption: subtract the keystream. -/
def ctrDecrypt (f : ZMod N → Y) (c : ZMod N × (Fin ℓ → Y)) : Fin ℓ → Y := c.2 - keystream f c.1

/-- Decryption inverts encryption. -/
theorem ctrDecrypt_ctrEncrypt (f : ZMod N → Y) (m : Fin ℓ → Y) (ctr : ZMod N) :
    ctrDecrypt f (ctrEncrypt f m ctr) = m := by
  simp [ctrDecrypt, ctrEncrypt]

variable {K : Type*} [Fintype K] [Nonempty K] [NeZero N]

variable (ℓ) in
/-- **Counter mode** from a keyed function `F` (Katz and Lindell, Section 3.6.2): a uniform key,
a uniform initial counter per encryption, messages of `ℓ` blocks. -/
noncomputable def ctrScheme (F : K → ZMod N → Y) :
    SymmEncScheme (Fin ℓ → Y) K (ZMod N × (Fin ℓ → Y)) where
  gen := U K
  enc k m := (U (ZMod N)).map (ctrEncrypt (F k) m)
  dec k c := some (ctrDecrypt (F k) c)

/-- **Correctness** of counter mode. -/
theorem ctrScheme_correct (F : K → ZMod N → Y) : (ctrScheme ℓ F).Correct := by
  intro k _ m c hc
  simp only [ctrScheme, PMF.support_map, Set.mem_image] at hc
  obtain ⟨ctr, -, rfl⟩ := hc
  simp [ctrScheme, ctrDecrypt_ctrEncrypt]

/-- Query the keyed function at each point of `p`, collecting the answers. -/
def queryVec {Q A : Type*} : (n : ℕ) → (Fin n → Q) → OracleComp Q A (Fin n → A)
  | 0, _ => .pure Fin.elim0
  | n + 1, p => .liftBind (p 0) fun y =>
    PFunctor.FreeM.bind (queryVec n (Fin.tail p)) fun ys => .pure (Fin.cons y ys)

/-- `queryVec` returns the oracle's values at the given points. -/
theorem run_queryVec {Q A : Type*} (O : Q → A) :
    ∀ (n : ℕ) (p : Fin n → Q), (queryVec n p).run O = O ∘ p
  | 0, _ => funext fun i => i.elim0
  | n + 1, p => by
    change OracleComp.run O (PFunctor.FreeM.bind (queryVec n (Fin.tail p))
      fun ys => .pure (Fin.cons (α := fun _ => A) (O (p 0)) ys)) = _
    rw [run_bind, run_queryVec O n]
    exact Fin.cons_self_tail (O ∘ p)

/-- Counter-mode encryption as an oracle algorithm querying the keyed function. -/
def ctrEncQ (m : Fin ℓ → Y) (ctr : ZMod N) : OracleComp (ZMod N) Y (ZMod N × (Fin ℓ → Y)) :=
  PFunctor.FreeM.bind (queryVec ℓ fun i => ctr + (i : ℕ)) fun ks => .pure (ctr, ks + m)

omit [NeZero N] in
/-- The oracle form of counter-mode encryption computes `ctrEncrypt`. -/
theorem run_ctrEncQ (f : ZMod N → Y) (m : Fin ℓ → Y) (ctr : ZMod N) :
    (ctrEncQ m ctr).run f = ctrEncrypt f m ctr := by
  rw [ctrEncQ, run_bind, run_queryVec]
  rfl

variable {R : Type*} [Fintype R] [Nonempty R]

/-- The PRF distinguisher built from a CPA adversary against counter mode
(`cpaTapeReduction` with `ctrEncQ`). -/
def ctrReduction (Adv : CPAAdversary (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) R) (q : ℕ) :
    Bool × R × (Fin q → ZMod N) × ZMod N → OracleComp (ZMod N) Y Bool :=
  cpaTapeReduction ctrEncQ Adv q

omit [NeZero N] [Fintype R] [Nonempty R] in
/-- Running `ctrReduction` against the function `f` runs the CPA experiment of counter mode
with keyed function `f`. -/
theorem run_ctrReduction (Adv : CPAAdversary (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) R) (q : ℕ)
    (f : ZMod N → Y) (s : Bool × R × (Fin q → ZMod N) × ZMod N) :
    (ctrReduction Adv q s).run f =
      (cpaTapeGuess (ctrEncrypt f) (Adv.run s.2.1) q s.2.2.1 s.2.2.2 s.1 == s.1) := by
  rw [ctrReduction, run_cpaTapeReduction]
  simp only [run_ctrEncQ]

/-- **The real world**: with the PRF oracle `F k`, the reduction runs the CPA game of counter
mode exactly. -/
theorem ctr_cpaGame_eq_prfReal (F : K → ZMod N → Y)
    (Adv : CPAAdversary (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) R) (hA : Adv.coins = U R) {q : ℕ}
    (hq : Adv.QueryBounded q) :
    cpaGame (ctrScheme ℓ F) Adv = PRF.prfReal F (ctrReduction Adv q) := by
  rw [cpaGame_eq_tape (ctrScheme ℓ F) (fun k => ctrEncrypt (F k)) rfl (fun _ _ => rfl) Adv hA hq,
    PRF.prfReal]
  congr 1
  funext ω
  rw [run_ctrReduction]

/-! #### The random world: a one-time pad on a fresh counter range -/

/-- Add `v i` to `f` at the counter `rs + i`, for each `i`. -/
def ctrShift (f : ZMod N → Y) (rs : ZMod N) (v : Fin ℓ → Y) : ZMod N → Y :=
  fun x => f x + ∑ i : Fin ℓ, if rs + ((i : ℕ) : ZMod N) = x then v i else 0

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- Successive shifts add up. -/
theorem ctrShift_ctrShift (f : ZMod N → Y) (rs : ZMod N) (u v : Fin ℓ → Y) :
    ctrShift (ctrShift f rs u) rs v = ctrShift f rs (u + v) := by
  funext x
  simp only [ctrShift, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- Shifting by zero does nothing. -/
theorem ctrShift_zero (f : ZMod N → Y) (rs : ZMod N) : ctrShift f rs (0 : Fin ℓ → Y) = f := by
  funext x
  simp [ctrShift]

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- Shifting changes nothing outside the counter range `rs, …, rs + ℓ - 1`. -/
theorem ctrShift_of_ne {f : ZMod N → Y} {rs x : ZMod N} (v : Fin ℓ → Y)
    (h : ∀ i : Fin ℓ, rs + ((i : ℕ) : ZMod N) ≠ x) : ctrShift f rs v x = f x := by
  simp [ctrShift, h]

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- If the counter range of `ℓ ≤ N` blocks does not wrap onto itself, shifting adds `v` to the
keystream at `rs`. -/
theorem keystream_ctrShift (hℓ : ℓ ≤ N) (f : ZMod N → Y) (rs : ZMod N) (v : Fin ℓ → Y) :
    keystream (ctrShift f rs v) rs = keystream f rs + v := by
  funext j
  simp only [keystream, ctrShift, Pi.add_apply, add_right_inj]
  rw [sum_eq_single j (fun i _ hij => ?_) (fun h => absurd (mem_univ j) h)]
  · simp
  rw [ite_eq_right_iff]
  intro h'
  exfalso
  apply hij
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (i.2.trans_le hℓ),
    Nat.mod_eq_of_lt (j.2.trans_le hℓ)] at h'
  exact Fin.ext h'

/-- The challenge counter range `rs, …, rs + ℓ - 1` is disjoint from the counter ranges of all
the encryption queries. -/
def CtrFresh {q : ℕ} (ρ : Fin q → ZMod N) (rs : ZMod N) : Prop :=
  ∀ j (i i' : Fin ℓ), ρ j + ((i' : ℕ) : ZMod N) ≠ rs + ((i : ℕ) : ZMod N)

/-- Freshness of the challenge counter range is decidable. -/
instance {q : ℕ} (ρ : Fin q → ZMod N) (rs : ZMod N) : Decidable (CtrFresh (ℓ := ℓ) ρ rs) :=
  by unfold CtrFresh; infer_instance

/-- The challenge messages output by the adversary's first phase (zero if it is stopped). -/
def ctrMsgs (f : ZMod N → Y)
    (c : OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y))
      (((Fin ℓ → Y) × (Fin ℓ → Y)) × (ZMod N × (Fin ℓ → Y) →
        OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) Bool)))
    (q : ℕ) (ρ : Fin q → ZMod N) : (Fin ℓ → Y) × (Fin ℓ → Y) :=
  runTape (ctrEncrypt f) (0, 0) (fun out _ _ => out.1) c q ρ

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- For a fresh challenge range, shifting on it leaves the encryptions of all queries
unchanged. -/
theorem ctrEncrypt_ctrShift_of_fresh {q : ℕ} {ρ : Fin q → ZMod N} {rs : ZMod N}
    (hfresh : CtrFresh (ℓ := ℓ) ρ rs) (f : ZMod N → Y) (v : Fin ℓ → Y) (m : Fin ℓ → Y)
    (j : Fin q) : ctrEncrypt (ctrShift f rs v) m (ρ j) = ctrEncrypt f m (ρ j) := by
  simp only [ctrEncrypt]
  congr 2
  funext i'
  simp only [keystream]
  exact ctrShift_of_ne v fun i h => hfresh j i i' h.symm

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- **The challenge is a one-time pad on a fresh counter range**: flipping the bit and shifting
the random function on the challenge range by the difference of the challenge messages leaves the
adversary's view, hence its guess, unchanged. -/
theorem ctr_cpaGuess_flip (hℓ : ℓ ≤ N) {q : ℕ} {ρ : Fin q → ZMod N} {rs : ZMod N}
    (hfresh : CtrFresh (ℓ := ℓ) ρ rs) (f : ZMod N → Y) (b : Bool)
    (c : OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y))
      (((Fin ℓ → Y) × (Fin ℓ → Y)) × (ZMod N × (Fin ℓ → Y) →
        OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) Bool)))
    (v : Fin ℓ → Y) (hv : v = pick (ctrMsgs f c q ρ) b - pick (ctrMsgs f c q ρ) (!b)) :
    cpaTapeGuess (ctrEncrypt (ctrShift f rs v)) c q ρ rs (!b) =
      cpaTapeGuess (ctrEncrypt f) c q ρ rs b := by
  have hagree := ctrEncrypt_ctrShift_of_fresh hfresh f v
  unfold cpaTapeGuess
  rw [runTape_congr _ _ c q ρ hagree, runTape_eq_runLeaf, runTape_eq_runLeaf]
  rcases hl : runLeaf (ctrEncrypt f) c q ρ with _ | ⟨a, n', ρ'⟩
  · rfl
  · have hm : ctrMsgs f c q ρ = a.1 := by rw [ctrMsgs, runTape_eq_runLeaf, hl]; rfl
    simp only [Option.elim]
    have hchal : ctrEncrypt (ctrShift f rs v) (pick a.1 (!b)) rs =
        ctrEncrypt f (pick a.1 b) rs := by
      simp only [ctrEncrypt, keystream_ctrShift hℓ, hv, hm]
      congr 1
      abel
    rw [hchal]
    refine runTape_congr _ _ _ n' ρ' fun m i => ?_
    obtain ⟨j, hj⟩ := runLeaf_entries _ c q ρ _ hl i
    simp only at hj
    rw [hj, hagree]

omit [Fintype K] [Nonempty K] [NeZero N] in
/-- A Boolean test whose value an involution flips holds on exactly half of the space. -/
private theorem two_mul_card_filter {Ω : Type*} [Fintype Ω] (g : Ω → Bool) (ψ : Ω → Ω)
    (hψ : Function.Involutive ψ) (hg : ∀ ω, g (ψ ω) = !g ω) :
    2 * (univ.filter fun ω => g ω = true).card = Fintype.card Ω := by
  classical
  have hc : (univ.filter fun ω => g ω = false).card =
      (univ.filter fun ω => g ω = true).card := by
    refine card_nbij' ψ ψ ?_ ?_ (fun ω _ => hψ ω) (fun ω _ => hψ ω) <;>
      · intro ω hω
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
        rw [hg, hω]
        rfl
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset Ω)) (fun ω => g ω = true)
  simp_rw [Bool.not_eq_true] at hsplit
  rw [hc, card_univ] at hsplit
  omega

/-- The first-phase algorithms of CPA adversaries against counter mode. -/
abbrev CtrComp (ℓ N : ℕ) (Y : Type*) :=
  OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y))
    (((Fin ℓ → Y) × (Fin ℓ → Y)) × (ZMod N × (Fin ℓ → Y) →
      OracleComp (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) Bool))

omit [Fintype K] [Nonempty K] in
/-- For a fresh challenge counter range, the adversary guesses the bit for exactly half of the
pairs `(f, b)` of a random function and a challenge bit. -/
theorem ctr_two_mul_card_wins [Fintype Y] (hℓ : ℓ ≤ N) {q : ℕ} {ρ : Fin q → ZMod N}
    {rs : ZMod N} (hfresh : CtrFresh (ℓ := ℓ) ρ rs) (c : CtrComp ℓ N Y) :
    2 * (univ.filter fun fb : (ZMod N → Y) × Bool =>
      (cpaTapeGuess (ctrEncrypt fb.1) c q ρ rs fb.2 == fb.2) = true).card =
        Fintype.card ((ZMod N → Y) × Bool) := by
  classical
  refine two_mul_card_filter _ (fun fb => (ctrShift fb.1 rs
    (pick (ctrMsgs fb.1 c q ρ) fb.2 - pick (ctrMsgs fb.1 c q ρ) (!fb.2)), !fb.2)) ?_ ?_
  · rintro ⟨f, b⟩
    have hm : ctrMsgs (ctrShift f rs (pick (ctrMsgs f c q ρ) b - pick (ctrMsgs f c q ρ) (!b)))
        c q ρ = ctrMsgs f c q ρ :=
      runTape_congr _ _ c q ρ (ctrEncrypt_ctrShift_of_fresh hfresh f _)
    simp only [hm, ctrShift_ctrShift, Bool.not_not]
    rw [show pick (ctrMsgs f c q ρ) b - pick (ctrMsgs f c q ρ) (!b) +
      (pick (ctrMsgs f c q ρ) (!b) - pick (ctrMsgs f c q ρ) b) = 0 by abel, ctrShift_zero]
  · rintro ⟨f, b⟩
    simp only
    rw [ctr_cpaGuess_flip hℓ hfresh f b c _ rfl]
    cases cpaTapeGuess (ctrEncrypt f) c q ρ rs b <;> cases b <;> rfl

omit [AddCommGroup Y] [Fintype K] [Nonempty K] in
/-- At most `q (2ℓ - 1)` challenge counters overlap the counter ranges of `q` queries. -/
theorem card_not_ctrFresh {q : ℕ} (ρ : Fin q → ZMod N) :
    (univ.filter fun rs => ¬CtrFresh (ℓ := ℓ) ρ rs).card ≤ q * (2 * ℓ - 1) := by
  classical
  have hsub : (univ.filter fun rs => ¬CtrFresh (ℓ := ℓ) ρ rs) ⊆
      (univ : Finset (Fin q × Fin (2 * ℓ - 1))).image
        fun p => ρ p.1 + ((p.2 : ℕ) : ZMod N) - ((ℓ - 1 : ℕ) : ZMod N) := by
    intro rs hrs
    simp only [mem_filter, mem_univ, true_and, CtrFresh, not_forall, not_not] at hrs
    obtain ⟨j, i, i', h⟩ := hrs
    have hi := i.2
    have hi' := i'.2
    refine mem_image.mpr ⟨(j, ⟨(i' : ℕ) + (ℓ - 1) - i, by omega⟩), mem_univ _, ?_⟩
    simp only
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    linear_combination h
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ : Finset (Fin q × Fin (2 * ℓ - 1))).card := card_image_le
    _ = q * (2 * ℓ - 1) := by simp

omit [Fintype K] [Nonempty K] in
/-- **The random world**: with a random function, the reduction's success probability is within
`q (2ℓ - 1) / (2 N)` of `1/2`; it is exactly `1/2` unless the challenge counter range overlaps
the counter range of one of the at most `q` encryption queries. -/
theorem ctr_prfRand_le [Fintype Y] [Nonempty Y] (hℓ : ℓ ≤ N)
    (Adv : CPAAdversary (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) R) (q : ℕ) :
    |(PRF.prfRand (ctrReduction Adv q) true).toReal - 1 / 2| ≤
      q * ((2 * ℓ - 1 : ℕ) : ℝ) / (2 * N) := by
  classical
  -- the wins for fixed `(r, ρ, rs)`, over the pairs `(f, b)`
  let W : R × (Fin q → ZMod N) × ZMod N → ℕ := fun s =>
    (univ.filter fun fb : (ZMod N → Y) × Bool =>
      (cpaTapeGuess (ctrEncrypt fb.1) (Adv.run s.1) q s.2.1 s.2.2 fb.2 == fb.2) = true).card
  set nF : ℕ := Fintype.card (ZMod N → Y)
  have hF : 0 < nF := Fintype.card_pos
  have hgood : ∀ s : R × (Fin q → ZMod N) × ZMod N, CtrFresh (ℓ := ℓ) s.2.1 s.2.2 → W s = nF := by
    intro s hs
    have h := ctr_two_mul_card_wins hℓ hs (Adv.run s.1)
    simp only [Fintype.card_prod, Fintype.card_bool] at h
    simp only [W]
    omega
  have hle : ∀ s, W s ≤ 2 * nF := fun s => (card_le_univ _).trans
    (by simp [nF, Fintype.card_prod, mul_comm])
  have hcount : (univ.filter fun ω : (ZMod N → Y) × Bool × R × (Fin q → ZMod N) × ZMod N =>
      (cpaTapeGuess (ctrEncrypt ω.1) (Adv.run ω.2.2.1) q ω.2.2.2.1 ω.2.2.2.2 ω.2.1 == ω.2.1) =
        true).card = ∑ s, W s := by
    rw [card_filter]
    simp only [W, card_filter]
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv
      { toFun := fun ω => ((ω.2.2.1, ω.2.2.2.1, ω.2.2.2.2), (ω.1, ω.2.1))
        invFun := fun p => (p.2.1, p.2.2, p.1.1, p.1.2.1, p.1.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun _ => rfl
  have hbad : (univ.filter fun s : R × (Fin q → ZMod N) × ZMod N =>
      ¬CtrFresh (ℓ := ℓ) s.2.1 s.2.2).card ≤
        Fintype.card R * (Fintype.card (Fin q → ZMod N) * (q * (2 * ℓ - 1))) := by
    rw [card_filter, Fintype.sum_prod_type]
    calc _ ≤ ∑ _r : R, Fintype.card (Fin q → ZMod N) * (q * (2 * ℓ - 1)) :=
          sum_le_sum fun r _ => ?_
      _ = _ := by simp
    rw [Fintype.sum_prod_type]
    calc _ ≤ ∑ _ρ : Fin q → ZMod N, q * (2 * ℓ - 1) := sum_le_sum fun ρ _ => ?_
      _ = _ := by simp
    rw [← card_filter]
    exact card_not_ctrFresh ρ
  -- the deviation from `1/2`
  have hdev : |(∑ s, (W s : ℝ)) - Fintype.card (R × (Fin q → ZMod N) × ZMod N) * nF| ≤
      nF * (Fintype.card R * (Fintype.card (Fin q → ZMod N) * (q * ((2 * ℓ - 1 : ℕ) : ℝ)))) := by
    have hsum : (Fintype.card (R × (Fin q → ZMod N) × ZMod N) : ℝ) * nF =
        ∑ _s : R × (Fin q → ZMod N) × ZMod N, (nF : ℝ) := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    rw [hsum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |(W s : ℝ) - nF|
        ≤ ∑ s : R × (Fin q → ZMod N) × ZMod N,
            if CtrFresh (ℓ := ℓ) s.2.1 s.2.2 then (0 : ℝ) else nF := by
          refine sum_le_sum fun s _ => ?_
          split_ifs with hs
          · rw [hgood s hs, sub_self, abs_zero]
          · have h1 : (W s : ℝ) ≤ 2 * nF := by exact_mod_cast hle s
            rw [abs_le]
            constructor <;> linarith [(Nat.cast_nonneg (W s) : (0 : ℝ) ≤ W s)]
      _ = nF * (univ.filter fun s : R × (Fin q → ZMod N) × ZMod N =>
            ¬CtrFresh (ℓ := ℓ) s.2.1 s.2.2).card := by
          rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact_mod_cast hbad
  rw [show (PRF.prfRand (ctrReduction Adv q) true).toReal =
    winProb (PRF.prfRand (ctrReduction Adv q)) from rfl, PRF.prfRand, winProb_map_uniform]
  simp only [run_ctrReduction]
  rw [hcount]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℝ) < Fintype.card (Fin q → ZMod N) := by exact_mod_cast Fintype.card_pos
  have hFr : (0 : ℝ) < nF := by exact_mod_cast hF
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card, Nat.cast_mul, Nat.cast_sum,
    Nat.cast_ofNat] at hdev ⊢
  rw [show ((∑ s, (W s : ℝ)) / (nF * (2 * (Fintype.card R * (Fintype.card (Fin q → ZMod N) *
      N)))) - 1 / 2) = ((∑ s, (W s : ℝ)) - Fintype.card R * (Fintype.card (Fin q → ZMod N) * N) *
        nF) / (2 * nF * (Fintype.card R * (Fintype.card (Fin q → ZMod N) * N))) by
    field_simp]
  have hD : (0 : ℝ) < 2 * nF * (Fintype.card R * (Fintype.card (Fin q → ZMod N) * N)) :=
    mul_pos (mul_pos two_pos hFr) (mul_pos hR (mul_pos hQ hN))
  rw [abs_div, abs_of_pos hD, div_le_div_iff₀ hD (by positivity)]
  calc |(∑ s, (W s : ℝ)) - Fintype.card R * (Fintype.card (Fin q → ZMod N) * N) * nF| * (2 * N)
      ≤ nF * (Fintype.card R * (Fintype.card (Fin q → ZMod N) * (q * ((2 * ℓ - 1 : ℕ) : ℝ)))) *
          (2 * N) := mul_le_mul_of_nonneg_right hdev (by positivity)
    _ = _ := by ring

/-- **Counter mode is CPA-secure, concrete bound** (Katz and Lindell, Theorem 3.32, for messages
of `ℓ ≤ N` blocks): for every adversary with uniform coins making at most `q` encryption queries,
the CPA advantage is at most the PRF advantage of the reduction `ctrReduction` plus
`q (2ℓ - 1) / (2 N)`. -/
theorem ctr_cpaAdvantage_le [Fintype Y] [Nonempty Y] (hℓ : ℓ ≤ N) (F : K → ZMod N → Y)
    (Adv : CPAAdversary (Fin ℓ → Y) (ZMod N × (Fin ℓ → Y)) R) (hA : Adv.coins = U R) {q : ℕ}
    (hq : Adv.QueryBounded q) :
    cpaAdvantage (ctrScheme ℓ F) Adv ≤
      PRF.prfAdvantage F (ctrReduction Adv q) + q * ((2 * ℓ - 1 : ℕ) : ℝ) / (2 * N) := by
  rw [cpaAdvantage, guessAdvantage, ctr_cpaGame_eq_prfReal F Adv hA hq, PRF.prfAdvantage, winProb]
  have h := ctr_prfRand_le hℓ Adv q
  calc |(PRF.prfReal F (ctrReduction Adv q) true).toReal - 1 / 2|
      = |((PRF.prfReal F (ctrReduction Adv q) true).toReal -
          (PRF.prfRand (ctrReduction Adv q) true).toReal) +
          ((PRF.prfRand (ctrReduction Adv q) true).toReal - 1 / 2)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl h)

end CTR

/-! ### Cipher block chaining -/

section CBC

variable {X : Type*} [AddCommGroup X]

/-- The CBC chain from the chaining value `iv`: `c₁ = p (iv + m₁)`, `cᵢ = p (cᵢ₋₁ + mᵢ)`. -/
def cbcChain (p : X → X) (iv : X) : (n : ℕ) → (Fin n → X) → Fin n → X
  | 0, _ => Fin.elim0
  | n + 1, m => Fin.cons (p (iv + m 0)) (cbcChain p (p (iv + m 0)) n (Fin.tail m))

/-- Undo the CBC chain with the inverse permutation: `mᵢ = p⁻¹ (cᵢ) - cᵢ₋₁`. -/
def cbcUnchain (pinv : X → X) (iv : X) : (n : ℕ) → (Fin n → X) → Fin n → X
  | 0, _ => Fin.elim0
  | n + 1, c => Fin.cons (pinv (c 0) - iv) (cbcUnchain pinv (c 0) n (Fin.tail c))

/-- Unchaining inverts chaining. -/
theorem cbcUnchain_cbcChain {p pinv : X → X} (h : ∀ x, pinv (p x) = x) :
    ∀ (n : ℕ) (iv : X) (m : Fin n → X), cbcUnchain pinv iv n (cbcChain p iv n m) = m
  | 0, _, _ => funext fun i => i.elim0
  | n + 1, iv, m => by
    rw [cbcChain, cbcUnchain, Fin.cons_zero, Fin.tail_cons, cbcUnchain_cbcChain h n, h,
      add_sub_cancel_left]
    exact Fin.cons_self_tail m

variable {ℓ : ℕ}

/-- CBC encryption (Katz and Lindell, Section 3.6.2, over an additive group of blocks): with
initial vector `iv`, the ciphertext is `(iv, c₁, …, c_ℓ)`. -/
def cbcEncrypt (p : X → X) (m : Fin ℓ → X) (iv : X) : X × (Fin ℓ → X) := (iv, cbcChain p iv ℓ m)

/-- CBC decryption with the inverse permutation. -/
def cbcDecrypt (pinv : X → X) (c : X × (Fin ℓ → X)) : Fin ℓ → X := cbcUnchain pinv c.1 ℓ c.2

variable {K : Type*} [Fintype K] [Nonempty K] [Fintype X] [Nonempty X]

variable (ℓ) in
/-- **CBC mode** from a block cipher `E` (Katz and Lindell, Section 3.6.2): a uniform key, a
uniform initial vector per encryption, messages of `ℓ` blocks. -/
noncomputable def cbcScheme (E : BlockCipher K X) :
    SymmEncScheme (Fin ℓ → X) K (X × (Fin ℓ → X)) where
  gen := U K
  enc k m := (U X).map (cbcEncrypt (E k) m)
  dec k c := some (cbcDecrypt (E k).symm c)

/-- **Correctness** of CBC mode. -/
theorem cbcScheme_correct (E : BlockCipher K X) : (cbcScheme ℓ E).Correct := by
  intro k _ m c hc
  simp only [cbcScheme, PMF.support_map, Set.mem_image] at hc
  obtain ⟨iv, -, rfl⟩ := hc
  simp [cbcScheme, cbcDecrypt, cbcEncrypt, cbcUnchain_cbcChain (E k).symm_apply_apply]

omit [AddCommGroup X] [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] in
/-- The CBC chain as an oracle algorithm querying the permutation. -/
def chainQ [Add X] (iv : X) : (n : ℕ) → (Fin n → X) → OracleComp X X (Fin n → X)
  | 0, _ => .pure Fin.elim0
  | n + 1, m => .liftBind (iv + m 0) fun c =>
    PFunctor.FreeM.bind (chainQ c n (Fin.tail m)) fun cs => .pure (Fin.cons c cs)

omit [Fintype K] [Nonempty K] [Fintype X] [Nonempty X] in
/-- The oracle form of the CBC chain computes `cbcChain`. -/
theorem run_chainQ (O : X → X) :
    ∀ (n : ℕ) (iv : X) (m : Fin n → X), (chainQ iv n m).run O = cbcChain O iv n m
  | 0, _, _ => funext fun i => i.elim0
  | n + 1, iv, m => by
    change OracleComp.run O (PFunctor.FreeM.bind (chainQ (O (iv + m 0)) n (Fin.tail m))
      fun cs => .pure (Fin.cons (α := fun _ => X) (O (iv + m 0)) cs)) = _
    rw [run_bind, run_chainQ O n]
    rfl

/-- CBC encryption as an oracle algorithm querying the permutation. -/
def cbcEncQ (m : Fin ℓ → X) (iv : X) : OracleComp X X (X × (Fin ℓ → X)) :=
  PFunctor.FreeM.bind (chainQ iv ℓ m) fun cs => .pure (iv, cs)

variable {R : Type*} [Fintype R] [Nonempty R] [DecidableEq X]

/-- The PRP distinguisher built from a CPA adversary against CBC mode (`cpaTapeReduction` with
`cbcEncQ`). -/
def cbcReduction (Adv : CPAAdversary (Fin ℓ → X) (X × (Fin ℓ → X)) R) (q : ℕ) :
    Bool × R × (Fin q → X) × X → OracleComp X X Bool :=
  cpaTapeReduction cbcEncQ Adv q

omit [DecidableEq X] in
/-- **The real world**: with the oracle `F_k`, the reduction runs the CPA game of CBC mode
exactly. -/
theorem cbc_cpaGame_eq_prpReal (E : BlockCipher K X)
    (Adv : CPAAdversary (Fin ℓ → X) (X × (Fin ℓ → X)) R) (hA : Adv.coins = U R) {q : ℕ}
    (hq : Adv.QueryBounded q) :
    cpaGame (cbcScheme ℓ E) Adv = PRP.prpReal E (cbcReduction Adv q) := by
  rw [cpaGame_eq_tape (cbcScheme ℓ E) (fun k => cbcEncrypt (E k)) rfl (fun _ _ => rfl) Adv hA hq,
    PRP.prpReal]
  congr 1
  funext ω
  rw [cbcReduction, run_cpaTapeReduction]
  simp only [cbcEncQ, run_bind, run_chainQ]
  rfl

/-- **CBC mode, the PRP step**: the CPA advantage of every adversary with uniform coins making at
most `q` queries is at most the PRP advantage of `cbcReduction` plus the deviation from `1/2` of
the same reduction against a uniformly random permutation. Bounding that ideal-world term (by a
birthday bound) is deferred. -/
theorem cbc_cpaAdvantage_le (E : BlockCipher K X)
    (Adv : CPAAdversary (Fin ℓ → X) (X × (Fin ℓ → X)) R) (hA : Adv.coins = U R) {q : ℕ}
    (hq : Adv.QueryBounded q) :
    cpaAdvantage (cbcScheme ℓ E) Adv ≤ PRP.prpAdvantage E (cbcReduction Adv q) +
      guessAdvantage (PRP.prpRand (cbcReduction Adv q)) := by
  rw [cpaAdvantage, guessAdvantage, cbc_cpaGame_eq_prpReal E Adv hA hq,
    PRP.prpAdvantage, advantage, guessAdvantage]
  calc |winProb (PRP.prpReal E (cbcReduction Adv q)) - 1 / 2|
      = |(winProb (PRP.prpReal E (cbcReduction Adv q)) -
          winProb (PRP.prpRand (cbcReduction Adv q))) +
          (winProb (PRP.prpRand (cbcReduction Adv q)) - 1 / 2)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

end CBC


end Cslib.Crypto.Modes
