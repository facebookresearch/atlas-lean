/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRG
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for pseudorandom generators and the stream cipher

* The doubling map `s ↦ (s, s)` on `ZMod 2` is not a PRG: the equality test outputs `1` on every
  generator output and on half of the uniform strings, so its PRG advantage is `1/2`.
* The stream cipher over the doubling map decrypts correctly, and an eavesdropper that checks
  whether the two halves of the challenge agree wins with probability `1` (advantage `1/2`).
  `cpaAdvantage_streamCipher_eq` then forces the PRG advantage of its reduction to be `1/2`: the
  reduction breaks the generator, as Katz and Lindell's proof of Theorem 3.18 says it must.
* The identity map on a group has PRG advantage `0` against every distinguisher, and its stream
  cipher is the one-time pad, with eavesdropping advantage `0` against every eavesdropper. The
  identity family satisfies `PRGIndistinguishable` against every distinguisher family, so
  `eavSecure_streamCipher` (which takes indistinguishability, not expansion) gives the asymptotic
  one-time pad directly. But the identity family does not expand, so it is **not** `PRGSecure`
  (Katz and Lindell, Definition 3.14): the expansion conjunct is what rules it out.
* The padding family `Fin n → ZMod 2 → Fin (n + 1) → ZMod 2` (append a `0`) expands, and it is
  `PRGSecure` against the distinguishers that ignore their input;
  `eavSecure_streamCipher_of_prgSecure` then applies to it.
* For every generator, the one-query replay attack has CPA advantage `1/2`, and no stream cipher
  family over `Fin (n + 1) → ZMod 2` is polynomial-query CPA-secure.
-/

@[expose] public section

namespace Cslib.Crypto.PRGTests

open Cslib.Crypto.Framework Cslib.Crypto.PRG

/-- Bit pairs. -/
abbrev Y2 := ZMod 2 × ZMod 2

/-- The doubling map, which is not pseudorandom. -/
def dbl (s : ZMod 2) : Y2 := (s, s)

/-- The equality test on pairs. -/
noncomputable def eqTest : Distinguisher Y2 Unit := ⟨PMF.pure (), fun y _ => decide (y.1 = y.2)⟩

theorem prgReal_dbl_eqTest : prgReal dbl eqTest = PMF.pure true := by
  simp only [prgReal, eqTest, PMF.pure_map, dbl, decide_true, PMF.bind_const]

theorem winProb_prgRand_eqTest : winProb (prgRand eqTest) = 1 / 2 := by
  have h : prgRand eqTest =
      (Cslib.Probability.PMF.uniformOfFintype Y2).map fun y => decide (y.1 = y.2) := by
    simp only [prgRand, eqTest, PMF.map, PMF.pure_bind]
    rfl
  rw [h, winProb_map_uniform]
  have hc : (Finset.univ.filter fun y : Y2 => decide (y.1 = y.2) = true).card = 2 := by decide
  rw [hc]
  simp only [Fintype.card_prod, ZMod.card]
  norm_num

/-- The doubling map has PRG advantage `1/2`. -/
theorem prgAdvantage_dbl_eqTest : prgAdvantage dbl eqTest = 1 / 2 := by
  rw [prgAdvantage, advantage, prgReal_dbl_eqTest, winProb_prgRand_eqTest, winProb_pure]
  norm_num

/-- Stream-cipher roundtrip over the doubling map. -/
example : (streamCipher dbl).dec 1 (dbl 1 + (1, 0)) = some (1, 0) := by decide

example : (streamCipher dbl).Correct := streamCipher_correct dbl

/-- An eavesdropper: challenge with `(0, 0)` and `(1, 0)`, guess `1` when the two halves of the
challenge ciphertext differ. -/
noncomputable def halvesA : CPAAdversary Y2 Y2 Unit :=
  ⟨PMF.pure (), fun _ => .pure (((0, 0), (1, 0)), fun c => .pure (decide (c.1 ≠ c.2)))⟩

theorem halvesA_queryBounded : halvesA.QueryBounded 0 := fun _ _ => trivial

theorem cpaExp_dbl_halvesA (b : Bool) : cpaExp (streamCipher dbl) halvesA b = PMF.pure b := by
  rw [cpaExp_streamCipher]
  have hrun : ∀ k, halvesA.coins.map (expRun halvesA (dbl k) b) = PMF.pure b := by
    intro k
    have : expRun halvesA (dbl k) b = fun _ => b := by
      funext r
      change decide ((dbl k + pick ((0, 0), (1, 0)) b).1 ≠ (dbl k + pick ((0, 0), (1, 0)) b).2) = b
      revert k
      cases b <;> decide
    rw [this]
    simp [halvesA, PMF.pure_map]
  simp only [hrun, PMF.bind_const]

/-- The eavesdropper wins with probability `1` against the stream cipher over `dbl`. -/
theorem cpaAdvantage_dbl_halvesA : cpaAdvantage (streamCipher dbl) halvesA = 1 / 2 := by
  rw [cpaAdvantage_eq, cpaExp_dbl_halvesA, cpaExp_dbl_halvesA, advantage]
  simp

/-- Theorem 3.18 as an equality: the reduction has PRG advantage `1/2` against `dbl`. -/
example : prgAdvantage dbl (cpaReduction halvesA) = 1 / 2 := by
  rw [← cpaAdvantage_streamCipher_eq dbl halvesA_queryBounded, cpaAdvantage_dbl_halvesA]

/-- The identity has PRG advantage `0` against every distinguisher. -/
theorem prgAdvantage_id {Y R : Type*} [Fintype Y] [Nonempty Y] (D : Distinguisher Y R) :
    prgAdvantage (id : Y → Y) D = 0 :=
  advantage_self _

/-- The stream cipher over the identity is the one-time pad: eavesdropping advantage `0`. -/
example (A : CPAAdversary Y2 Y2 Unit) (hA : A.QueryBounded 0) :
    cpaAdvantage (streamCipher (id : Y2 → Y2)) A = 0 := by
  rw [cpaAdvantage_streamCipher_eq _ hA, prgAdvantage_id]

/-- The identity family on bit strings. -/
def idFam (n : ℕ) : (Fin n → ZMod 2) → Fin n → ZMod 2 := id

/-- The identity family is indistinguishable from uniform against **every** distinguisher
family. -/
theorem prgIndistinguishable_idFam (R : ℕ → Type*) [∀ n, Nonempty (R n)] :
    PRGIndistinguishable idFam R fun _ => True :=
  fun D _ => negligibleAdv_zero.mono fun n => (prgAdvantage_id (D n)).le

/-- **The identity family is not a PRG**: it does not expand (`|S 0| = |Y 0| = 1`), so
`PRGSecure` fails for every coin type and every class of distinguishers, although the family is
indistinguishable from uniform (`prgIndistinguishable_idFam`). -/
theorem not_prgSecure_idFam (R : ℕ → Type*) [∀ n, Nonempty (R n)]
    (Admissible : ((n : ℕ) → Distinguisher (Fin n → ZMod 2) (R n)) → Prop) :
    ¬ PRGSecure idFam R Admissible :=
  not_prgSecure_of_card_le (n := 0) le_rfl

/-- In particular the identity family is not `PRGSecure` against all distinguishers, the class
for which `PRGIndistinguishable` holds. -/
example : ¬ PRGSecure idFam (fun _ => Unit) fun _ => True := not_prgSecure_idFam _ _

/-- The asymptotic one-time pad: `eavSecure_streamCipher` applies to the identity family, which
is indistinguishable but not expanding, so the identity stream cipher family is
eavesdropping-secure against every eavesdropper family. -/
theorem eavSecure_streamCipher_idFam : AsymptoticallySecure
    (fun n A => cpaAdvantage (streamCipher (idFam n)) A)
    (fun A : (n : ℕ) → CPAAdversary (Fin n → ZMod 2) (Fin n → ZMod 2) Unit =>
      ∀ n, (A n).QueryBounded 0) :=
  eavSecure_streamCipher idFam _ (fun _ => True) (fun _ h => h) (fun _ _ => trivial)
    (prgIndistinguishable_idFam _)

/-- The padding family: append a `0` to the seed. -/
def pad (n : ℕ) (s : Fin n → ZMod 2) : Fin (n + 1) → ZMod 2 := Fin.snoc s 0

/-- The padding family expands: `2 ^ n < 2 ^ (n + 1)`. -/
theorem prgExpanding_pad : PRGExpanding pad := fun n => by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)

/-- A distinguisher whose guess ignores the challenge has advantage `0`. -/
theorem prgAdvantage_of_blind {S Y R : Type*} [Fintype S] [Nonempty S] [Fintype Y] [Nonempty Y]
    (G : S → Y) (D : Distinguisher Y R) (hD : ∀ y y' r, D.guess y r = D.guess y' r) :
    prgAdvantage G D = 0 := by
  have h : ∀ y, D.guess y = D.guess (Classical.arbitrary Y) := fun y => funext (hD y _)
  simp only [prgAdvantage, prgReal, prgRand, h, PMF.bind_const, advantage_self]

/-- The padding family is a PRG against the distinguishers that ignore their input. -/
theorem prgSecure_pad_blind :
    PRGSecure pad (fun _ => Unit)
      (fun D => ∀ n y y' r, (D n).guess y r = (D n).guess y' r) :=
  ⟨prgExpanding_pad, fun D hD => negligibleAdv_zero.mono fun n =>
    (prgAdvantage_of_blind (pad n) (D n) (hD n)).le⟩

/-- `eavSecure_streamCipher_of_prgSecure` over the padding family, against the eavesdroppers
whose reductions have PRG advantage `0`: the `PRGSecure` hypothesis carries `prgExpanding_pad`,
which the identity family could not supply. -/
example : AsymptoticallySecure
    (fun n A => cpaAdvantage (streamCipher (pad n)) A)
    (fun A : (n : ℕ) → CPAAdversary (Fin (n + 1) → ZMod 2) (Fin (n + 1) → ZMod 2) Unit =>
      ∀ n, (A n).QueryBounded 0 ∧ cpaAdvantage (streamCipher (pad n)) (A n) = 0) :=
  eavSecure_streamCipher_of_prgSecure pad _ (fun D => ∀ n, prgAdvantage (pad n) (D n) = 0)
    (fun _ h n => (h n).1)
    (fun _ h n => by rw [← cpaAdvantage_streamCipher_eq (pad n) (h n).1]; exact (h n).2)
    ⟨prgExpanding_pad, fun _ hD => negligibleAdv_zero.mono fun n => (hD n).le⟩

/-- The replay attack wins against the stream cipher over `dbl`. -/
example : cpaAdvantage (streamCipher dbl) (replayAttack (0, 0) (1, 0)) = 1 / 2 :=
  cpaAdvantage_replayAttack dbl (by decide)

/-- Even the one-time pad (the identity generator) is not CPA-secure with one query. -/
example : cpaAdvantage (streamCipher (id : Y2 → Y2)) (replayAttack (0, 0) (1, 0)) = 1 / 2 :=
  cpaAdvantage_replayAttack id (by decide)

example : ¬ PolyQueryCPASecure
    (fun n => streamCipher (id : (Fin (n + 1) → ZMod 2) → Fin (n + 1) → ZMod 2))
    (fun _ => Unit) :=
  not_polyQueryCPASecure_streamCipher _

end Cslib.Crypto.PRGTests
