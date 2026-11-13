/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.EncryptThenMac
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for encrypt-then-MAC

The CPA scheme is the PRF-style scheme of Katz and Lindell, Construction 3.30, with the keyed
function `F k r = k * r` from `ZMod 3` to `ZMod 5`: `Enc_k(m) = (r, k * r + m)`.

* Encrypt-then-MAC decrypts its encryptions and rejects a mauled ciphertext under a real MAC.
* With the **constant** MAC `tag0` (the tag is always `0`, and verification accepts exactly the
  tag `0`), the mauling adversary, which decrypts the challenge with `1` added to its second
  component and the tag `0` kept (so it still verifies), wins the CCA game with probability `1`
  (`ccaAdvantage = 1/2`). Its CPA reduction has advantage `0`, so `ccaAdvantage_le` forces the
  MAC term alone to be at least `1/2`: the MAC term cannot be dropped. (This example says nothing
  about the necessity of the CPA term.)
* With the constant MAC, a forger that outputs a fixed ciphertext with tag `0` wins `INT-CTXT`
  with probability `1`, so `ctxtAdvantage_le` forces the MAC forger's advantage to be `1`.
* Query bounds of the reductions: a `q`-query CCA adversary gives `(q + 1)`-query MAC forgers
  (the extra query tags the challenge, and is needed even for `q = 0`), and a `q`-query
  ciphertext forger gives a `q`-query MAC forger.
* `ccaAdvantage_le` and `ctxtAdvantage_le` are instantiated with a real MAC.
-/

@[expose] public section

namespace Cslib.Crypto.CCAAEADTests

open Cslib.Crypto.Framework Cslib.Crypto.EncryptThenMac FreeM

/-- PRF-style encryption `Enc_k(m) = (r, k * r + m)`. -/
def encR (k : ZMod 5) (m : ZMod 5) (r : ZMod 3) : ZMod 3 × ZMod 5 := (r, k * (r.val : ZMod 5) + m)

/-- Decryption `Dec_k(r, y) = y - k * r`. -/
def dec₁ (k : ZMod 5) (c : ZMod 3 × ZMod 5) : Option (ZMod 5) := some (c.2 - k * (c.1.val : ZMod 5))

theorem hdec : ∀ k m r, dec₁ k (encR k m r) = some m := by
  intro k m r
  simp [dec₁, encR]

/-- A MAC on `ZMod 3 × ZMod 5` with key in `ZMod 7`. -/
def tagF (k : ZMod 7) (c : ZMod 3 × ZMod 5) : ZMod 7 :=
  k + (c.2.val : ZMod 7) + 2 * (c.1.val : ZMod 7)

/-- The constant MAC: the tag is always `0`, so `detMac` accepts exactly the tag `0`. -/
def tag0 (_ : ZMod 7) (_ : ZMod 3 × ZMod 5) : ZMod 7 := 0

/-- Uniform key and randomness distributions. -/
noncomputable abbrev gen₁ : PMF (ZMod 5) := Cslib.Probability.PMF.uniformOfFintype _
/-- Uniform MAC key. -/
noncomputable abbrev gen₂ : PMF (ZMod 7) := Cslib.Probability.PMF.uniformOfFintype _
/-- Uniform encryption randomness. -/
noncomputable abbrev ρ : PMF (ZMod 3) := Cslib.Probability.PMF.uniformOfFintype _

/-- Encrypt-then-MAC with the real MAC. -/
noncomputable abbrev etm := scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tagF)

/-- Encrypt-then-MAC with the constant MAC. -/
noncomputable abbrev etm0 := scheme (coinScheme gen₁ ρ encR dec₁) (detMac gen₂ tag0)

/-! ### Correctness and rejection -/

example : etm.dec (2, 3) (encAns encR tagF (2, 3) 4 1) = some 4 := by decide

/-- Encrypt-then-MAC is correct. -/
example : etm.Correct :=
  correct_scheme (correct_coinScheme hdec) (correct_detMac _ _)

/-- Mauling the second component of a ciphertext is rejected by the real MAC... -/
example : etm.dec (2, 3) (((encAns encR tagF (2, 3) 4 1).1.1,
    (encAns encR tagF (2, 3) 4 1).1.2 + 1), (encAns encR tagF (2, 3) 4 1).2) = none := by decide

/-- ...and accepted (decrypting to `m + 1`) under the constant MAC. -/
example : etm0.dec (2, 3) (((encAns encR tag0 (2, 3) 4 1).1.1,
    (encAns encR tag0 (2, 3) 4 1).1.2 + 1), (encAns encR tag0 (2, 3) 4 1).2) = some 0 := by
  decide

/-! ### The mauling attack -/

/-- Choose the challenges `0, 1`; decrypt the challenge with `1` added to its second component;
guess `1` iff the answer is `2`. -/
noncomputable def mauler : CCAAdversary (ZMod 5) ((ZMod 3 × ZMod 5) × ZMod 7) Unit where
  coins := PMF.pure ()
  run _ := .pure ((0, 1), fun ct =>
    .liftBind (.inr ((ct.1.1, ct.1.2 + 1), ct.2)) fun (o : Option (ZMod 5)) =>
      .pure (decide (o = some 2)))

theorem mauler_queryBounded : mauler.QueryBounded 1 := fun _ _ _ => trivial

/-- Under the constant MAC the mauler always recovers the challenge bit. -/
theorem realOut_mauler (b : Bool) (w : (ZMod 5 × ZMod 7) × Unit × List (ZMod 3) × ZMod 3 ×
    List (ZMod 3)) : realOut encR dec₁ tag0 mauler b w = b := by
  obtain ⟨⟨k₁, k₂⟩, r, ω₁, x, ω₂⟩ := w
  simp only [realOut, mauler, runTape, realAns, encAns, encR, tag0, pick]
  cases b
  · simp [dec₁]
    decide
  · simp [dec₁]
    exact ⟨by decide, by ring⟩

/-- The mauler wins the CCA game against encrypt-then-MAC with the constant MAC with
probability `1`. -/
theorem ccaAdvantage_mauler : ccaAdvantage etm0 mauler = 1 / 2 := by
  have h : ∀ b, ccaExp etm0 mauler b = PMF.pure b := by
    intro b
    rw [ccaExp_eq encR dec₁ tag0 mauler gen₁ ρ gen₂ mauler_queryBounded b]
    rw [show realOut encR dec₁ tag0 mauler b = Function.const _ b from
      funext (realOut_mauler b), PMF.map_const]
  rw [ccaAdvantage_eq, h, h]
  simp [advantage, winProb]

/-- The CPA reduction of the mauler always outputs `0` under the constant MAC: its simulated
decryption oracle answers `⊥` on the mauled challenge, which was never an encryption answer. -/
theorem simPhase2_mauler (b : Bool) (w : (ZMod 5 × ZMod 7) × Unit × List (ZMod 3) × ZMod 3 ×
    List (ZMod 3)) : (simPhase2 encR tag0 mauler b w).1 = false := by
  have h : ∀ ch ct, simDec ch ([] : List (((ZMod 3 × ZMod 5) × ZMod 7) × ZMod 5)) ct = none := by
    intro ch ct
    simp [simDec, lookupCt]
  change decide (simDec _ [] _ = some 2) = false
  simp [h]

/-- The CPA reduction of the mauler has advantage `0`. -/
theorem cpaAdvantage_mauler :
    cpaAdvantage (coinScheme gen₁ ρ encR dec₁) (cpaReduction tag0 gen₂ mauler) = 0 := by
  have h : ∀ b, cpaExp (coinScheme gen₁ ρ encR dec₁) (cpaReduction tag0 gen₂ mauler) b =
      PMF.pure false := by
    intro b
    rw [cpaExp_eq encR dec₁ tag0 mauler gen₁ ρ gen₂ mauler_queryBounded b]
    rw [show (fun w => (simPhase2 encR tag0 mauler b w).1) = Function.const _ false from
      funext (simPhase2_mauler b), PMF.map_const]
  rw [cpaAdvantage_eq, h, h]
  simp [advantage]

/-- Hence, for the mauler, the MAC term of `ccaAdvantage_le` alone is at least `1/2`: the MAC
term cannot be dropped. -/
example : 1 / 2 ≤
    ∑ j ∈ Finset.range 1, macAdvantage (detMac gen₂ tag0) (forger encR mauler gen₁ ρ 1 j) := by
  have h := ccaAdvantage_le encR dec₁ tag0 mauler gen₁ ρ gen₂ hdec mauler_queryBounded
  rwa [ccaAdvantage_mauler, cpaAdvantage_mauler, zero_add] at h

/-- With the real MAC, the CCA bound applies to the mauler. -/
example : ccaAdvantage etm mauler ≤
    cpaAdvantage (coinScheme gen₁ ρ encR dec₁) (cpaReduction tagF gen₂ mauler) +
    ∑ j ∈ Finset.range 1, macAdvantage (detMac gen₂ tagF) (forger encR mauler gen₁ ρ 1 j) :=
  ccaAdvantage_le encR dec₁ tagF mauler gen₁ ρ gen₂ hdec mauler_queryBounded

/-! ### Query bounds of the reductions -/

/-- The MAC forgers built from the `1`-query mauler make at most `2` tagging queries. -/
example (n j : ℕ) : (forger encR mauler gen₁ ρ n j).QueryBounded 2 :=
  forger_queryBounded encR mauler gen₁ ρ mauler_queryBounded n j

/-- A CCA adversary that makes no query and always guesses `1`. -/
noncomputable def noQuery : CCAAdversary (ZMod 5) ((ZMod 3 × ZMod 5) × ZMod 7) Unit where
  coins := PMF.pure ()
  run _ := .pure ((0, 1), fun _ => .pure true)

theorem noQuery_queryBounded : noQuery.QueryBounded 0 := fun _ _ => trivial

/-- Its MAC forgers make at most one query... -/
example : (forger encR noQuery gen₁ ρ 0 0).QueryBounded 1 :=
  forger_queryBounded encR noQuery gen₁ ρ noQuery_queryBounded 0 0

/-- ...and that query is needed: the forger tags the challenge even when the adversary makes no
query, so the `+ 1` of `forger_queryBounded` cannot be dropped. -/
example : ¬ (forger encR noQuery gen₁ ρ 0 0).QueryBounded 0 := fun h =>
  h (0, true, (), [], 0, [])

/-- Ask one encryption query of `0` and output the answer. -/
noncomputable def echoForger : CtxtForger (ZMod 5) ((ZMod 3 × ZMod 5) × ZMod 7) Unit where
  coins := PMF.pure ()
  forge _ := .liftBind 0 fun ct => .pure ct

theorem echoForger_queryBounded : echoForger.QueryBounded 1 := fun _ _ => trivial

/-- The INT-CTXT reduction of the `1`-query forger makes at most one tagging query... -/
example : (ctxtReduction gen₁ ρ encR 1 echoForger).QueryBounded 1 :=
  ctxtReduction_queryBounded gen₁ ρ encR 1 echoForger_queryBounded

/-- ...and not zero: it forwards the forger's query to the MAC oracle. -/
example : ¬ (ctxtReduction gen₁ ρ encR 1 echoForger).QueryBounded 0 := fun h => h (0, (), [0])

/-! ### Ciphertext integrity -/

/-- Output the fixed ciphertext `((0, 0), 0)` without queries. -/
noncomputable def fixedForger : CtxtForger (ZMod 5) ((ZMod 3 × ZMod 5) × ZMod 7) Unit where
  coins := PMF.pure ()
  forge _ := .pure ((0, 0), 0)

/-- Under the constant MAC every ciphertext with tag `0` is valid (`dec₁` never fails): the fixed
forger, whose ciphertext has tag `0`, always wins. -/
theorem ctxtAdvantage_fixedForger : ctxtAdvantage etm0 fixedForger = 1 := by
  have : ctxtGame etm0 fixedForger = PMF.pure true := by
    simp only [ctxtGame, fixedForger, OracleComp.evalLog_pure, PMF.pure_map, PMF.pure_bind]
    simp [scheme_dec, tag0, dec₁, coinScheme, PMF.bind_const]
  rw [ctxtAdvantage, this]
  simp [winProb]

/-- Hence the MAC forger of `ctxtAdvantage_le` wins with probability `1`. -/
example : 1 ≤ macAdvantage (detMac gen₂ tag0) (ctxtReduction gen₁ ρ encR 0 fixedForger) :=
  ctxtAdvantage_fixedForger ▸
    ctxtAdvantage_le gen₁ ρ encR dec₁ gen₂ tag0 fixedForger fun _ => trivial

end Cslib.Crypto.CCAAEADTests
