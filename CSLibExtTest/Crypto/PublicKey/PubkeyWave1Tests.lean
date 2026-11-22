/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.Assumptions
public import CSLibExt.Crypto.PublicKey.ElGamalCPA
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the hardness assumptions and ElGamal CPA security

All in `G5 = Multiplicative (ZMod 5)` with generator `g = ofAdd 1` and `q = 5`, where discrete
logarithms are easy, so the reductions produce adversaries with large, exactly computed
advantages (none of the theorems is vacuous: every advantage below is strictly positive).
* DLog: the solver `h ↦ toAdd h` has advantage `1`; hence its CDH solver `cdhOfDlog` has
  advantage `1`, and the DDH distinguisher built from it has advantage exactly `|1 - 1/5| = 4/5`.
* CDH: the constant solver `1` wins exactly when `x y = 0` in `ZMod 5`, i.e. on `9` of the `25`
  pairs: advantage `9/25`, and its DDH distinguisher has advantage `|9/25 - 1/5| = 4/25`.
  On a random triple it outputs `1` with probability exactly `1/5`.
* RSA with `p = 61`, `q = 53`, `e = 17`: the factoring algorithm that outputs `(61, 53)` has
  advantage `1`, so the RSA inverter `rsaOfFactor` built from it has advantage `1`; it takes the
  `17`-th root of `2790` (which is `65 ^ 17`). A wrong "factorization" `(1, 3233)` has advantage
  `0`.
* ElGamal CPA: an adversary that queries its encryption oracle once and then decrypts the
  challenge using the discrete log of the public key has CPA advantage `1/2` (the maximum), and
  so does the DDH distinguisher the reduction produces from it.
-/

@[expose] public section

namespace Cslib.Crypto.PubkeyWave1Tests

open Cslib.Crypto.PublicKey Cslib.Crypto.PublicKey.Assumptions Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFintype)

/-- The group `ZMod 5`, written multiplicatively. -/
abbrev G5 := Multiplicative (ZMod 5)

/-- The generator `ofAdd 1`. -/
abbrev g : G5 := Multiplicative.ofAdd 1

theorem generates : ∀ x : G5, x ∈ Subgroup.zpowers g := by
  intro x
  refine Subgroup.mem_zpowers_iff.mpr ⟨(Multiplicative.toAdd x).val, ?_⟩
  rw [zpow_natCast, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  rfl

theorem card_G5 : Fintype.card G5 = 5 := by simp [G5]

theorem hg : g ^ 5 = 1 := by decide

/-! ### Discrete log, CDH, DDH -/

/-- Discrete logarithms are easy in `ZMod 5`: read the exponent off `h`. -/
def dlogSolver : G5 → Unit → ZMod 5 := fun h _ => Multiplicative.toAdd h

theorem dlogAdvantage_dlogSolver : dlogAdvantage 5 g dlogSolver = 1 := by
  have h : dlogGame 5 g dlogSolver = PMF.pure true := by
    rw [dlogGame, ← PMF.map_const (uniformOfFintype (ZMod 5 × Unit)) true]
    congr 1
    funext ω
    revert ω
    decide
  rw [dlogAdvantage, h, winProb_pure]
  rfl

/-- The CDH solver built from it wins with probability `1`. -/
theorem cdhAdvantage_cdhOfDlog : cdhAdvantage 5 g (cdhOfDlog dlogSolver) = 1 :=
  le_antisymm (winProb_le_one _)
    (dlogAdvantage_dlogSolver ▸ dlogAdvantage_le_cdhAdvantage g hg dlogSolver)

/-- The DDH distinguisher built from that has advantage exactly `4/5`. -/
example : ElGamal.ddhAdvantage 5 g (ddhOfCdh (cdhOfDlog dlogSolver)) = 4 / 5 := by
  rw [ddhAdvantage_ddhOfCdh g generates card_G5, cdhAdvantage_cdhOfDlog]
  norm_num [abs_of_pos]

/-- The composite DDH ⇒ DLog bound, instantiated: `1 ≤ 4/5 + 1/5`. -/
example : dlogAdvantage 5 g dlogSolver ≤
    ElGamal.ddhAdvantage 5 g (ddhOfCdh (cdhOfDlog dlogSolver)) + 1 / 5 := by
  exact_mod_cast dlogAdvantage_le_ddhAdvantage g generates card_G5 dlogSolver

/-- A CDH solver that always answers `1`. -/
def constSolver : G5 → G5 → Unit → G5 := fun _ _ _ => 1

/-- It wins exactly when `x y = 0`: on `9` of the `25` exponent pairs. -/
theorem cdhAdvantage_constSolver : cdhAdvantage 5 g constSolver = 9 / 25 := by
  rw [cdhAdvantage, cdhGame, winProb_map_uniform]
  have h : (Finset.univ.filter fun ω : ZMod 5 × ZMod 5 × Unit =>
      decide (constSolver (gpow g ω.1) (gpow g ω.2.1) ω.2.2 = gpow g (ω.1 * ω.2.1)) = true).card =
      9 := by decide
  rw [h]
  simp [ZMod.card]

/-- On a random DDH triple its distinguisher outputs `1` with probability exactly `1/5`. -/
example : winProb (ElGamal.ddhRand 5 g (ddhOfCdh constSolver)) = 1 / 5 := by
  exact_mod_cast winProb_ddhRand_ddhOfCdh g generates card_G5 constSolver

/-- ... so its DDH advantage is `|9/25 - 1/5| = 4/25`. -/
example : ElGamal.ddhAdvantage 5 g (ddhOfCdh constSolver) = 4 / 25 := by
  rw [ddhAdvantage_ddhOfCdh g generates card_G5, cdhAdvantage_constSolver]
  norm_num [abs_of_pos]

/-! ### RSA and factoring -/

/-- The textbook example key `n = 61 * 53 = 3233`, `e = 17`, `d = 2753`. -/
def key : RSA.Key where
  p := 61
  q := 53
  hp := by norm_num
  hq := by norm_num
  hpq := by decide
  e := 17
  d := 2753
  hed_p := by decide
  hed_q := by decide

/-- A factoring algorithm that knows the factors of `3233`. -/
def factorer : ℕ → Unit → ℕ × ℕ := fun _ _ => (61, 53)

/-- A "factoring" algorithm that outputs the trivial factorization. -/
def trivialFactorer : ℕ → Unit → ℕ × ℕ := fun n _ => (1, n)

theorem factorAdvantage_factorer : factorAdvantage (PMF.pure key) factorer = 1 := by
  have h : factorGame (PMF.pure key) factorer = PMF.pure true := by
    rw [factorGame, PMF.pure_bind, ← PMF.map_const (uniformOfFintype Unit) true]
    refine congrArg (PMF.map · (uniformOfFintype Unit)) (funext fun s => ?_)
    have hf : IsFactorization key.n (factorer key.n s) := ⟨by norm_num [factorer, key, RSA.Key.n],
      by norm_num [factorer], by norm_num [factorer]⟩
    simp [hf]
  rw [factorAdvantage, h, winProb_pure]
  rfl

example : factorAdvantage (PMF.pure key) trivialFactorer = 0 := by
  have h : factorGame (PMF.pure key) trivialFactorer = PMF.pure false := by
    rw [factorGame, PMF.pure_bind, ← PMF.map_const (uniformOfFintype Unit) false]
    refine congrArg (PMF.map · (uniformOfFintype Unit)) (funext fun s => ?_)
    have hf : ¬ IsFactorization key.n (trivialFactorer key.n s) := fun h =>
      absurd h.2.1 (lt_irrefl 1)
    simp [hf]
  rw [factorAdvantage, h, winProb_pure]
  rfl

/-- Hence the RSA inverter built from `factorer` has advantage `1`. -/
example : rsaAdvantage (PMF.pure key) (rsaOfFactor factorer) = 1 :=
  le_antisymm (winProb_le_one _)
    (factorAdvantage_factorer ▸ factorAdvantage_le_rsaAdvantage _ factorer)

/-- The inverter takes the `17`-th root of the ciphertext `2790 = 65 ^ 17 mod 3233`. -/
example : (show ZMod key.n from rsaOfFactor factorer key.publicKey 2790 ()) ^ 17 = 2790 :=
  rsaOfFactor_pow_e factorer key () ⟨by norm_num [factorer, key, RSA.Key.n],
    by norm_num [factorer], by norm_num [factorer]⟩ 2790

/-- The only nontrivial factorizations of `3233` are `61 * 53` and `53 * 61`. -/
example : (53 = 61 ∧ 61 = 53) ∨ (53 = 53 ∧ 61 = 61) :=
  eq_or_eq_of_mul_eq (p := 61) (q := 53) (by norm_num) (by norm_num) (by decide) (by decide)
    (by decide)

/-! ### Presampled oracle coins -/

/-- `OracleComp.runCoins` answers the `i`-th query with the `i`-th coin (`1 + 5 = 6`), and with
`default = 0` once the coins run out (`10 + 0 = 10`). -/
example : OracleComp.runCoins (fun (x ρ : ℕ) => x + ρ)
    (.liftBind 1 fun y => .liftBind 10 fun z => .pure (y, z) : OracleComp ℕ ℕ (ℕ × ℕ)) [5] =
      (6, 10) := rfl

/-- `OracleComp.map_runCoins` for a one-query computation that returns the oracle's answer. -/
example : (uniformOfFintype (Fin 1 → Bool)).map
      (fun f => OracleComp.runCoins (fun (_ : Unit) (ρ : Bool) => ρ)
        (.liftBind () fun y => .pure y : OracleComp Unit Bool Bool) (List.ofFn f)) =
    FreeM.evalPMF (fun _ => (uniformOfFintype Bool).map id)
      (.liftBind () fun y => .pure y : OracleComp Unit Bool Bool) :=
  OracleComp.map_runCoins _ (FreeM.isQueryBounded_liftBind fun _ => FreeM.isQueryBounded_pure 0 _)

/-! ### ElGamal CPA -/

/-- An adversary with an encryption oracle: it queries an encryption of `1` (and ignores it),
chooses the messages `1` and `ofAdd 1`, and decrypts the challenge with the discrete log of the
public key. -/
noncomputable def cpaBreaker : PubOracleCPAAdversary G5 G5 (G5 × G5) Unit where
  coins := uniformOfFintype Unit
  run pk _ := .liftBind 1 fun _ => .pure ((1, g), fun c => .pure
    (decide (ElGamal.decrypt (q := 5) (Multiplicative.toAdd pk) c = g)))

theorem cpaBreaker_queryBounded : cpaBreaker.QueryBounded 1 :=
  fun _ _ _ _ => trivial

/-- It always wins, so its CPA advantage is `1/2`. -/
theorem cpaBreaker_advantage : pubOracleCpaAdvantage (ElGamal.scheme 5 g) cpaBreaker = 1 / 2 := by
  rw [← pubCpaAdvantage_toEav (ElGamal.scheme 5 g) (ElGamal.encrypt (q := 5) g) (fun _ _ => rfl)
      cpaBreaker cpaBreaker_queryBounded,
    ElGamal.pubCpaAdvantage_eq_eavAdvantage g _ (cpaBreaker.toEav_coins_uniform rfl _ 1)]
  have h : ElGamal.eavGame 5 g
      (ElGamal.toElGamal (cpaBreaker.toEav (ElGamal.encrypt (q := 5) g) 1)) = PMF.pure true := by
    rw [ElGamal.eavGame, ← PMF.map_const (uniformOfFintype
      (ZMod 5 × ZMod 5 × (Unit × (Fin 1 → ZMod 5) × (Fin 1 → ZMod 5)) × Bool)) true]
    congr 1
    funext ω
    obtain ⟨x, y, r, b⟩ := ω
    simp only [ElGamal.toElGamal, PubOracleCPAAdversary.toEav, cpaBreaker, OracleComp.runCoins,
      List.ofFn_succ, List.ofFn_zero]
    have hx : Multiplicative.toAdd (ElGamal.publicKey (q := 5) g x) = x := by revert x; decide
    rw [hx, ElGamal.decrypt_encrypt]
    cases b <;> rfl
  rw [ElGamal.eavAdvantage, h, PMF.pure_apply_self]
  norm_num

/-- The DDH distinguisher the reduction builds from it also has advantage `1/2`. -/
example : ElGamal.ddhAdvantage 5 g
    (ElGamal.reduction (ElGamal.toElGamal (cpaBreaker.toEav (ElGamal.encrypt (q := 5) g) 1))) =
      1 / 2 :=
  (ElGamal.cpaAdvantage_eq_ddhAdvantage g generates card_G5 cpaBreaker cpaBreaker_queryBounded
    rfl).symm.trans cpaBreaker_advantage

/-- ElGamal as a framework scheme is correct. -/
example : (ElGamal.scheme 5 g).Correct := ElGamal.scheme_correct g

end Cslib.Crypto.PubkeyWave1Tests
