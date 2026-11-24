/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.GoldwasserMicali
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Tests for Goldwasser–Micali encryption

A non-degenerate key for the modulus `N = 15 = 3 · 5`: `y = 2` is a quadratic non-residue
modulo `15` (by the Euler test of `isSquare_iff_euler`: `2 ^ (3 / 2) = 2 ≠ 1` modulo `3`), and its
Jacobi symbol is `(2 / 15) = (2 / 3)(2 / 5) = (-1)(-1) = 1`, so it is a pseudo-square, as
Goldwasser and Micali require. With randomness `x = 7`, the encryptions of `0` and `1` are
`49 ≡ 4` and `2 · 49 ≡ 8`, and trapdoor decryption returns `0` and `1`. The scheme with the point
key distribution on this key is correct, and the per-adversary reduction is instantiated. The
all-distinguisher hypothesis is shown to force `ε ≥ 1` on this key, and the scheme is shown not to
be `IndSecure` with error `1/2` against unbounded distinguishers.
-/

@[expose] public section

namespace Cslib.Crypto.GoldwasserMicaliTests

open Cslib.Crypto.PublicKey Cslib.Crypto.PublicKey.GoldwasserMicali Cslib.Crypto.Framework

/-- The unit `2` modulo `15`. -/
def y : (ZMod 15)ˣ := ZMod.unitOfCoprime 2 (by norm_num)

/-- The unit `7` modulo `15`. -/
def x : (ZMod 15)ˣ := ZMod.unitOfCoprime 7 (by norm_num)

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `2` is not a square modulo `15`, by the Euler test. -/
theorem y_not_isSquare : ¬ IsSquare y := by
  have h := isSquare_iff_euler (p := 3) (q := 5) (by norm_num) y
  rw [h]
  decide

/-- `2` has Jacobi symbol `1` modulo `15`: a pseudo-square. -/
example : jacobiSym 2 15 = 1 := by norm_num

/-- `(y, (3, 5))` is a valid key for the modulus `15`. -/
theorem isKey : IsKey 15 (y, (3, 5)) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, y_not_isSquare⟩

example : ((encryptBit y false x : (ZMod 15)ˣ) : ZMod 15) = 4 := by decide
example : ((encryptBit y true x : (ZMod 15)ˣ) : ZMod 15) = 8 := by decide
example : decryptBit (N := 15) 3 5 4 = false := by decide
example : decryptBit (N := 15) 3 5 8 = true := by decide

/-- The general correctness theorem on this key. -/
example (b : Bool) (x : (ZMod 15)ˣ) :
    decryptBit 3 5 ((encryptBit y b x : (ZMod 15)ˣ) : ZMod 15) = b :=
  decryptBit_encryptBit isKey b x

/-- Residuosity reveals the bit. -/
example : ¬ IsSquare (encryptBit y true x) :=
  (isSquare_encryptBit_iff y_not_isSquare true x).not.mpr (by decide)

/-- The scheme with the point key distribution on `(y, (3, 5))` is correct. -/
example : (scheme 15 (PMF.pure (y, (3, 5)))).Correct :=
  scheme_correct 15 fun k hk => by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hk
    exact hk ▸ isKey

/-- The exact reduction, instantiated. -/
example {R : Type} (A : PubCPAAdversary Bool (ZMod 15)ˣ (ZMod 15)ˣ R) :
    pubCpaAdvantage (scheme 15 (PMF.pure (y, (3, 5)))) A =
      qrAdvantage (PMF.pure (y, (3, 5))) A.coins (reduction A) / 2 :=
  pubCpaAdvantage_eq_qrAdvantage _ A

/-- Semantic security per adversary, instantiated: guessing the plaintext bit itself. -/
example (coins : PMF Unit) (A : (ZMod 15)ˣ → (ZMod 15)ˣ → Unit → Unit → Bool) :
    winProb (SemanticSecurity.ssReal (scheme 15 (PMF.pure (y, (3, 5)))) coins A
        (PMF.pure true) (fun _ => ()) id) ≤
      winProb (SemanticSecurity.ssIdeal (fun _ => 0)
        (SemanticSecurity.simulator (scheme 15 (PMF.pure (y, (3, 5)))) coins (fun _ => false) A)
        (PMF.pure true) (fun _ => ()) id) +
        qrAdvantage (PMF.pure (y, (3, 5))) coins
          (SemanticSecurity.ssDistinguisher A (fun _ => ()) id true) :=
  winProb_ssReal_le_qrAdvantage _ coins A _ _ _

/-- The all-distinguisher hypothesis is vacuous: on this key it forces `ε ≥ 1`. -/
example (coins : PMF Unit) {ε : ℝ}
    (hqr : ∀ D : (ZMod 15)ˣ → (ZMod 15)ˣ → Unit → Bool,
      qrAdvantage (PMF.pure (y, (3, 5))) coins D ≤ ε) : 1 ≤ ε :=
  one_le_of_forall_qrAdvantage_le _ y_not_isSquare coins hqr

/-- Against unbounded distinguishers the scheme is not indistinguishable with error `1/2`. -/
example (coins : PMF Unit) :
    ¬ SemanticSecurity.IndSecure (scheme 15 (PMF.pure (y, (3, 5)))) (fun _ => 0) coins (1 / 2) :=
  not_indSecure_scheme _ y_not_isSquare coins (by norm_num)

/-! ### Messages of several bits -/

/-- The bitwise scheme on the key `(2, (3, 5))` is correct. -/
example : (schemeVec (N := 15) (ℓ := 3) (PMF.pure (y, (3, 5)))).Correct :=
  schemeVec_correct fun k hk => by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hk
    exact hk ▸ isKey

/-- Bitwise encryption of `(1, 0)` with randomness `(7, 7)` is `(8, 4)`. -/
example :
    (fun i => ((encryptVec y ![true, false] ![x, x] i : (ZMod 15)ˣ) : ZMod 15)) = ![8, 4] := by
  funext i; fin_cases i <;> decide

/-- The hybrid messages between `(0, 0, 0)` and `(1, 1, 1)`: after one step, `(1, 0, 0)`. -/
example : hybridMsg ![false, false, false] ![true, true, true] 1 = ![true, false, false] := by
  funext i; fin_cases i <;> rfl

/-- The hybrid bound with `ℓ = 3`. -/
example {R : Type} (coins : PMF R) (D : (ZMod 15)ˣ → (Fin 3 → (ZMod 15)ˣ) → R → Bool)
    (m m' : Fin 3 → Bool) {ε : ℝ}
    (hε : ∀ j : Fin 3, qrAdvantage (PMF.pure (y, (3, 5))) (hybridCoins coins)
      (hybridReduction D (hybridMsg m m' j) j) ≤ ε) :
    SemanticSecurity.indAdvantage (schemeVec (N := 15) (PMF.pure (y, (3, 5)))) coins D m m' ≤
      3 * ε := by
  have := indAdvantage_schemeVec_le_mul _ coins D m m' hε
  simpa using this

end Cslib.Crypto.GoldwasserMicaliTests
