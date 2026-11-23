/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Asymptotic
public import CSLibExtTest.Crypto.Framework.GamesTests

/-!
# Tests for the asymptotic bridge

* `NegligibleAdv`: `0` and a function that is nonzero only at `n = 0` are negligible, and so is
  their sum; the constant `1/2` is not.
* Asymptotic security of constant families of toy schemes: the one-time pad is secure against
  eavesdropper families, the identity scheme is not, and neither the identity scheme nor the
  one-time pad is `PolyQueryCPASecure` (polynomial-query adversaries, nonempty coin family `Unit`),
  witnessed by the adversaries of `GamesTests`; likewise the one-time pad is not
  `PolyQueryCCASecure`, the key-as-tag MAC is not `PolyQueryMACSecure`, the key-as-signature scheme
  is not `PolyQuerySigSecure`, and the identity public-key scheme is not `PubCPASecure`.
* Why the instances require nonempty coin and message types: over adversaries with coin type
  `Empty` there are no adversaries, so `AsymptoticallySecure` holds even for the identity scheme;
  over the message type `Empty` a scheme exists, there are again no CPA adversaries, and
  `AsymptoticallySecure` holds vacuously. The instances' hypothesis `∀ n, Nonempty (M n)` cannot be
  met by `Empty`, and with `Bool` messages and `Unit` coins each query-bearing notion has an
  admissible adversary family.
* `invertGame` for a constant function: every inverter succeeds, so `invertSucc = 1`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Asymptotic

open Cslib.Crypto.Framework Cslib.Crypto.FrameworkTests.Games Cslib.Complexity.Classes

example : NegligibleAdv fun _ => 0 := negligibleAdv_zero

/-- A function that is `1` at `n = 0` and `0` elsewhere is negligible. -/
theorem negligibleAdv_indicator_zero : NegligibleAdv fun n => if n = 0 then 1 else 0 :=
  ⟨fun n => if n = 0 then 1 else 0,
    fun _ => ⟨1, fun n hn => by
      simp only [show n ≠ 0 by omega, ↓reduceIte]
      positivity⟩,
    fun n => by dsimp only; split_ifs <;> simp⟩

example : NegligibleAdv ((fun n => if n = 0 then (1 : ℝ) else 0) + fun _ => 0) :=
  negligibleAdv_indicator_zero.add negligibleAdv_zero

example : ¬ NegligibleAdv fun _ => (1 / 2 : ℝ) := not_negligibleAdv_const (by norm_num)

/-- Eavesdropper families: no queries at any security parameter. -/
def Eavesdroppers {M C R : ℕ → Type} (A : (n : ℕ) → CPAAdversary (M n) (C n) (R n)) : Prop :=
  ∀ n, (A n).QueryBounded 0

/-- The one-time pad on a fixed finite group is asymptotically secure against eavesdroppers. -/
example (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    AsymptoticallySecure (Adv := fun _ => CPAAdversary G G Unit)
      (fun _ A => cpaAdvantage (otp G) A) Eavesdroppers := fun A hA =>
  negligibleAdv_zero.mono fun n => (otp_cpaAdvantage_eq_zero G (A n) (hA n)).le

/-- The identity scheme is not asymptotically secure against eavesdroppers. -/
example : ¬ AsymptoticallySecure (Adv := fun _ => CPAAdversary Bool Bool Unit)
    (fun _ A => cpaAdvantage idScheme A) Eavesdroppers := fun h =>
  not_negligibleAdv_const (δ := 1 / 2) (by norm_num) <| by
    simpa [idScheme_cpaAdvantage] using h (fun _ => idAdversary) fun _ => idAdversary_queryBounded

/-- The identity scheme is not `PolyQueryCPASecure`: its eavesdropper makes `0 = p(n)` queries for
the zero polynomial. -/
example : ¬ PolyQueryCPASecure (fun _ => idScheme) (fun _ => Unit) := fun h =>
  not_negligibleAdv_const (δ := 1 / 2) (by norm_num) <| by
    simpa [idScheme_cpaAdvantage] using
      h (fun _ => idAdversary) ⟨0, fun _ => by simpa using idAdversary_queryBounded⟩

/-- The one-time pad is not `PolyQueryCPASecure`: the one-query attacker makes `1 = p(n)` queries
for the constant polynomial `1`. -/
example : ¬ PolyQueryCPASecure (fun _ => otp (Multiplicative (ZMod 2))) (fun _ => Unit) := fun h =>
  not_negligibleAdv_const (δ := 1 / 2) (by norm_num) <| by
    simpa [otpAttacker_cpaAdvantage _ (show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide)] using
      h (fun _ => otpAttacker _ (Multiplicative.ofAdd 1))
        ⟨1, fun _ => by simpa using otpAttacker_queryBounded _ _⟩

/-- The one-time pad is not `PolyQueryCCASecure`: one decryption query on the mauled challenge
(constant polynomial `1`) wins with advantage `1/2`. -/
example : ¬ PolyQueryCCASecure (fun _ => otp (Multiplicative (ZMod 2))) (fun _ => Unit) :=
  fun h => not_negligibleAdv_const (δ := 1 / 2) (by norm_num) <| by
    simpa [otpCCAAttacker_ccaAdvantage _ (show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 by decide)]
      using h (fun _ => otpCCAAttacker _ (Multiplicative.ofAdd 1))
        ⟨1, fun _ => by simpa using otpCCAAttacker_queryBounded _ _⟩

/-- The key-as-tag MAC is not `PolyQueryMACSecure`: one tag query gives a forgery with
probability `1`. -/
example : ¬ PolyQueryMACSecure (fun _ => keyMAC) (fun _ => Unit) := fun h =>
  not_negligibleAdv_const (δ := 1) (by norm_num) <| by
    simpa [macAdvantage_freshForger] using
      h (fun _ => freshForger) ⟨1, fun _ => by simpa using freshForger_queryBounded⟩

/-- The key-as-signature scheme is not `PolyQuerySigSecure`: one signing query gives a forgery
with probability `1`. -/
example : ¬ PolyQuerySigSecure (fun _ => keySig) (fun _ => Unit) := fun h =>
  not_negligibleAdv_const (δ := 1) (by norm_num) <| by
    simpa [sigAdvantage_freshSigForger] using
      h (fun _ => freshSigForger) ⟨1, fun _ => by simpa using freshSigForger_queryBounded⟩

/-- The identity public-key scheme is not `PubCPASecure` with every adversary family admissible:
its adversary has advantage `1/2`. -/
example : ¬ PubCPASecure (fun _ => idPKE) (fun _ => Unit) fun _ => True := fun h =>
  not_negligibleAdv_const (δ := 1 / 2) (by norm_num) <| by
    simpa [idPKE_pubCpaAdvantage] using h (fun _ => idPubAdversary) trivial

/-- With coin type `Empty` there is no adversary (no `PMF Empty` exists), so asymptotic security
holds vacuously, even for the identity scheme that the previous examples show insecure. This is
why the `PolyQuery…Secure` instances require `∀ n, Nonempty (R n)`. -/
example : AsymptoticallySecure (Adv := fun _ => CPAAdversary Bool Bool Empty)
    (fun _ A => cpaAdvantage idScheme A) (PolyQueryBounded fun _ q A => A.QueryBounded q) :=
  fun A _ => ((A 0).coins.support_nonempty.some).elim

/-- A private-key scheme over the empty message space. -/
noncomputable def emptyMsgScheme : SymmEncScheme Empty Unit Empty where
  gen := PMF.pure ()
  enc _ m := m.elim
  dec _ _ := none

/-- Over the empty message space there is no CPA adversary: the first stage cannot query (there
is no message to encrypt) and cannot return two challenge messages. -/
theorem isEmpty_cpaAdversary_emptyMsg : IsEmpty (CPAAdversary Empty Empty Unit) :=
  ⟨fun A => by
    cases h : A.run () with
    | pure out => exact out.1.1.elim
    | liftBind a _ => exact a.elim⟩

/-- Hence asymptotic security of the empty-message scheme holds vacuously, with a nonempty coin
type. This is why the `PolyQuery…Secure` instances also require `∀ n, Nonempty (M n)`. -/
example : AsymptoticallySecure (Adv := fun _ => CPAAdversary Empty Empty Unit)
    (fun _ A => cpaAdvantage emptyMsgScheme A) (PolyQueryBounded fun _ q A => A.QueryBounded q) :=
  fun A _ => isEmpty_cpaAdversary_emptyMsg.elim (A 0)

/-- The message hypothesis of the instances is unsatisfiable for the empty-message family, so
`PolyQueryCPASecure (fun _ => emptyMsgScheme) (fun _ => Unit)` cannot be stated. -/
example : ¬ ∀ n : ℕ, Nonempty ((fun _ : ℕ => Empty) n) := fun h => isEmptyElim (h 0).some

/-- With `Bool` messages and `Unit` coins each query-bearing notion has an admissible adversary
family, so none of them holds vacuously. -/
example : ∃ A : (n : ℕ) → CPAAdversary Bool Bool Unit,
    PolyQueryBounded (fun _ q A => CPAAdversary.QueryBounded q A) A :=
  exists_polyQueryBounded_cpa (M := fun _ => Bool) (C := fun _ => Bool) (R := fun _ => Unit)

example : ∃ A : (n : ℕ) → CCAAdversary Bool Bool Unit,
    PolyQueryBounded (fun _ q A => CCAAdversary.QueryBounded q A) A :=
  exists_polyQueryBounded_cca (M := fun _ => Bool) (C := fun _ => Bool) (R := fun _ => Unit)

example : ∃ A : (n : ℕ) → MACForger Bool Bool Unit,
    PolyQueryBounded (fun _ q A => MACForger.QueryBounded q A) A :=
  exists_polyQueryBounded_mac (M := fun _ => Bool) (T := fun _ => Bool) (R := fun _ => Unit)

example : ∃ A : (n : ℕ) → SigForger Bool Unit Bool Unit,
    PolyQueryBounded (fun _ q A => SigForger.QueryBounded q A) A :=
  exists_polyQueryBounded_sig (M := fun _ => Bool) (PK := fun _ => Unit) (S := fun _ => Bool)
    (R := fun _ => Unit)

/-- The forger of `exists_polyQueryBounded_mac` needs no inhabitant of the tag type: over an empty
tag type a one-query forger still exists. -/
example : ∃ A : MACForger Bool Empty Unit, A.QueryBounded 1 := MACForger.exists_queryBounded_one

example : Nonempty (PubCPAAdversary Bool Unit Bool Unit) := PubCPAAdversary.nonempty

/-- A constant function is inverted by every inverter. -/
theorem winProb_invertGame_const (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) :
    winProb (invertGame (fun _ _ => []) inv n m) = 1 := by
  simp only [invertGame, decide_true]
  rw [show (fun _ : (Fin n → Bool) × (Fin m → Bool) => true) = Function.const _ true from rfl,
    PMF.map_const]
  simp

example (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) :
    (invertSucc (fun _ _ => []) inv n m : ℝ) = 1 := by
  rw [← winProb_invertGame, winProb_invertGame_const]

end Cslib.Crypto.FrameworkTests.Asymptotic
