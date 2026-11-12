/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games
public import CSLibExt.Crypto.PublicKey.ElGamal

/-!
# ElGamal is CPA-secure under DDH

**Generic step** (Katz and Lindell, Proposition 11.3), in `CSLibExt.Crypto.Framework.Games`:
the public-key CPA experiment with an encryption oracle (`PubOracleCPAAdversary`,
`pubOracleCpaAdvantage`) and the exact equality `pubCpaAdvantage_toEav` between the advantage of
a CPA adversary making at most `n` queries and that of the eavesdropper `A.toEav encR n` that
answers its queries from presampled coins (`OracleComp.runCoins` and `OracleComp.map_runCoins`,
in `CSLibExt.Crypto.Framework.Oracle`). This file only instantiates it for ElGamal.

**ElGamal.**
* `ElGamal.scheme q g`: ElGamal (Katz and Lindell, Construction 11.16) as a framework
  `PKEScheme`; `ElGamal.scheme_correct`.
* `ElGamal.pubCpaGame_eq_eavGame`: for a framework eavesdropper with uniform coins, the framework
  game `pubCpaGame` is the existing `ElGamal.eavGame` (so the Wave-2 migration of
  `ElGamal.eavGame` onto the framework is this equation).
* `ElGamal.cpaAdvantage_eq_ddhAdvantage` (**ElGamal is CPA-secure if DDH is hard**, Katz and
  Lindell, Theorem 11.18, exact form): for every adversary with an encryption oracle, uniform
  coins and at most `n` queries,
  `pubOracleCpaAdvantage (scheme q g) A = ddhAdvantage q g (reduction (toElGamal (A.toEav …)))`.
  It chains the generic step with the existing `ElGamal.eavAdvantage_eq_ddhAdvantage`, closing
  the CPA step that `CSLibExt.Crypto.PublicKey.ElGamal` leaves unformalized.
  `ElGamal.cpaAdvantage_le` is the bound form.

**Simplifications.** Encryption randomness is uniform on a finite type (`ZMod q`); the query
bound is structural (every path).

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 11.2.2 (Proposition 11.3), Section 11.4.1 (Construction 11.16, Theorem 11.18).
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey

open Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_prod uniformOfFintype_map_equiv)

/-! ### ElGamal -/

namespace ElGamal

variable {G : Type*} [CommGroup G] [Fintype G] {q : ℕ} [NeZero q] (g : G)

variable (q) in
/-- **ElGamal** (Katz and Lindell, Construction 11.16) as a framework `PKEScheme`: key generation
samples a uniform secret key `x` and publishes `g ^ x`; encryption samples uniform randomness
`y` and outputs `encrypt g h m y = (g ^ y, h ^ y * m)`. -/
noncomputable def scheme : PKEScheme G G (ZMod q) (G × G) where
  gen := (uniformOfFintype (ZMod q)).map fun x => (publicKey g x, x)
  enc h m := (uniformOfFintype (ZMod q)).map (encrypt g h m)
  dec x c := some (decrypt x c)

omit [Fintype G] in
/-- **Correctness of ElGamal** as a framework scheme (Katz and Lindell, Construction 11.16). -/
theorem scheme_correct : (scheme q g).Correct := by
  intro kp hkp m c hc
  simp only [scheme, PMF.support_map, Set.mem_image] at hkp hc
  obtain ⟨x, -, rfl⟩ := hkp
  obtain ⟨y, -, rfl⟩ := hc
  exact congrArg some (decrypt_encrypt g x y m)

/-- A framework eavesdropper against ElGamal, viewed as an `ElGamal.Adversary`. -/
def toElGamal {R : Type*} (B : PubCPAAdversary G G (G × G) R) : Adversary G R :=
  ⟨B.choose, B.guess⟩

omit [Fintype G] in
/-- For a framework eavesdropper with uniform coins, the framework game `PubK^eav` on
`ElGamal.scheme` is exactly the existing `ElGamal.eavGame`. -/
theorem pubCpaGame_eq_eavGame {R : Type*} [Fintype R] [Nonempty R]
    (B : PubCPAAdversary G G (G × G) R) (hB : B.coins = uniformOfFintype R) :
    pubCpaGame (scheme q g) B = eavGame q g (toElGamal B) := by
  -- both sides as one uniform map, over the samples in the framework's order `(b, x, r, y)`
  let e : Bool × ZMod q × R × ZMod q ≃ ZMod q × ZMod q × R × Bool :=
    { toFun := fun ω => (ω.2.1, ω.2.2.2, ω.2.2.1, ω.1)
      invFun := fun ω => (ω.2.2.2, ω.1, ω.2.2.1, ω.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [eavGame, ← uniformOfFintype_map_equiv e, PMF.map_comp, pubCpaGame, bitGame, fairCoin]
  simp only [pubCpaExp, hB, scheme, ← uniformOfFintype_prod, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  rfl

omit [Fintype G] in
/-- The framework advantage of a uniform-coin eavesdropper against `ElGamal.scheme` is the
existing `ElGamal.eavAdvantage`. -/
theorem pubCpaAdvantage_eq_eavAdvantage {R : Type*} [Fintype R] [Nonempty R]
    (B : PubCPAAdversary G G (G × G) R) (hB : B.coins = uniformOfFintype R) :
    pubCpaAdvantage (scheme q g) B = eavAdvantage q g (toElGamal B) := by
  rw [pubCpaAdvantage, pubCpaGame_eq_eavGame g B hB]
  rfl

/-- **ElGamal is CPA-secure if DDH is hard** (Katz and Lindell, Theorem 11.18), as an exact
equality: an adversary with an encryption oracle, uniform coins and at most `n` queries has
exactly the DDH advantage of the reduction applied to its oracle-simulating eavesdropper. -/
theorem cpaAdvantage_eq_ddhAdvantage (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) {R : Type*} [Fintype R] [Nonempty R] {n : ℕ}
    (A : PubOracleCPAAdversary G G (G × G) R) (hA : A.QueryBounded n)
    (hcoins : A.coins = uniformOfFintype R) :
    pubOracleCpaAdvantage (scheme q g) A =
      ddhAdvantage q g (reduction (toElGamal (A.toEav (encrypt (q := q) g) n))) := by
  rw [← pubCpaAdvantage_toEav (scheme q g) (encrypt g) (fun _ _ => rfl) A hA,
    pubCpaAdvantage_eq_eavAdvantage g _ (A.toEav_coins_uniform hcoins _ n)]
  exact eavAdvantage_eq_ddhAdvantage g hgen hcard _

/-- Any bound on the DDH advantage of the reduction bounds the CPA advantage of ElGamal. -/
theorem cpaAdvantage_le (hgen : ∀ x : G, x ∈ Subgroup.zpowers g) (hcard : Fintype.card G = q)
    {R : Type*} [Fintype R] [Nonempty R] {n : ℕ} (A : PubOracleCPAAdversary G G (G × G) R)
    (hA : A.QueryBounded n) (hcoins : A.coins = uniformOfFintype R) {ε : ℝ}
    (hε : ddhAdvantage q g (reduction (toElGamal (A.toEav (encrypt (q := q) g) n))) ≤ ε) :
    pubOracleCpaAdvantage (scheme q g) A ≤ ε :=
  (cpaAdvantage_eq_ddhAdvantage g hgen hcard A hA hcoins).le.trans hε

end ElGamal

end Cslib.Crypto.PublicKey
