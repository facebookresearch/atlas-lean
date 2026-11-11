/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.Commitment.HashCommitment
public import CSLibExt.Crypto.Protocols.Commitment.Pedersen
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Pedersen and hash-based commitments

**Pedersen** in `ZMod 5` written multiplicatively, with `g = ofAdd 1` and `h = ofAdd 3`, so the
discrete logarithm of `h` is `3`. The openings `(2, 4)` and `(1, 1)` both commit to `ofAdd 4`;
`extract` recovers `3` from them. The commitment distribution is uniform (each element has
probability `1/5`). Parameter generation samples `x` from the four units of `ZMod 5`, so it
never produces `h = 1`, and every generated `h` gives a perfectly hiding scheme. A constant
adversary that outputs these two openings wins the binding game with probability exactly `1/4`,
the probability that the unit `x` is `3`, and its reduction wins the matching discrete-logarithm
game with the same probability `1/4`.

**Hash commitment** with the toy hash `H (r, m) = r + m` on `ZMod 5`: the openings `(2, 1)` and
`(1, 2)` both commit to `3`, which is a collision `(1, 2), (2, 1)`. This hash is perfectly hiding
(every nonce digest is uniform) and a constant adversary breaks binding with probability `1`. The
games take an arbitrary key distribution and arbitrary adversary coins: with the keyed hash
`keyedHash true = addHash`, `keyedHash false (r, m) = r + 2 m`, the same adversary wins with
probability `1` under the point-mass key `true` and `1/2` under a uniform key, and a collision
finder with coins in the infinite type `ℕ` is allowed. An injective hash gives a perfectly binding
scheme. With a one-element nonce space and `D = Bool`,
`NonceClose` fails below `1 / 2` for every hash, even the constant hash, whose scheme is perfectly
hiding: `NonceClose` is strictly stronger than hiding and is not implied by random-oracle hiding.
-/

@[expose] public section

namespace Cslib.Crypto.CommitmentWave2Tests

open Cslib.Crypto.PublicKey Cslib.Crypto.Framework Cslib.Crypto.Protocols.Commitment

/-! ### Pedersen -/

section PedersenTests

open Pedersen

/-- `ZMod 5`, written multiplicatively. -/
abbrev G5 := Multiplicative (ZMod 5)

/-- The first generator. -/
abbrev g : G5 := Multiplicative.ofAdd 1

/-- The second generator, `h = g ^ 3`. -/
abbrev h : G5 := Multiplicative.ofAdd 3

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem g_pow : g ^ 5 = 1 := by decide

theorem card_G5 : Fintype.card G5 = 5 := rfl

theorem dlog_h : gpow g (3 : ZMod 5) = h := by decide

example : commitValue g h (2 : ZMod 5) 4 = Multiplicative.ofAdd 4 := by decide

example : commitValue g h (1 : ZMod 5) 1 = Multiplicative.ofAdd 4 := by decide

example : (scheme 5 g h).Accepts 2 (Multiplicative.ofAdd 4) 4 := accepts_iff.mpr (by decide)

example : ¬ (scheme 5 g h).Accepts 2 (Multiplicative.ofAdd 4) 3 := by
  rw [accepts_iff]; decide

/-- Every commitment has probability `1/5`, whatever the message. -/
example : (scheme 5 g h).commitmentDist 2 (Multiplicative.ofAdd 4) = 5⁻¹ := by
  rw [commitmentDist_eq_uniform g
    (fun _ => mem_zpowers_of_prime_card (Nat.card_eq_fintype_card.trans card_G5) (by decide))
    card_G5, Cslib.Probability.PMF.uniformOfFintype_apply, card_G5]
  rfl

example : (scheme 5 g h).PerfectlyHiding :=
  perfectlyHiding_of_prime_card g (by decide) card_G5

example : ¬ (scheme 5 g h).PerfectlyBinding :=
  not_perfectlyBinding g
    (fun _ => mem_zpowers_of_prime_card (Nat.card_eq_fintype_card.trans card_G5) (by decide))
    card_G5 (by norm_num)

/-- The extractor applied to the two openings `(2, 4)` and `(1, 1)` is `(2 - 1) / (1 - 4) = 3`. -/
theorem extract_eq_three : extract (2 : ZMod 5) 4 1 1 = 3 := by
  rw [extract, show (1 : ZMod 5) - 4 = 2 by decide, ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide)]
  decide

example : gpow g (extract (2 : ZMod 5) 4 1 1) = h :=
  extract_spec g_pow (by decide) (by decide) (c := Multiplicative.ofAdd 4) (by decide)
    (by decide) (by decide)

/-- An experiment against an adversary with a single coin is a map of the key distribution. -/
theorem bind_map_pure_unit {K : Type*} (gen : PMF K) (f : K → Unit → Bool) :
    (gen.bind fun k => (PMF.pure ()).map (f k)) = gen.map fun k => f k () := by
  simp only [PMF.pure_map]
  rfl

/-- Counting units of `ZMod 5` with a property reduces to counting nonzero residues, which
`decide` can evaluate. -/
theorem card_filter_units_five (P : (ZMod 5)ˣ → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun a : ZMod 5 => ∃ h : a ≠ 0, P (Units.mk0 a h)).card := by
  refine Finset.card_bij (fun x _ => (x : ZMod 5)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨x.ne_zero, by simpa using hx⟩
  · intro x _ y _ hxy
    exact Units.ext hxy
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨h0, hP⟩ := ha
    exact ⟨Units.mk0 a h0, by simpa using hP, rfl⟩

/-- `ZMod 5` has four units. -/
theorem card_units_five : Fintype.card (ZMod 5)ˣ = 4 := by
  rw [← Finset.card_univ, ← Finset.filter_true_of_mem (s := Finset.univ) (p := fun _ => True)
    (fun _ _ => trivial), card_filter_units_five]
  decide

/-- Parameter generation never produces `h = 1`. -/
example : (1 : G5) ∉ (paramGen 5 g).support := fun h1 =>
  ne_one_of_mem_support_paramGen g_pow (by decide) h1 rfl

/-- `h = g ^ 3` is a possible parameter. -/
example : h ∈ (paramGen 5 g).support := by
  rw [paramGen, PMF.mem_support_map_iff]
  refine ⟨ZMod.unitOfCoprime 3 (by norm_num), ?_, dlog_h⟩
  simp [PMF.mem_support_iff]

/-- Every generated parameter gives a perfectly hiding scheme. -/
example {h' : G5} (hh : h' ∈ (paramGen 5 g).support) : (scheme 5 g h').PerfectlyHiding :=
  perfectlyHiding_of_mem_support card_G5 (by decide) hh

/-- A binding adversary that ignores `h` and always outputs the two openings above. -/
noncomputable def constAdv : BindingAdversary G5 (ZMod 5) G5 (ZMod 5) Unit where
  coins := PMF.pure ()
  run _ _ := (Multiplicative.ofAdd 4, (2, 4), (1, 1))

/-- It wins exactly when `h = g ^ 3`, i.e. for one of the four units: probability `1/4`. Over
all five exponents it would be `1/5`. -/
theorem bindingAdvantage_constAdv : Pedersen.bindingAdvantage 5 g constAdv = 1 / 4 := by
  rw [Pedersen.bindingAdvantage, Pedersen.bindingGame, Protocols.Commitment.bindingGame, paramGen,
    PMF.bind_map, Function.comp_def, constAdv, bind_map_pure_unit, winProb_map_uniform,
    card_units_five, card_filter_units_five]
  norm_num
  decide

/-- Its reduction always outputs `extract 2 4 1 1 = 3`, so it wins the discrete-logarithm game
with the same probability `1/4`. -/
theorem dlAdvantage_reduction_constAdv : dlAdvantage 5 g (reduction constAdv) = 1 / 4 := by
  rw [dlAdvantage, dlGame, paramGen, PMF.bind_map, Function.comp_def, reduction, constAdv,
    bind_map_pure_unit]
  simp only [extract_eq_three]
  rw [winProb_map_uniform, card_units_five, card_filter_units_five]
  norm_num
  decide

example : Pedersen.bindingAdvantage 5 g constAdv ≤ dlAdvantage 5 g (reduction constAdv) :=
  bindingAdvantage_le g_pow (by decide) constAdv

end PedersenTests

/-! ### Hash-based commitments -/

section HashTests

open HashCommitment

/-- A toy, unkeyed hash: `H (r, m) = r + m`. -/
def addHash : Unit → ZMod 5 × ZMod 5 → ZMod 5 := fun _ x => x.1 + x.2

example : commitValue addHash () (2 : ZMod 5) (1 : ZMod 5) = 3 := by decide

example : commitValue addHash () (1 : ZMod 5) (2 : ZMod 5) = 3 := by decide

example : IsCollision addHash () ((1 : ZMod 5), (2 : ZMod 5)) (2, 1) :=
  collision_of_openings (c := 3) (by decide) (by decide) (by decide)

example : ¬ IsCollision addHash () ((1 : ZMod 5), (2 : ZMod 5)) (1, 2) := by decide

example : ¬ IsCollision addHash () ((1 : ZMod 5), (2 : ZMod 5)) (1, 3) := by decide

/-- Every nonce digest of `addHash` is uniform. -/
theorem nonceDigest_addHash (m : ZMod 5) :
    nonceDigest addHash () m = Cslib.Probability.PMF.uniformOfFintype (ZMod 5) :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.addRight m)

theorem addHash_nonceClose : NonceClose addHash () 0 := fun m => by
  rw [nonceDigest_addHash]
  exact Cslib.Probability.PMF.StatisticallyClose.refl _

example : (scheme addHash ()).PerfectlyHiding := perfectlyHiding addHash_nonceClose

example : (scheme addHash ()).StatisticallyHiding 0 := by
  simpa using statisticallyHiding addHash_nonceClose

example : (scheme addHash ()).commitmentDist 2 3 = 5⁻¹ := by
  rw [commitmentDist_eq, nonceDigest_addHash, Cslib.Probability.PMF.uniformOfFintype_apply]
  rfl

/-! `NonceClose` fixes the key and randomizes only the nonce, so random-oracle hiding does not
imply it: with a one-element nonce space and `D = Bool`, every nonce digest is a point mass, at
statistical distance exactly `1 / 2` from uniform, whatever the hash. -/

section NonceCloseCounterexample

open scoped Cslib.Probability.PMF

/-- With a one-element nonce space, the nonce digest is a point mass. -/
theorem nonceDigest_unit {K M : Type*} (H : K → Unit × M → Bool) (s : K) (m : M) :
    nonceDigest H s m = PMF.pure (H s ((), m)) := by
  ext b
  by_cases hb : b = H s ((), m)
  · subst hb; simp [nonceDigest, PMF.map_apply]
  · simp [nonceDigest, PMF.map_apply, PMF.pure_apply, hb]

/-- A point mass on `Bool` is at statistical distance `1 / 2` from uniform. -/
theorem dist_pure_uniform_bool (b : Bool) :
    dist (PMF.pure b) (Cslib.Probability.PMF.uniformOfFintype Bool) = 1 / 2 := by
  rw [Cslib.Probability.PMF.dist_eq]
  cases b <;> norm_num [Fintype.sum_bool, PMF.pure_apply]

/-- No hash with a one-element nonce space and `D = Bool` satisfies `NonceClose` below `1 / 2`,
for any key, including hashes that a random oracle could output. -/
theorem not_nonceClose_unit_bool {K M : Type*} [Nonempty M] (H : K → Unit × M → Bool) (s : K)
    {ε : NNReal} (hε : (ε : ℝ) < 1 / 2) : ¬ NonceClose H s ε := fun h => by
  have := h (Classical.arbitrary M)
  rw [Cslib.Probability.PMF.StatisticallyClose, nonceDigest_unit, dist_pure_uniform_bool] at this
  linarith

/-- The bound `1 / 2` is attained: every such hash satisfies `NonceClose` at `1 / 2`. -/
theorem nonceClose_unit_bool_half {K M : Type*} (H : K → Unit × M → Bool) (s : K) :
    NonceClose H s (1 / 2) := fun m => by
  rw [Cslib.Probability.PMF.StatisticallyClose, nonceDigest_unit, dist_pure_uniform_bool]
  norm_num

/-- The message-revealing hash `H ((), m) = m` on `Bool`. -/
def revealHash : Unit → Unit × Bool → Bool := fun _ x => x.2

example : ¬ NonceClose revealHash () (1 / 4) :=
  not_nonceClose_unit_bool revealHash () (by norm_num)

example : NonceClose revealHash () (1 / 2) := nonceClose_unit_bool_half revealHash ()

/-- Even the constant hash, whose commitments reveal nothing, fails `NonceClose` below `1 / 2`. -/
example : ¬ NonceClose (fun (_ : Unit) (_ : Unit × Bool) => true) () (49 / 100) :=
  not_nonceClose_unit_bool _ () (by norm_num)

example : (scheme (fun (_ : Unit) (_ : Unit × Bool) => true) ()).PerfectlyHiding := by
  rw [Scheme.perfectlyHiding_iff_statisticallyHiding_zero]
  intro m₀ m₁
  rw [commitmentDist_eq, commitmentDist_eq, nonceDigest_unit, nonceDigest_unit]
  exact Cslib.Probability.PMF.StatisticallyClose.refl _

end NonceCloseCounterexample

/-- A binding adversary that always opens `3` as `(2, 1)` and as `(1, 2)`. -/
noncomputable def constHashAdv {K : Type*} :
    BindingAdversary K (ZMod 5) (ZMod 5) (ZMod 5) Unit where
  coins := PMF.pure ()
  run _ _ := (3, (2, 1), (1, 2))

theorem bindingAdvantage_constHashAdv :
    bindingAdvantage (PMF.pure ()) (scheme addHash) constHashAdv = 1 := by
  rw [bindingAdvantage, bindingGame, PMF.pure_bind, constHashAdv, PMF.pure_map, winProb_pure]
  split_ifs with hw
  · rfl
  · exact (hw (by decide)).elim

example : 1 ≤ collAdvantage (PMF.pure ()) addHash (reduction constHashAdv) :=
  bindingAdvantage_constHashAdv ▸ bindingAdvantage_le _ addHash constHashAdv

/-- A keyed hash: `addHash` under key `true`, and `r + 2 m` under key `false`. -/
def keyedHash : Bool → ZMod 5 × ZMod 5 → ZMod 5 := fun b x => if b then x.1 + x.2 else x.1 + 2 * x.2

/-- Under the point-mass key `true` the adversary always wins. -/
example : bindingAdvantage (PMF.pure true) (scheme keyedHash) constHashAdv = 1 := by
  rw [bindingAdvantage, bindingGame, PMF.pure_bind, constHashAdv, PMF.pure_map, winProb_pure]
  split_ifs with hw
  · rfl
  · exact (hw (by decide)).elim

/-- Under a uniform key it wins only for the key `true`: probability `1/2`. -/
theorem bindingAdvantage_keyedHash_uniform :
    bindingAdvantage (Cslib.Probability.PMF.uniformOfFintype Bool) (scheme keyedHash)
      constHashAdv = 1 / 2 := by
  rw [bindingAdvantage, bindingGame, constHashAdv, bind_map_pure_unit, winProb_map_uniform]
  norm_num
  decide

example : 1 / 2 ≤ collAdvantage (Cslib.Probability.PMF.uniformOfFintype Bool) keyedHash
    (reduction constHashAdv) :=
  bindingAdvantage_keyedHash_uniform ▸ bindingAdvantage_le _ keyedHash constHashAdv

/-- A collision finder with coins in the infinite type `ℕ`: on coin `n` it outputs the collision
`(1, 2), (2, 1)` of `addHash` shifted by `n` in the first coordinate. -/
noncomputable def natCollFinder : CollFinder Unit (ZMod 5 × ZMod 5) ℕ where
  coins := PMF.pure 7
  run _ n := ((1 + n, 2), (2 + n, 1))

example : collAdvantage (PMF.pure ()) addHash natCollFinder = 1 := by
  rw [collAdvantage, collGame, PMF.pure_bind, natCollFinder, PMF.pure_map, winProb_pure]
  split_ifs with hw
  · rfl
  · exact (hw (by decide)).elim

/-- An injective hash: the identity on `ZMod 5 × Bool`. -/
example : (scheme (fun (_ : Unit) (x : ZMod 5 × Bool) => x) ()).PerfectlyBinding :=
  perfectlyBinding_of_injective Function.injective_id

end HashTests

end Cslib.Crypto.CommitmentWave2Tests
