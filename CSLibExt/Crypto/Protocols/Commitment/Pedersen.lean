/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Protocols.Commitment.Binding
public import CSLibExt.Crypto.PublicKey.DiffieHellman
public import Mathlib.Algebra.Field.ZMod

/-!
# Pedersen commitments: perfect hiding, and binding from the discrete logarithm

In a commutative group `G` with public elements `g` and `h` and exponents in `ZMod q` (`gpow`),
the **Pedersen commitment** to a message `m` with opening `r` is `g ^ m * h ^ r`. It is packaged
as a CSLib `Cslib.Crypto.Protocols.Commitment.Scheme` with uniform `r`.

* `commitmentDist_eq_uniform`, `perfectlyHiding` (**perfect hiding**): if `h` generates `G` and
  `|G| = q`, every message has the uniform commitment distribution on `G`, so the scheme is
  `PerfectlyHiding`. `perfectlyHiding_of_prime_card` is the prime-order special case with
  `h ≠ 1`.
* `not_perfectlyBinding`: hence, for `1 < q`, Pedersen commitments are not perfectly binding
  (CSLib's hiding-binding trade-off); binding is computational.
* `extract_spec` (**binding extraction**): for `q` prime, `g ^ q = h ^ q = 1` and `g ≠ 1`, two
  openings `(m, r)` and `(m', r')` of one commitment with `m ≠ m'` yield the discrete logarithm
  `extract m r m' r' = (m - m') / (r' - r)` of `h` to base `g`.
* `paramGen` (**parameter generation**): `h = g ^ x` for a uniform unit `x` of `ZMod q`; for `q`
  prime these are exactly the nonzero exponents, so `h ≠ 1`. `perfectlyHiding_of_mem_support`:
  every generated `h` gives a perfectly hiding scheme when `|G| = q` is prime and `g ≠ 1`.
* `bindingAdvantage_le` (**computational binding from DL**): in the binding experiment
  `bindingGame` (the generic `Commitment.bindingGame` with key generation `paramGen`), where the
  adversary, with arbitrary coins, outputs a commitment with two openings, the success probability
  is at most the discrete-logarithm advantage `dlAdvantage` of `reduction A`, which runs on the
  same `h` and the same coins.

The discrete-logarithm experiment `dlGame` is a minimal local definition that samples `h` from
the same distribution `paramGen` as the binding experiment (so the bound needs no conditioning
factor). It differs from Katz and Lindell's experiment (Section 8.3.2), which samples `h`
uniformly from all of `G`, by excluding `h = 1`. Wave 3: unify with the Wave 1 Assumptions DLP
game, with the conditioning factor `q / (q - 1)` for prime `q`.

## References

* T. P. Pedersen, *Non-interactive and information-theoretic secure verifiable secret sharing*,
  CRYPTO 1991.
* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.6.5 (commitment schemes: hiding and binding) and Section 8.3.2 (the
  discrete-logarithm experiment).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.Commitment.Pedersen

open Cslib.Crypto.PublicKey Cslib.Crypto.Framework

variable {G : Type*} [CommGroup G] {q : ℕ}

/-- The Pedersen commitment value `g ^ m * h ^ r` (Pedersen 1991). -/
def commitValue (g h : G) (m r : ZMod q) : G := gpow g m * gpow h r

/-! ### The scheme and perfect hiding -/

section Scheme

variable (q) [NeZero q] [DecidableEq G]

/-- The Pedersen commitment scheme with public parameters `g` and `h`: commit to `m` by sampling
a uniform opening `r` and publishing `g ^ m * h ^ r`; verification recomputes it. -/
noncomputable def scheme (g h : G) : Scheme (ZMod q) G (ZMod q) where
  commit m := (Cslib.Probability.PMF.uniformOfFintype (ZMod q)).map
    fun r => (commitValue g h m r, r)
  verify m c r := decide (commitValue g h m r = c)
  correct m c r hmem := by
    simp only [PMF.support_map, Set.mem_image, Prod.mk.injEq] at hmem
    obtain ⟨r', -, rfl, rfl⟩ := hmem
    simp

variable {q}

/-- An opening is accepted exactly when it recomputes the commitment. -/
@[simp]
theorem accepts_iff {g h : G} {m r : ZMod q} {c : G} :
    (scheme q g h).Accepts m c r ↔ commitValue g h m r = c := by
  simp [Scheme.Accepts, scheme]

/-- If `h` generates `G` and `|G| = q`, the commitment to any message is uniform on `G`: the
opening `r` is a one-time pad on the exponent of `h`. -/
theorem commitmentDist_eq_uniform [Fintype G] (g : G) {h : G}
    (hgen : ∀ x : G, x ∈ Subgroup.zpowers h) (hcard : Fintype.card G = q) (m : ZMod q) :
    (scheme q g h).commitmentDist m = Cslib.Probability.PMF.uniformOfFintype G := by
  let e : ZMod q ≃ G := (gpowEquiv hgen hcard).trans (Equiv.mulLeft (gpow g m))
  have he : (Prod.fst ∘ fun r => (commitValue g h m r, r)) = ⇑e := by
    funext r
    simp [e, commitValue, Equiv.coe_mulLeft]
  rw [Scheme.commitmentDist, scheme, PMF.map_comp, he,
    Cslib.Probability.PMF.uniformOfFintype_map_equiv]

/-- **Perfect hiding of Pedersen commitments**: if `h` generates `G` and `|G| = q`, all messages
have the same commitment distribution. -/
theorem perfectlyHiding [Fintype G] (g : G) {h : G} (hgen : ∀ x : G, x ∈ Subgroup.zpowers h)
    (hcard : Fintype.card G = q) : (scheme q g h).PerfectlyHiding := fun m₀ m₁ => by
  rw [commitmentDist_eq_uniform g hgen hcard, commitmentDist_eq_uniform g hgen hcard]

/-- Perfect hiding in a group of prime order `q`, for any `h ≠ 1`. -/
theorem perfectlyHiding_of_prime_card [Fintype G] [Fact q.Prime] (g : G) {h : G} (hh : h ≠ 1)
    (hcard : Fintype.card G = q) : (scheme q g h).PerfectlyHiding :=
  perfectlyHiding g (fun _ => mem_zpowers_of_prime_card (Nat.card_eq_fintype_card.trans hcard) hh)
    hcard

/-- Pedersen commitments with at least two messages are not perfectly binding: perfect hiding
and perfect binding exclude each other (CSLib's
`Scheme.subsingleton_of_perfectlyHiding_of_perfectlyBinding`). -/
theorem not_perfectlyBinding [Fintype G] (g : G) {h : G} (hgen : ∀ x : G, x ∈ Subgroup.zpowers h)
    (hcard : Fintype.card G = q) (hq : 1 < q) : ¬ (scheme q g h).PerfectlyBinding := fun hbind => by
  have := (scheme q g h).subsingleton_of_perfectlyHiding_of_perfectlyBinding
    (perfectlyHiding g hgen hcard) hbind
  have h01 : (0 : ZMod q) ≠ 1 := by
    have : Fact (1 < q) := ⟨hq⟩
    exact zero_ne_one
  exact h01 (Subsingleton.elim _ _)

end Scheme

/-! ### Binding extraction -/

/-- The discrete-logarithm extractor from two openings: `(m - m') / (r' - r)`. -/
def extract (m r m' r' : ZMod q) : ZMod q := (m - m') * (r' - r)⁻¹

private theorem gpow_sub [NeZero q] {g : G} (hg : g ^ q = 1) (a b : ZMod q) :
    gpow g (a - b) = gpow g a * (gpow g b)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← gpow_add hg, sub_add_cancel]

/-- For `q` prime and `g ≠ 1` with `g ^ q = 1`, `gpow g` has trivial kernel. -/
theorem eq_zero_of_gpow_eq_one [Fact q.Prime] {g : G} (hg : g ^ q = 1) (hg1 : g ≠ 1)
    {a : ZMod q} (ha : gpow g a = 1) : a = 0 := by
  have hord : orderOf g = q := by
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hg) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have hdvd : orderOf g ∣ a.val := orderOf_dvd_of_pow_eq_one (by simpa only [gpow] using ha)
  rw [hord] at hdvd
  exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt a))

/-- **Binding extraction**: for `q` prime, `g ^ q = h ^ q = 1` and `g ≠ 1`, two openings of the
same Pedersen commitment to different messages reveal the discrete logarithm of `h` to base
`g`. -/
theorem extract_spec [Fact q.Prime] {g h : G} (hg : g ^ q = 1) (hg1 : g ≠ 1) (hh : h ^ q = 1)
    {c : G} {m r m' r' : ZMod q} (hne : m ≠ m') (h₁ : commitValue g h m r = c)
    (h₂ : commitValue g h m' r' = c) : gpow g (extract m r m' r') = h := by
  have hsub : gpow g (m - m') = gpow h (r' - r) := by
    rw [gpow_sub hg, gpow_sub hh, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    have := h₁.trans h₂.symm
    rw [commitValue, commitValue] at this
    rw [this, mul_comm]
  have hrr : r' - r ≠ 0 := by
    intro h0
    rw [h0, gpow_zero] at hsub
    exact hne (sub_eq_zero.mp (eq_zero_of_gpow_eq_one hg hg1 hsub))
  have hone : gpow h (1 : ZMod q) = h := by rw [gpow, ZMod.val_one, pow_one]
  rw [extract, gpow_mul hg, hsub, ← gpow_mul hh,
    ZMod.mul_inv_of_unit _ (isUnit_iff_ne_zero.mpr hrr), hone]

/-! ### Parameter generation -/

section Params

variable [NeZero q]

variable (q) in
/-- Pedersen parameter generation: `h = g ^ x` for a uniform unit `x` of `ZMod q`. For `q` prime
the units are exactly the nonzero exponents, so `h ≠ 1` whenever `g` has order `q`
(`ne_one_of_mem_support_paramGen`), which is the generator condition of perfect hiding. -/
noncomputable def paramGen (g : G) : PMF G :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod q)ˣ).map fun x : (ZMod q)ˣ => gpow g (x : ZMod q)

/-- Every generated parameter is `g ^ x` for a unit `x`. -/
theorem exists_of_mem_support_paramGen {g h : G} (hh : h ∈ (paramGen q g).support) :
    ∃ x : (ZMod q)ˣ, gpow g (x : ZMod q) = h := by
  rw [paramGen, PMF.mem_support_map_iff] at hh
  obtain ⟨x, -, hx⟩ := hh
  exact ⟨x, hx⟩

/-- Every generated parameter satisfies `h ^ q = 1` when `g ^ q = 1`. -/
theorem pow_eq_one_of_mem_support_paramGen {g h : G} (hg : g ^ q = 1)
    (hh : h ∈ (paramGen q g).support) : h ^ q = 1 := by
  obtain ⟨x, rfl⟩ := exists_of_mem_support_paramGen hh
  exact gpow_pow_eq_one hg _

/-- For `q` prime, `g ^ q = 1` and `g ≠ 1`, no generated parameter is the identity. -/
theorem ne_one_of_mem_support_paramGen [Fact q.Prime] {g h : G} (hg : g ^ q = 1) (hg1 : g ≠ 1)
    (hh : h ∈ (paramGen q g).support) : h ≠ 1 := by
  obtain ⟨x, rfl⟩ := exists_of_mem_support_paramGen hh
  exact fun h1 => x.ne_zero (eq_zero_of_gpow_eq_one hg hg1 h1)

/-- **Every generated parameter gives a perfectly hiding scheme**: in a group of prime order
`q` with `g ≠ 1`, `scheme q g h` is perfectly hiding for every `h` in the support of
`paramGen q g`. -/
theorem perfectlyHiding_of_mem_support [Fintype G] [DecidableEq G] [Fact q.Prime] {g h : G}
    (hcard : Fintype.card G = q) (hg1 : g ≠ 1) (hh : h ∈ (paramGen q g).support) :
    (scheme q g h).PerfectlyHiding :=
  perfectlyHiding_of_prime_card g
    (ne_one_of_mem_support_paramGen (hcard ▸ pow_card_eq_one) hg1 hh) hcard

end Params

/-! ### Computational binding from the discrete logarithm -/

section Binding

variable [DecidableEq G] [NeZero q] {R : Type*}

/-- A discrete-logarithm adversary: with coins `r ← coins`, from `h` it outputs an exponent. -/
structure DLAdversary (G : Type*) (q : ℕ) (R : Type*) where
  /-- The distribution of the adversary's random coins. -/
  coins : PMF R
  /-- The adversary, as a function of `h` and its coins. -/
  run : G → R → ZMod q

variable (q) in
/-- The discrete-logarithm experiment (Katz and Lindell, Section 8.3.2, with `h` from
`paramGen`): `h ← paramGen q g`, `r ← A.coins`, and the adversary wins if its output `x'`
satisfies `g ^ x' = h`. Unlike Katz and Lindell, `h = 1` is excluded, matching the binding
experiment. Wave 3: unify with the Wave 1 Assumptions DLP game. -/
noncomputable def dlGame (g : G) (A : DLAdversary G q R) : PMF Bool :=
  (paramGen q g).bind fun h => A.coins.map fun r => decide (gpow g (A.run h r) = h)

variable (q) in
/-- The discrete-logarithm advantage: the success probability in `dlGame`. Wave 3: unify with
the Wave 1 Assumptions DLP game. -/
noncomputable def dlAdvantage (g : G) (A : DLAdversary G q R) : ℝ := winProb (dlGame q g A)

variable (q) in
/-- The binding experiment for Pedersen commitments (Katz and Lindell, Section 5.6.5): the
generic `Commitment.bindingGame` with parameter `h ← paramGen q g`, hidden exponent, and the
scheme `scheme q g h`. -/
noncomputable abbrev bindingGame (g : G) (A : BindingAdversary G (ZMod q) G (ZMod q) R) :
    PMF Bool :=
  Commitment.bindingGame (paramGen q g) (scheme q g) A

variable (q) in
/-- The binding advantage: the success probability in `bindingGame`. -/
noncomputable abbrev bindingAdvantage (g : G) (A : BindingAdversary G (ZMod q) G (ZMod q) R) :
    ℝ :=
  winProb (bindingGame q g A)

/-- The discrete-logarithm adversary built from a binding adversary: on the same `h` and the same
coins, apply `extract` to its two openings. -/
def reduction (A : BindingAdversary G (ZMod q) G (ZMod q) R) : DLAdversary G q R where
  coins := A.coins
  run h r := extract (A.run h r).2.1.1 (A.run h r).2.1.2 (A.run h r).2.2.1 (A.run h r).2.2.2

/-- **Computational binding of Pedersen commitments from the discrete logarithm**: for `q`
prime, `g ^ q = 1` and `g ≠ 1`, every binding adversary's success probability is at most the
discrete-logarithm advantage of `reduction A`, both over `h ← paramGen q g`. -/
theorem bindingAdvantage_le [Fact q.Prime] {g : G} (hg : g ^ q = 1) (hg1 : g ≠ 1)
    (A : BindingAdversary G (ZMod q) G (ZMod q) R) :
    bindingAdvantage q g A ≤ dlAdvantage q g (reduction A) := by
  refine winProb_bind_map_mono _ _ fun h hh r hw => ?_
  obtain ⟨h₁, h₂, hne⟩ := of_decide_eq_true hw
  exact decide_eq_true (extract_spec hg hg1 (pow_eq_one_of_mem_support_paramGen hg hh) hne
    (accepts_iff.mp h₁) (accepts_iff.mp h₂))

end Binding

end Cslib.Crypto.Protocols.Commitment.Pedersen
