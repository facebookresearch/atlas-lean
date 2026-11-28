/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.RepresentationTheory.TwistByCharacter

/-!
# The cyclotomic character of a field and Tate twists

Let `k` be a field and `G_k = Field.absoluteGaloisGroup k`, the group of automorphisms of the
algebraic closure `AlgebraicClosure k` over `k` (which restricts isomorphically to the Galois
group of the separable closure). Following J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of
Number Fields*, 2nd ed., electronic edition version 2.3 (May 2020), Chapter VII, §3, (7.3.6)
Definition, the text before it and the remarks after it, pp. 397–398, this file defines

* the `ℓ`-adic cyclotomic character `χ_ℓ : G_k →* ℤ_ℓˣ` for a prime `ℓ`
  (`Field.ellAdicCyclotomicCharacter`), with its defining property
  `σ ζ = ζ ^ (χ_ℓ(σ) mod ℓ ^ n)` for `ζ ^ ℓ ^ n = 1` and its uniqueness when `(ℓ : k) ≠ 0`,
  its continuity for the Krull topology, and its triviality when `(ℓ : k) = 0`;
* the cyclotomic character `χ_cycl : G_k →* ∏_{ℓ ≠ char k} ℤ_ℓˣ`
  (`Field.cyclotomicCharacterProd`), with the property `σ ζ = ζ ^ a` for every root of unity
  `ζ` with `ζ ^ n = 1`, `(n : k) ≠ 0`, and every integer `a ≡ χ_cycl(σ) mod n`;
* the scalar model `ℤ_ℓ(i)` of the Tate twist (`Field.tateTwistZl`), the twist of the trivial
  representation by `χ_ℓ ^ i` (`Representation.twistByCharacter`), and the equivariance of
  `a ↦ ζ ^ a` from `ℤ/ℓ^mℤ(1)` to the `ℓ ^ m`-th roots of unity.

The Mathlib character `cyclotomicCharacter` of a domain is the input, and its continuity
`cyclotomicCharacter.continuous` gives the continuity of each `χ_ℓ` and of `χ_cycl` with the
product topology. The quoted phrases in the docstrings are those of the page *Cyclotomic
character and Tate twists*.
-/

@[expose] public section

set_option autoImplicit false

namespace Field

variable (k : Type*) [Field k]

private theorem hasEnoughRootsOfUnity_of_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    HasEnoughRootsOfUnity (AlgebraicClosure k) n := by
  have : NeZero (n : k) := ⟨hn⟩
  infer_instance

private theorem hasEnoughRootsOfUnity_pow (ℓ : ℕ) (hℓ : (ℓ : k) ≠ 0) (i : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure k) (ℓ ^ i) :=
  hasEnoughRootsOfUnity_of_ne_zero k (by push_cast; exact pow_ne_zero _ hℓ)

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_k →* ℤ_ℓˣ` of a field `k`, defined for every
prime `ℓ`: Mathlib's `cyclotomicCharacter` of the algebraic closure, restricted to
`G_k = Field.absoluteGaloisGroup k`. For `(ℓ : k) ≠ 0` it is characterized by
`ellAdicCyclotomicCharacter_spec` and `eq_ellAdicCyclotomicCharacter`. For `(ℓ : k) = 0`, that
is `ℓ = char k`, the algebraic closure has no primitive `ℓ`-th root of unity and the character
is trivial (`ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero`); the page defines `χ_ℓ`
only for `ℓ ≠ char k`. It is continuous for every prime `ℓ`
(`continuous_ellAdicCyclotomicCharacter`).

Page: *Cyclotomic character and Tate twists* (`af_04b38c0b2968aca1898d6fbe`): "its component
`χ_ℓ` ... describes the action of `G_k` on the `ℓ`-power roots of unity". Source:
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition
version 2.3, Chapter VII, §3, (7.3.6) Definition and the text before it, p. 397. -/
noncomputable def ellAdicCyclotomicCharacter (ℓ : ℕ) [Fact ℓ.Prime] :
    absoluteGaloisGroup k →* ℤ_[ℓ]ˣ where
  toFun σ := cyclotomicCharacter (AlgebraicClosure k) ℓ σ.toRingEquiv
  map_one' := map_one (cyclotomicCharacter (AlgebraicClosure k) ℓ)
  map_mul' σ τ :=
    map_mul (cyclotomicCharacter (AlgebraicClosure k) ℓ) σ.toRingEquiv τ.toRingEquiv

/-- The defining property of the `ℓ`-adic cyclotomic character: for a prime `ℓ` with
`(ℓ : k) ≠ 0`, `σ ∈ G_k` and `ζ` in the algebraic closure with `ζ ^ ℓ ^ n = 1`,
`σ ζ = ζ ^ a` where `a` is the residue of `χ_ℓ(σ)` modulo `ℓ ^ n`, as a natural number.

Page `af_04b38c0b2968aca1898d6fbe`, the relation `σ(ζ) = ζ ^ χ_cycl(σ)` restricted to the
`ℓ`-power roots of unity (Neukirch–Schmidt–Wingberg, text before (7.3.6) Definition,
p. 397). -/
theorem ellAdicCyclotomicCharacter_spec (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) {n : ℕ} {ζ : AlgebraicClosure k}
    (hζ : ζ ^ ℓ ^ n = 1) :
    σ ζ = ζ ^ (PadicInt.toZModPow n (ellAdicCyclotomicCharacter k ℓ σ : ℤ_[ℓ])).val := by
  have := hasEnoughRootsOfUnity_pow k ℓ hℓ
  exact cyclotomicCharacter.spec ℓ σ.toRingEquiv ζ hζ

/-- Uniqueness of the `ℓ`-adic cyclotomic character: for a prime `ℓ` with `(ℓ : k) ≠ 0`, an
element `α ∈ ℤ_ℓ` such that `σ ζ = ζ ^ (α mod ℓ ^ n)` for every `n` and every `ζ` with
`ζ ^ ℓ ^ n = 1` is `χ_ℓ(σ)`.

Page `af_04b38c0b2968aca1898d6fbe`: the character is "determined by" this relation
(Neukirch–Schmidt–Wingberg, text before (7.3.6) Definition, p. 397). -/
theorem eq_ellAdicCyclotomicCharacter (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (α : ℤ_[ℓ])
    (h : ∀ (n : ℕ) (ζ : AlgebraicClosure k), ζ ^ ℓ ^ n = 1 →
      σ ζ = ζ ^ (PadicInt.toZModPow n α).val) :
    α = ellAdicCyclotomicCharacter k ℓ σ := by
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  have := hasEnoughRootsOfUnity_pow k ℓ hℓ n
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure k) (ℓ ^ n)
  have h1 := h n ζ hζ.pow_eq_one
  have h2 := ellAdicCyclotomicCharacter_spec k ℓ hℓ σ hζ.pow_eq_one
  rw [h1] at h2
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)

/-- For a prime `ℓ` with `(ℓ : k) = 0`, that is `ℓ = char k`, the `ℓ`-adic cyclotomic
character is the trivial character: the algebraic closure, of characteristic `ℓ`, has no
primitive `ℓ`-th root of unity, and Mathlib's `cyclotomicCharacter` is then trivial. -/
theorem ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) = 0) : ellAdicCyclotomicCharacter k ℓ = 1 := by
  have H : ¬ ∀ i : ℕ, ∃ ζ : AlgebraicClosure k, IsPrimitiveRoot ζ (ℓ ^ i) := by
    intro H
    obtain ⟨ζ, hζ⟩ := H 1
    rw [pow_one] at hζ
    have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    have h := hζ.neZero'
    exact h.out (by rw [← map_natCast (algebraMap k (AlgebraicClosure k)), hℓ, map_zero])
  ext σ
  simp [ellAdicCyclotomicCharacter, cyclotomicCharacter, cyclotomicCharacter.toFun,
    dite_eq_right H]

/-- The `ℓ`-adic cyclotomic character is continuous for the Krull topology on `G_k` and the
topology of `ℤ_ℓˣ`, for every prime `ℓ`. This is Mathlib's `cyclotomicCharacter.continuous`
for the extension `AlgebraicClosure k` of `k`.

Page `af_04b38c0b2968aca1898d6fbe`: "the cyclotomic character is the continuous homomorphism",
here for its `ℓ`-component. Neukirch–Schmidt–Wingberg introduce the character in the text before
(7.3.6) Definition, p. 397, and do not state its continuity there. -/
theorem continuous_ellAdicCyclotomicCharacter (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous (ellAdicCyclotomicCharacter k ℓ) :=
  (cyclotomicCharacter.continuous ℓ k (AlgebraicClosure k)).congr fun _ =>
    congrArg (cyclotomicCharacter (AlgebraicClosure k) ℓ) (RingEquiv.ext fun _ => rfl)

/-- The primes `ℓ` different from the characteristic of `k`, that is, with `(ℓ : k) ≠ 0`: the
index set of the product `∏_{ℓ ≠ char k} ℤ_ℓˣ` of page `af_04b38c0b2968aca1898d6fbe`. -/
def CyclotomicPrime : Type := {ℓ : ℕ // ℓ.Prime ∧ (ℓ : k) ≠ 0}

/-- Each index of `Field.CyclotomicPrime k` is a prime. -/
instance CyclotomicPrime.fact_prime (ℓ : CyclotomicPrime k) : Fact ℓ.1.Prime := ⟨ℓ.2.1⟩

/-- The cyclotomic character `χ_cycl : G_k →* ∏_{ℓ ≠ char k} ℤ_ℓˣ` of a field `k`, whose
components are the `ℓ`-adic cyclotomic characters (`ellAdicCyclotomicCharacter`). Its
defining property is `cyclotomicCharacterProd_spec`, and it is continuous for the product
topology (`continuous_cyclotomicCharacterProd`).

Page: *Cyclotomic character and Tate twists* (`af_04b38c0b2968aca1898d6fbe`). Source:
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition
version 2.3, Chapter VII, §3, (7.3.6) Definition and the text before it, p. 397. -/
noncomputable def cyclotomicCharacterProd :
    absoluteGaloisGroup k →* ((ℓ : CyclotomicPrime k) → ℤ_[ℓ.1]ˣ) :=
  MonoidHom.pi fun ℓ => ellAdicCyclotomicCharacter k ℓ.1

/-- The cyclotomic character `χ_cycl : G_k →* ∏_{ℓ ≠ char k} ℤ_ℓˣ` is continuous for the
Krull topology and the product topology. Page `af_04b38c0b2968aca1898d6fbe`: "the cyclotomic
character is the continuous homomorphism". Neukirch–Schmidt–Wingberg introduce the character in
the text before (7.3.6) Definition, p. 397, and do not state its continuity there. -/
theorem continuous_cyclotomicCharacterProd : Continuous (cyclotomicCharacterProd k) :=
  continuous_pi fun ℓ => continuous_ellAdicCyclotomicCharacter k ℓ.1

private theorem zpow_eq_of_modEq {K : Type*} [Field K] {η : K} {N : ℕ} (hN : N ≠ 0)
    (hη : η ^ N = 1) (a b : ℤ) (h : (N : ℤ) ∣ b - a) : η ^ a = η ^ b := by
  obtain ⟨t, ht⟩ := h
  have hb : b = a + N * t := by linarith
  have hη0 : η ≠ 0 := by
    rintro rfl
    simp [zero_pow hN] at hη
  rw [hb, zpow_add₀ hη0, zpow_mul, zpow_natCast, hη, one_zpow, mul_one]

/-- The defining property of the cyclotomic character: for `σ ∈ G_k`, a root of unity `ζ` of
the algebraic closure with `ζ ^ n = 1` for some `n` with `(n : k) ≠ 0`, and an integer `a`
with `a ≡ χ_cycl(σ)_ℓ (mod ℓ ^ v_ℓ(n))` for every prime `ℓ ≠ char k` (that is,
`a ≡ χ_cycl(σ) mod n`), `σ ζ = ζ ^ a`.

Page `af_04b38c0b2968aca1898d6fbe`: "determined by `σ(ζ) = ζ^{χ_cycl(σ)}` ... one sets
`ζ^α = ζ^a` for any `a ∈ ℤ` with `a ≡ α mod n`" (Neukirch–Schmidt–Wingberg, text before
(7.3.6) Definition, p. 397). -/
theorem cyclotomicCharacterProd_spec (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) {n : ℕ}
    (hn : (n : k) ≠ 0)
    {ζ : AlgebraicClosure k} (hζ : ζ ^ n = 1) (a : ℤ)
    (ha : ∀ ℓ : CyclotomicPrime k, ((a : ZMod (ℓ.1 ^ n.factorization ℓ.1))) =
      PadicInt.toZModPow (n.factorization ℓ.1) (cyclotomicCharacterProd k σ ℓ : ℤ_[ℓ.1])) :
    σ ζ = ζ ^ a := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow hn0] at hζ
  have hza : ζ ^ a ≠ 0 := zpow_ne_zero _ hζ0
  set x := σ ζ * (ζ ^ a)⁻¹ with hx
  -- `x ^ (n / ℓ ^ v_ℓ(n)) = 1` for every prime `ℓ ≠ char k`.
  have key : ∀ ℓ : CyclotomicPrime k, x ^ (n / ℓ.1 ^ n.factorization ℓ.1) = 1 := by
    intro ℓ
    set e := n.factorization ℓ.1
    set m := n / ℓ.1 ^ e
    have hnm : ℓ.1 ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ.1
    have hη : (ζ ^ m) ^ ℓ.1 ^ e = 1 := by
      rw [← pow_mul, mul_comm, hnm, hζ]
    have hs := ellAdicCyclotomicCharacter_spec k ℓ.1 ℓ.2.2 σ hη
    set c := PadicInt.toZModPow e (ellAdicCyclotomicCharacter k ℓ.1 σ : ℤ_[ℓ.1])
    have : NeZero (ℓ.1 ^ e) := ⟨pow_ne_zero _ ℓ.2.1.ne_zero⟩
    have hac : ((ℓ.1 ^ e : ℕ) : ℤ) ∣ (c.val : ℤ) - a := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [ha ℓ, Int.cast_natCast, ZMod.natCast_zmod_val]
      rfl
    have h3 : (ζ ^ m) ^ a = (ζ ^ m) ^ (c.val : ℤ) := zpow_eq_of_modEq (NeZero.ne _) hη a _ hac
    rw [zpow_natCast] at h3
    rw [hx, mul_pow, ← map_pow, hs, ← h3, inv_pow, ← zpow_natCast (ζ ^ a) m, ← zpow_mul,
      ← zpow_natCast ζ m, ← zpow_mul, mul_comm (m : ℤ) a, mul_inv_cancel₀ (zpow_ne_zero _ hζ0)]
  have hxn : x ^ n = 1 := by
    have hzn : (ζ ^ a) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
    rw [hx, mul_pow, ← map_pow, hζ, map_one, inv_pow, hzn, inv_one, one_mul]
  have hx1 : x = 1 := by
    rw [← orderOf_eq_one_iff]
    by_contra hne
    obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
    have hℓn : ℓ ∣ n := hℓd.trans (orderOf_dvd_of_pow_eq_one hxn)
    have hℓk : (ℓ : k) ≠ 0 := by
      intro h0
      obtain ⟨c, hc⟩ := Nat.cast_dvd_cast (α := k) hℓn
      exact hn (by rw [hc, h0, zero_mul])
    have h4 := orderOf_dvd_of_pow_eq_one (key ⟨ℓ, hℓ, hℓk⟩)
    exact Nat.not_dvd_ordCompl hℓ hn0 (hℓd.trans h4)
  rw [hx, mul_inv_eq_one₀ hza] at hx1
  exact hx1

/-- The Tate twist `ℤ_ℓ(i)` in the scalar-character model, for a prime `ℓ`: `ℤ_ℓ` with `G_k`
acting by multiplication by `χ_ℓ ^ i`, the twist of the trivial representation by the `ℓ`-adic
cyclotomic character. For `(ℓ : k) = 0`, that is `ℓ = char k`, the character is trivial
(`ellAdicCyclotomicCharacter_eq_one_of_natCast_eq_zero`), so this is the trivial
representation for every `i`; the page defines `ℤ_ℓ(i)` only for `ℓ ≠ char k`.

Page `af_04b38c0b2968aca1898d6fbe`: "these are `ℤ_ℓ` and `ℚ_ℓ/ℤ_ℓ` with `G_k` acting through
`χ_ℓ^i` (the scalar-character model)". The description of `ℤ_ℓ(i)` as `lim ℤ/ℓ^mℤ(i)`
(Neukirch–Schmidt–Wingberg, remarks after (7.3.6) Definition, p. 398) is not stated here. -/
noncomputable def tateTwistZl (ℓ : ℕ) [Fact ℓ.Prime] (i : ℤ) :
    Representation ℤ_[ℓ] (absoluteGaloisGroup k) ℤ_[ℓ] :=
  (Representation.trivial ℤ_[ℓ] (absoluteGaloisGroup k) ℤ_[ℓ]).twistByCharacter
    (ellAdicCyclotomicCharacter k ℓ) i

/-- `σ ∈ G_k` acts on `ℤ_ℓ(i)` as multiplication by `χ_ℓ(σ) ^ i`. Page
`af_04b38c0b2968aca1898d6fbe`. -/
theorem tateTwistZl_apply (ℓ : ℕ) [Fact ℓ.Prime] (i : ℤ)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (x : ℤ_[ℓ]) :
    tateTwistZl k ℓ i σ x = ((ellAdicCyclotomicCharacter k ℓ σ ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * x := by
  rfl

/-- Equivariance of `a ↦ ζ ^ a` from `ℤ/ℓ^mℤ(1)` to the `ℓ ^ m`-th roots of unity: for a prime
`ℓ` with `(ℓ : k) ≠ 0`, `σ ∈ G_k`, an element `ζ` of the algebraic closure with
`ζ ^ ℓ ^ m = 1` and `a ∈ ℤ/ℓ^mℤ`, `σ (ζ ^ a) = ζ ^ (χ_ℓ(σ) a)`, where `χ_ℓ(σ)` acts through its
residue modulo `ℓ ^ m` and the exponents are taken as natural-number representatives.

Page `af_04b38c0b2968aca1898d6fbe`: "a choice of ... primitive `ℓ^m`-th roots of unity ...
gives isomorphisms `ℤ/ℓ^mℤ(1) ≅ μ_{ℓ^m}`, `1 ↦ ζ_{ℓ^m}`". Only equivariance is stated; for a
primitive `ℓ ^ m`-th root of unity `ζ`, the bijectivity of `a ↦ ζ ^ a` is Mathlib's
`IsPrimitiveRoot.zmodEquivZPowers`. -/
theorem ellAdicCyclotomicCharacter_spec_pow_val (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    {m : ℕ} {ζ : AlgebraicClosure k} (hζ : ζ ^ ℓ ^ m = 1) (a : ZMod (ℓ ^ m)) :
    σ (ζ ^ a.val) =
      ζ ^ (PadicInt.toZModPow m (ellAdicCyclotomicCharacter k ℓ σ : ℤ_[ℓ]) * a).val := by
  rw [map_pow, ellAdicCyclotomicCharacter_spec k ℓ hℓ σ hζ, ← pow_mul, ZMod.val_mul,
    ← pow_eq_pow_mod _ hζ]

end Field
