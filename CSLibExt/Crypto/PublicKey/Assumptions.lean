/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import CSLibExt.Crypto.PublicKey.ElGamal
public import CSLibExt.Crypto.PublicKey.RSA

/-!
# Cryptographic hardness assumptions as games, and the implications between them

The number-theoretic assumptions of Katz and Lindell, Chapter 8, as concrete (fixed-size)
experiments `PMF Bool` in the style of `CSLibExt.Crypto.Framework`: every adversary is a
deterministic function of its uniformly random coins in a finite type `S`, and the advantage is
the success probability `winProb` (or, for the decisional problem, a distinguishing
`advantage`). Assumptions are **stated, not proved**: the content of this file is the reductions
between them, each an exact relation between advantages.

**Groups.** `G` is a commutative group with an element `g`, and exponents live in `ZMod q`
(`gpow g x = g ^ x.val`). The DDH experiments `ElGamal.ddhReal`, `ElGamal.ddhRand` and
`ElGamal.ddhAdvantage` are reused from `CSLibExt.Crypto.PublicKey.ElGamal`, not redefined.
* `dlogGame q g A`, `dlogAdvantage`: the discrete-logarithm experiment `DLog` (Section 8.3.2):
  for uniform `x`, the solver gets `h = g ^ x` and wins when its output `x'` has `g ^ x' = h`.
* `cdhGame q g A`, `cdhAdvantage`: the computational Diffie–Hellman experiment (Section 8.3.2):
  given `(g ^ x, g ^ y)` the solver wins when it outputs `g ^ (x y)`.
* **CDH ⇒ DLog** (`dlogAdvantage_le_cdhAdvantage`): from a discrete-log solver `A`,
  `cdhOfDlog A` answers `(X, Y) ↦ Y ^ (A X)`; it wins whenever `A` does, so
  `dlogAdvantage A ≤ cdhAdvantage (cdhOfDlog A)`. Needs only `g ^ q = 1`.
* **DDH ⇒ CDH** (`ddhAdvantage_ddhOfCdh`): from a CDH solver `A`, `ddhOfCdh A` outputs whether
  `A X Y = Z`. On a real triple it outputs `1` exactly when `A` wins; on a random triple with
  probability exactly `1/q` (`winProb_ddhRand_ddhOfCdh`, when `g` generates `G` and `|G| = q`).
  So `ddhAdvantage (ddhOfCdh A) = |cdhAdvantage A - 1/q|`, and
  `cdhAdvantage A ≤ ddhAdvantage (ddhOfCdh A) + 1/q` (`cdhAdvantage_le_ddhAdvantage`).
* `dlogAdvantage_le_ddhAdvantage`: the composite **DDH ⇒ DLog** bound.

**RSA.** Keys are `CSLibExt.Crypto.PublicKey.RSA.Key` (distinct primes `p`, `q`, exponents with
`e d ≡ 1` modulo `p - 1` and `q - 1`), drawn from an arbitrary key-generation distribution
`gen : PMF RSA.Key` (Katz and Lindell's `GenRSA`).
* `rsaGame gen A`, `rsaAdvantage`: the RSA-inversion experiment `RSA-inv` (Section 8.2.4): for a
  key from `gen` and a uniform `y ∈ (ZMod n)ˣ`, the inverter gets `(n, e, y)` and wins when its
  output `x` has `x ^ e = y`.
* `factorGame gen A`, `factorAdvantage`: the factoring experiment `Factor` (Section 8.2.3) for the
  moduli `n = p q` output by `gen`: the algorithm gets `n` and wins when it outputs `a, b > 1`
  with `a b = n`.
* **RSA ⇒ factoring** (`factorAdvantage_le_rsaAdvantage`): from a factoring algorithm `F`,
  `rsaOfFactor F` factors `n` as `(a, b)`, inverts `e` modulo `(a - 1)(b - 1)` and outputs
  `y ^ (e⁻¹ mod (a - 1)(b - 1))`. Whenever `F` succeeds, `{a, b} = {p, q}`
  (`eq_or_eq_of_mul_eq`), and the output is the `e`-th root of `y` for **every** `y`
  (`rsaOfFactor_pow_e`), so `factorAdvantage F ≤ rsaAdvantage (rsaOfFactor F)`. This is the
  concrete core of the direction Katz and Lindell prove (if RSA is hard then factoring is hard;
  the asymptotic statement is out of scope, see below). The converse (an RSA inverter yields a
  factoring algorithm) is an open problem and is not claimed.

**Scope: concrete bounds only.** There is no security parameter and no PPT model here: the
theorems are exact relations between concrete advantages for one fixed group order `q` (or one
key distribution `gen`). Katz and Lindell's asymptotic implications ("if DDH is hard relative to
`𝒢` then so is CDH", etc.) are **not** claimed. Deriving them with
`Framework.AsymptoticallySecure.of_reduction` (`CSLibExt.Crypto.Framework.Asymptotic`) needs,
for families indexed by the security parameter `n`, two facts this file does not prove:
* **admissibility of the reductions**: `cdhOfDlog`, `ddhOfCdh` and `rsaOfFactor` map admissible
  (for example polynomial-time) adversary families to admissible families. They are efficient
  (one exponentiation, one comparison, one modular inversion), but no adversary class here
  expresses that;
* **a negligible additive term**, for DDH ⇒ CDH and DDH ⇒ DLog only: their bounds carry `+ 1/q`,
  so they need the group order `qₙ` to grow so fast that `n ↦ 1 / qₙ` is negligible (as in Katz
  and Lindell, where `𝒢(1ⁿ)` outputs a group of order `qₙ` with `‖qₙ‖ = n`). For a bounded
  `qₙ` the term is not negligible and the bound transfers nothing. CDH ⇒ DLog and
  RSA ⇒ factoring have no additive term and need only admissibility.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 8.2.3, 8.2.4 and 8.3.2.
-/

@[expose] public section

namespace Cslib.Crypto.PublicKey.Assumptions

open Finset Cslib.Crypto.Framework
open Cslib.Probability.PMF (uniformOfFintype)

/-! ### A counting lemma -/

/-- If every success of `g` on `a` makes `f` succeed on all of `e (a, b)`, then `f` on a uniform
sample succeeds at least as often as `g` on a uniform sample: the reductions of this file add an
independent uniform coordinate `b` that the inner algorithm ignores. -/
theorem winProb_map_uniform_le_of_equiv {Ω Ω' B : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ω']
    [Nonempty Ω'] [Finite B] [Nonempty B] (e : Ω' × B ≃ Ω) (f : Ω → Bool) (g : Ω' → Bool)
    (h : ∀ a b, g a = true → f (e (a, b)) = true) :
    winProb ((uniformOfFintype Ω').map g) ≤ winProb ((uniformOfFintype Ω).map f) := by
  classical
  have := Fintype.ofFinite B
  rw [winProb_map_uniform, winProb_map_uniform, ← Fintype.card_congr e, Fintype.card_prod]
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hΩ' : (0 : ℝ) < Fintype.card Ω' := by exact_mod_cast Fintype.card_pos
  have hcard : (univ.filter fun a => g a = true).card * Fintype.card B ≤
      (univ.filter fun ω => f ω = true).card := by
    rw [← card_univ (α := B), ← card_product]
    refine card_le_card_of_injOn (fun p => e p) ?_ (fun p _ p' _ hpp => e.injective hpp)
    intro p hp
    simp only [coe_product, coe_filter, mem_univ, true_and, coe_univ, Set.mem_prod,
      Set.mem_ofPred_eq, Set.mem_univ, and_true] at hp ⊢
    exact h p.1 p.2 hp
  have hcard' : ((univ.filter fun a => g a = true).card : ℝ) * Fintype.card B ≤
      (univ.filter fun ω => f ω = true).card := by exact_mod_cast hcard
  rw [Nat.cast_mul, div_le_div_iff₀ hΩ' (mul_pos hΩ' hB)]
  nlinarith

/-! ### Discrete logarithm and computational Diffie–Hellman -/

section DiscreteLog

variable {G : Type*} [CommGroup G] [DecidableEq G] {q : ℕ} [NeZero q] (g : G)
  {S : Type*} [Fintype S] [Nonempty S]

variable (q) in
/-- The **discrete-logarithm experiment** `DLog` (Katz and Lindell, Section 8.3.2): for uniform
`x` and coins `s`, the solver receives `h = g ^ x` and wins when its output `x'` satisfies
`g ^ x' = h`. -/
noncomputable def dlogGame (A : G → S → ZMod q) : PMF Bool :=
  (uniformOfFintype (ZMod q × S)).map fun ω => decide (gpow g (A (gpow g ω.1) ω.2) = gpow g ω.1)

variable (q) in
/-- The discrete-logarithm advantage `Pr[DLog = 1]` (Katz and Lindell, Section 8.3.2). -/
noncomputable def dlogAdvantage (A : G → S → ZMod q) : ℝ := winProb (dlogGame q g A)

variable (q) in
/-- The **computational Diffie–Hellman experiment** (Katz and Lindell, Section 8.3.2): for
uniform `x`, `y` and coins `s`, the solver receives `(g ^ x, g ^ y)` and wins when it outputs
`g ^ (x y)`. -/
noncomputable def cdhGame (A : G → G → S → G) : PMF Bool :=
  (uniformOfFintype (ZMod q × ZMod q × S)).map fun ω =>
    decide (A (gpow g ω.1) (gpow g ω.2.1) ω.2.2 = gpow g (ω.1 * ω.2.1))

variable (q) in
/-- The CDH advantage `Pr[CDH = 1]` (Katz and Lindell, Section 8.3.2). -/
noncomputable def cdhAdvantage (A : G → G → S → G) : ℝ := winProb (cdhGame q g A)

/-- The CDH solver built from a discrete-logarithm solver `A` (Katz and Lindell, Section 8.3.2:
"if the discrete-logarithm problem is easy, so is CDH"): on `(X, Y)` it computes
`x' = A X` and outputs `Y ^ x'`. -/
def cdhOfDlog (A : G → S → ZMod q) : G → G → S → G := fun X Y s => gpow Y (A X s)

/-- **CDH ⇒ DLog** (Katz and Lindell, Section 8.3.2): the CDH solver `cdhOfDlog A` succeeds
whenever the discrete-logarithm solver `A` does, so its advantage is at least that of `A`. -/
theorem dlogAdvantage_le_cdhAdvantage (hg : g ^ q = 1) (A : G → S → ZMod q) :
    dlogAdvantage q g A ≤ cdhAdvantage q g (cdhOfDlog A) := by
  let e : (ZMod q × S) × ZMod q ≃ ZMod q × ZMod q × S :=
    { toFun := fun p => (p.1.1, p.2, p.1.2)
      invFun := fun ω => ((ω.1, ω.2.2), ω.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine winProb_map_uniform_le_of_equiv e _ _ fun a y ha => ?_
  simp only [decide_eq_true_eq] at ha ⊢
  change gpow (gpow g y) (A (gpow g a.1) a.2) = gpow g (a.1 * y)
  rw [dh_agree, ha, gpow_mul hg]

/-- The DDH distinguisher built from a CDH solver `A` (Katz and Lindell, Section 8.3.2: "if CDH
is easy, so is DDH"): on `(X, Y, Z)` it outputs whether `A X Y = Z`. -/
def ddhOfCdh (A : G → G → S → G) : G → G → G → S → Bool := fun X Y Z s => decide (A X Y s = Z)

/-- With a real DDH triple, `ddhOfCdh A` runs the CDH experiment exactly. -/
theorem ddhReal_ddhOfCdh (A : G → G → S → G) :
    ElGamal.ddhReal q g (ddhOfCdh A) = cdhGame q g A := rfl

/-- With a random DDH triple, `ddhOfCdh A` outputs `1` with probability exactly `1/q`: the third
element `g ^ z` is uniform in `G` and independent of `A`'s answer. -/
theorem winProb_ddhRand_ddhOfCdh [Fintype G] (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : G → G → S → G) :
    winProb (ElGamal.ddhRand q g (ddhOfCdh A)) = 1 / q := by
  classical
  have key : ∀ t : G, gpow g ((gpowEquiv hgen hcard).symm t) = t := fun t => by
    rw [← gpowEquiv_apply hgen hcard, Equiv.apply_symm_apply]
  have hc : (univ.filter fun ω : ZMod q × ZMod q × ZMod q × S =>
      ddhOfCdh A (gpow g ω.1) (gpow g ω.2.1) (gpow g ω.2.2.1) ω.2.2.2 = true).card =
      Fintype.card (ZMod q × ZMod q × S) := by
    rw [← card_univ]
    symm
    refine card_nbij'
      (fun ω => (ω.1, ω.2.1, (gpowEquiv hgen hcard).symm (A (gpow g ω.1) (gpow g ω.2.1) ω.2.2),
        ω.2.2))
      (fun ω => (ω.1, ω.2.1, ω.2.2.2)) ?_ ?_ ?_ ?_
    · intro ω _
      simp [ddhOfCdh, key]
    · intro ω _
      simp
    · intro ω _
      rfl
    · intro ω hω
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, ddhOfCdh,
        decide_eq_true_eq] at hω
      obtain ⟨x, y, z, s⟩ := ω
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [hω, ← gpowEquiv_apply hgen hcard, Equiv.symm_apply_apply]
  rw [ElGamal.ddhRand, winProb_map_uniform, hc]
  simp only [Fintype.card_prod, ZMod.card, Nat.cast_mul]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hS : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- **DDH ⇒ CDH**, exactly (Katz and Lindell, Section 8.3.2): the DDH advantage of
`ddhOfCdh A` is `|cdhAdvantage A - 1/q|`. -/
theorem ddhAdvantage_ddhOfCdh [Fintype G] (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : G → G → S → G) :
    ElGamal.ddhAdvantage q g (ddhOfCdh A) = |cdhAdvantage q g A - 1 / q| := by
  change |winProb (ElGamal.ddhReal q g (ddhOfCdh A)) -
    winProb (ElGamal.ddhRand q g (ddhOfCdh A))| = _
  rw [ddhReal_ddhOfCdh, winProb_ddhRand_ddhOfCdh g hgen hcard, cdhAdvantage]

/-- **DDH ⇒ CDH** as a bound: a CDH solver's advantage exceeds the DDH advantage of
`ddhOfCdh A` by at most `1/q`. -/
theorem cdhAdvantage_le_ddhAdvantage [Fintype G] (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : G → G → S → G) :
    cdhAdvantage q g A ≤ ElGamal.ddhAdvantage q g (ddhOfCdh A) + 1 / q := by
  rw [ddhAdvantage_ddhOfCdh g hgen hcard]
  linarith [le_abs_self (cdhAdvantage q g A - 1 / q)]

/-- **DDH ⇒ DLog** (Katz and Lindell, Section 8.3.2), the composite of the two reductions: a
discrete-logarithm solver's advantage exceeds the DDH advantage of
`ddhOfCdh (cdhOfDlog A)` by at most `1/q`. -/
theorem dlogAdvantage_le_ddhAdvantage [Fintype G] (hgen : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Fintype.card G = q) (A : G → S → ZMod q) :
    dlogAdvantage q g A ≤ ElGamal.ddhAdvantage q g (ddhOfCdh (cdhOfDlog A)) + 1 / q :=
  (dlogAdvantage_le_cdhAdvantage g (hcard ▸ pow_card_eq_one) A).trans
    (cdhAdvantage_le_ddhAdvantage g hgen hcard _)

end DiscreteLog

/-! ### RSA and factoring -/

section RSA

open RSA

variable {S : Type*} [Fintype S] [Nonempty S]

instance (key : Key) : NeZero key.n := ⟨key.n_pos.ne'⟩

/-- The **RSA-inversion experiment** `RSA-inv` (Katz and Lindell, Section 8.2.4): a key is drawn
from `gen`, `y ∈ (ZMod n)ˣ` and the coins `s` are uniform, and the inverter receives the public
key `(n, e)` and `y`; it wins when its output `x` satisfies `x ^ e = y`. -/
noncomputable def rsaGame (gen : PMF Key) (A : (pk : PubKey) → ZMod pk.n → S → ZMod pk.n) :
    PMF Bool :=
  gen.bind fun key => (uniformOfFintype ((ZMod key.n)ˣ × S)).map fun ω =>
    decide ((show ZMod key.n from A key.publicKey (ω.1 : ZMod key.n) ω.2) ^ key.e =
      (ω.1 : ZMod key.n))

/-- The RSA-inversion advantage `Pr[RSA-inv = 1]` (Katz and Lindell, Section 8.2.4). -/
noncomputable def rsaAdvantage (gen : PMF Key)
    (A : (pk : PubKey) → ZMod pk.n → S → ZMod pk.n) : ℝ :=
  winProb (rsaGame gen A)

/-- A factoring algorithm's output `(a, b)` is a **nontrivial factorization** of `n`:
`a b = n` with `a, b > 1` (Katz and Lindell, Section 8.2.3). -/
def IsFactorization (n : ℕ) (ab : ℕ × ℕ) : Prop := ab.1 * ab.2 = n ∧ 1 < ab.1 ∧ 1 < ab.2

instance (n : ℕ) (ab : ℕ × ℕ) : Decidable (IsFactorization n ab) := by
  unfold IsFactorization; infer_instance

/-- The **factoring experiment** `Factor` (Katz and Lindell, Section 8.2.3) for the moduli
`n = p q` of the keys output by `gen`: the algorithm receives `n` and wins when it outputs a
nontrivial factorization. -/
noncomputable def factorGame (gen : PMF Key) (A : ℕ → S → ℕ × ℕ) : PMF Bool :=
  gen.bind fun key => (uniformOfFintype S).map fun s => decide (IsFactorization key.n (A key.n s))

/-- The factoring advantage `Pr[Factor = 1]` (Katz and Lindell, Section 8.2.3). -/
noncomputable def factorAdvantage (gen : PMF Key) (A : ℕ → S → ℕ × ℕ) : ℝ :=
  winProb (factorGame gen A)

/-- The only nontrivial factorizations of a product of two primes are `p q` and `q p`. -/
theorem eq_or_eq_of_mul_eq {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hab : a * b = p * q)
    (ha : 1 < a) (hb : 1 < b) : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := Nat.dvd_mul.mp (Dvd.intro b hab)
  rcases hp.eq_one_or_self_of_dvd a₁ ha₁ with h₁ | h₁ <;>
    rcases hq.eq_one_or_self_of_dvd a₂ ha₂ with h₂ | h₂ <;> subst a₁ a₂
  · omega
  · right
    refine ⟨one_mul q, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
    rw [mul_comm q p, ← hab, one_mul]
  · left
    refine ⟨mul_one p, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
    rw [← hab, mul_one]
  · exfalso
    have : p * q * b = p * q * 1 := by rw [mul_one]; exact hab
    have := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hq.pos) this
    omega

/-- An inverse `d'` of `e` modulo `φ`, computed in `ZMod φ`, satisfies `e d' ≡ 1 [MOD φ]`. -/
theorem mul_inv_val_modEq {e φ : ℕ} [NeZero φ] (h : e.Coprime φ) :
    e * ((e : ZMod φ)⁻¹).val ≡ 1 [MOD φ] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.coe_mul_inv_eq_one e h, Nat.cast_one]

/-- The RSA inverter built from a factoring algorithm `F` (Katz and Lindell, Section 8.2.4: "if
factoring is easy, RSA is easy"): factor `n` as `(a, b)`, invert `e` modulo `(a - 1)(b - 1)`,
and output `y ^ (e⁻¹ mod (a - 1)(b - 1))`. -/
def rsaOfFactor (F : ℕ → S → ℕ × ℕ) : (pk : PubKey) → ZMod pk.n → S → ZMod pk.n :=
  fun pk y s => y ^ ((pk.e : ZMod (((F pk.n s).1 - 1) * ((F pk.n s).2 - 1)))⁻¹).val

/-- With `φ = (p - 1)(q - 1)`, the exponent `e⁻¹ mod φ` inverts encryption on every residue. -/
theorem pow_inv_val_pow (key : Key) (y : ZMod key.n) :
    (y ^ ((key.e : ZMod ((key.p - 1) * (key.q - 1)))⁻¹).val) ^ key.e = y := by
  have hp2 := key.hp.two_le
  have hq2 := key.hq.two_le
  have : NeZero ((key.p - 1) * (key.q - 1)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hcop : key.e.Coprime ((key.p - 1) * (key.q - 1)) :=
    Nat.Coprime.mul_right (Nat.coprime_of_mul_modEq_one _ key.hed_p)
      (Nat.coprime_of_mul_modEq_one _ key.hed_q)
  have hed := mul_inv_val_modEq hcop
  let key' : Key :=
    { key with
      d := ((key.e : ZMod ((key.p - 1) * (key.q - 1)))⁻¹).val
      hed_p := Nat.ModEq.of_mul_right _ hed
      hed_q := Nat.ModEq.of_mul_left _ hed }
  rw [← pow_mul, mul_comm]
  exact key'.pow_ed y

omit [Fintype S] [Nonempty S] in
/-- **Correctness of the reduction**: whenever `F` outputs a nontrivial factorization of `n`,
`rsaOfFactor F` outputs the `e`-th root of every `y`. -/
theorem rsaOfFactor_pow_e (F : ℕ → S → ℕ × ℕ) (key : Key) (s : S)
    (hF : IsFactorization key.n (F key.n s)) (y : ZMod key.n) :
    (show ZMod key.n from rsaOfFactor F key.publicKey y s) ^ key.e = y := by
  obtain ⟨hab, ha, hb⟩ := hF
  have hφ : ((F key.n s).1 - 1) * ((F key.n s).2 - 1) = (key.p - 1) * (key.q - 1) := by
    rcases eq_or_eq_of_mul_eq key.hp key.hq hab ha hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2]
    exact mul_comm _ _
  change (y ^ ((key.e : ZMod (((F key.n s).1 - 1) * ((F key.n s).2 - 1)))⁻¹).val) ^ key.e = y
  rw [hφ]
  exact pow_inv_val_pow key y

/-- **RSA ⇒ factoring** (Katz and Lindell, Section 8.2.4): the RSA inverter `rsaOfFactor F`
succeeds whenever the factoring algorithm `F` does (for every challenge `y`), so its advantage is
at least that of `F`. -/
theorem factorAdvantage_le_rsaAdvantage (gen : PMF Key) (F : ℕ → S → ℕ × ℕ) :
    factorAdvantage gen F ≤ rsaAdvantage gen (rsaOfFactor F) := by
  have inner : ∀ key : Key,
      ((uniformOfFintype S).map fun s => decide (IsFactorization key.n (F key.n s))) true ≤
      ((uniformOfFintype ((ZMod key.n)ˣ × S)).map fun ω =>
        decide ((show ZMod key.n from rsaOfFactor F key.publicKey (ω.1 : ZMod key.n) ω.2) ^
          key.e = (ω.1 : ZMod key.n))) true := by
    intro key
    have h := winProb_map_uniform_le_of_equiv (Equiv.prodComm S (ZMod key.n)ˣ)
      (fun ω : (ZMod key.n)ˣ × S =>
        decide ((show ZMod key.n from rsaOfFactor F key.publicKey (ω.1 : ZMod key.n) ω.2) ^
          key.e = (ω.1 : ZMod key.n)))
      (fun s => decide (IsFactorization key.n (F key.n s))) fun s y hs => by
        simp only [decide_eq_true_eq] at hs ⊢
        exact rsaOfFactor_pow_e F key s hs y
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp h
  refine ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_
  rw [factorGame, rsaGame, PMF.bind_apply, PMF.bind_apply]
  exact ENNReal.tsum_le_tsum fun key => mul_le_mul_right (inner key) _

end RSA

end Cslib.Crypto.PublicKey.Assumptions
