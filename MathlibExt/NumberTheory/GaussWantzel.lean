/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/NumberTheory/GaussWantzel.lean` (leanprover/lean-eval),
problem `gauss_wantzel_constructible_polygon` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
lean-eval ships no `NOTICE` file.

The definitions of `IsConstructible` and `GaussWantzelNumber` and the theorem statement are
adapted from this source via `WantedExt/NumberTheory/GaussWantzelWanted.lean`. ATLAS replaced
the evaluation marker with `theorem_wanted`, inlined helper modules, and placed the declarations
in the current namespace. This file keeps their names, statements, and docstrings and adds
the proof.
-/

module

public import MathlibExt.NumberTheory.FermatPrime
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MathlibExt.NumberTheory.Cyclotomic.TwoCosAlgebraicDegree
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Gauss-Wantzel constructible polygon theorem

`gauss_wantzel_constructible_polygon`: a regular `n`-gon is
straightedge-and-compass constructible exactly when `n` is a Gauss-Wantzel
integer. Constructibility is encoded by `IsConstructible`, the smallest
subfield of `ℝ` closed under square roots, applied to `cos (2π/n)`; the
arithmetic side `GaussWantzelNumber` requires every odd prime factor to be a
distinct Fermat prime. Mathlib has the algebraic ingredients but no
constructibility theory and no Gauss-Wantzel theorem. Category-(b) candidate
from §174 of the Knill survey.

The proof uses the degree of the real cyclotomic field and the Galois correspondence
to relate constructibility to Euler's totient being a power of two.
-/

namespace MathlibExt.NumberTheory.GaussWantzelWanted
namespace NumberTheory.GaussWantzel

@[expose] public section

set_option linter.dupNamespace false in
/-- **Constructible real numbers.** The constructible real numbers form the smallest set of real
numbers that contains every rational number and is closed under addition, negation,
multiplication, inverses of nonzero elements and square roots of nonnegative elements;
equivalently, the smallest subfield of $\mathbb{R}$ closed under square roots.

These are the real values constructible from rational data by straightedge and compass. -/
inductive IsConstructible : ℝ → Prop
  | base (q : ℚ) : IsConstructible (q : ℝ)
  | add {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x + y)
  | neg {x : ℝ} : IsConstructible x → IsConstructible (-x)
  | mul {x y : ℝ} : IsConstructible x → IsConstructible y → IsConstructible (x * y)
  | inv {x : ℝ} : IsConstructible x → IsConstructible x⁻¹
  | sqrt {x : ℝ} : IsConstructible x → IsConstructible (Real.sqrt x)

set_option linter.dupNamespace false in
/-- **Gauss–Wantzel number.** A natural number $n$ is a Gauss–Wantzel number if $n > 0$, every
prime factor of $n$ is either $2$ or a Fermat prime, and $p^2$ does not divide $n$ for every odd
prime factor $p$ of $n$.

Equivalently, $n$ is a power of $2$ times a product of distinct Fermat primes. -/
def GaussWantzelNumber (n : ℕ) : Prop :=
  0 < n ∧
    ∀ p : ℕ, p.Prime → p ∣ n →
      (p = 2 ∨ MetaMathlibExt.IsFermatPrime p) ∧ (p ≠ 2 → ¬ p ^ 2 ∣ n)

end

open IntermediateField Module Polynomial
open scoped IntermediateField

-- Adjoining a root of a monic quadratic gives degree one or two.
private theorem finrank_adjoin_eq_pow_two {F E : Type*} [Field F] [Field E]
    [Algebra F E] {x : E} {p : F[X]} (hp : p.Monic) (hdeg : p.natDegree = 2)
    (hx : aeval x p = 0) : ∃ k : ℕ, finrank F F⟮x⟯ = 2 ^ k := by
  have hi : IsIntegral F x := ⟨p, hp, hx⟩
  rw [IntermediateField.adjoin.finrank hi]
  have hle := (natDegree_le_of_dvd (minpoly.dvd F x hx) hp.ne_zero).trans_eq hdeg
  have hpos := minpoly.natDegree_pos hi
  rcases show (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 by omega with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, by simpa using h⟩

-- Build a tower over an arbitrary base so that the two operands of a binary operation
-- can be adjoined successively.
private theorem exists_pow_two_extension {x : ℝ} (hx : IsConstructible x) :
    ∀ (F : Type) [Field F] [Algebra F ℝ],
      ∃ (K : IntermediateField F ℝ) (k : ℕ), x ∈ K ∧ finrank F K = 2 ^ k := by
  let InTower (a : ℝ) : Prop := ∀ (F : Type) [Field F] [Algebra F ℝ],
    ∃ (K : IntermediateField F ℝ) (k : ℕ), a ∈ K ∧ finrank F K = 2 ^ k
  change InTower x
  have combine {a b : ℝ} (ha : InTower a) (hb : InTower b)
      (F : Type) [Field F] [Algebra F ℝ] :
      ∃ (K : IntermediateField F ℝ) (k : ℕ), a ∈ K ∧ b ∈ K ∧ finrank F K = 2 ^ k := by
    obtain ⟨K, k, haK, hk⟩ := ha F
    obtain ⟨L, l, hbL, hl⟩ := hb K
    refine ⟨L.restrictScalars F, k + l, L.algebraMap_mem ⟨a, haK⟩, hbL, ?_⟩
    rw [pow_add, ← hk, ← hl]
    exact (Module.finrank_mul_finrank F K L).symm
  induction hx with
  | base q =>
    intro F _ _
    refine ⟨⊥, 0, ?_, IntermediateField.finrank_bot⟩
    exact mem_bot.mpr ⟨(q : F), map_ratCast _ q⟩
  | add _ _ ihx ihy =>
    intro F _ _
    obtain ⟨K, k, hxK, hyK, hk⟩ := combine ihx ihy F
    exact ⟨K, k, add_mem hxK hyK, hk⟩
  | neg _ ih =>
    intro F _ _
    obtain ⟨K, k, hxK, hk⟩ := ih F
    exact ⟨K, k, neg_mem hxK, hk⟩
  | mul _ _ ihx ihy =>
    intro F _ _
    obtain ⟨K, k, hxK, hyK, hk⟩ := combine ihx ihy F
    exact ⟨K, k, mul_mem hxK hyK, hk⟩
  | inv _ ih =>
    intro F _ _
    obtain ⟨K, k, hxK, hk⟩ := ih F
    exact ⟨K, k, inv_mem hxK, hk⟩
  | @sqrt x _ ih =>
    intro F _ _
    by_cases h : 0 ≤ x
    · obtain ⟨K, k, hxK, hk⟩ := ih F
      let L := K⟮Real.sqrt x⟯
      let p : K[X] := X ^ 2 - C ⟨x, hxK⟩
      have hp : p.Monic := monic_X_pow_sub_C _ (by decide)
      have hdeg : p.natDegree = 2 := by
        dsimp [p]
        compute_degree
        simp
      have hroot : aeval (Real.sqrt x) p = 0 := by
        simpa [p] using sub_eq_zero.mpr (Real.sq_sqrt h)
      obtain ⟨l, hl⟩ := finrank_adjoin_eq_pow_two hp hdeg hroot
      refine ⟨L.restrictScalars F, k + l, mem_adjoin_simple_self K _, ?_⟩
      change finrank K L = 2 ^ l at hl
      rw [pow_add, ← hk, ← hl]
      exact (Module.finrank_mul_finrank F K L).symm
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
      exact ⟨⊥, 0, zero_mem _, IntermediateField.finrank_bot⟩

-- A real root of a monic quadratic is obtained by completing the square.
private theorem constructible_of_quadratic {x b c : ℝ} (hb : IsConstructible b)
    (hc : IsConstructible c) (hx : x ^ 2 + b * x + c = 0) : IsConstructible x := by
  have hhalf : IsConstructible (b / 2) := by
    have htwo : IsConstructible (2 : ℝ) := by simpa using IsConstructible.base 2
    simpa only [div_eq_mul_inv] using hb.mul htwo.inv
  have hs : (x + b / 2) ^ 2 = (b / 2) * (b / 2) + -c := by linarith
  have habs : IsConstructible |x + b / 2| := by
    rw [← Real.sqrt_sq_eq_abs, hs]
    exact ((hhalf.mul hhalf).add hc.neg).sqrt
  have hshift : IsConstructible (x + b / 2) := by
    rcases le_total 0 (x + b / 2) with h | h
    · rwa [abs_of_nonneg h] at habs
    · rw [abs_of_nonpos h] at habs
      simpa only [neg_neg] using habs.neg
  convert hshift.add hhalf.neg using 1
  ring

-- The fixed field of an order-two subgroup has half the degree, and the
-- resulting quadratic step is solved over the real numbers.
private theorem constructible_of_abelian (k : ℕ) (K : IntermediateField ℚ ℝ)
    [IsAbelianGalois ℚ K] (hK : finrank ℚ K = 2 ^ k) {x : ℝ} (hx : x ∈ K) :
    IsConstructible x := by
  induction k generalizing K x with
  | zero =>
    have h : K = ⊥ := finrank_eq_one_iff.mp (by simpa using hK)
    rw [h, mem_bot] at hx
    obtain ⟨q, rfl⟩ := hx
    exact IsConstructible.base q
  | succ k ih =>
    have : FiniteDimensional ℚ K :=
      FiniteDimensional.of_finrank_pos (hK ▸ by positivity)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hd : 2 ^ 1 ∣ Nat.card (K ≃ₐ[ℚ] K) := by
      rw [IsGalois.card_aut_eq_finrank, hK, pow_succ]
      simp
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
    let L := fixedField H
    let L' := L.map K.val
    let e := L.equivMap K.val
    have hKL : finrank L K = 2 := by simpa [L] using (finrank_fixedField_eq_card H).trans hH
    have hL : finrank ℚ L' = 2 ^ k := by
      rw [← e.toLinearEquiv.finrank_eq]
      have ht := Module.finrank_mul_finrank ℚ L K
      rw [hKL, hK, pow_succ] at ht
      omega
    have : IsAbelianGalois ℚ L' := IsAbelianGalois.of_algHom (L.val.comp e.symm.toAlgHom)
    have hcoeff (a : L) : IsConstructible ((a : K) : ℝ) :=
      ih L' hL (show ((a : K) : ℝ) ∈ L' from (e a).property)
    let y : K := ⟨x, hx⟩
    let p := (Algebra.lmul L K y).charpoly
    have hdeg : p.natDegree = 2 := (LinearMap.charpoly_natDegree _).trans hKL
    have hmonic : p.Monic := LinearMap.charpoly_monic _
    have hlead : p.coeff 2 = 1 := hdeg ▸ hmonic.coeff_natDegree
    have hp : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      conv_lhs => rw [p.as_sum_range_C_mul_X_pow, hdeg]
      simp [Finset.sum_range_succ, hlead, add_comm, add_left_comm]
    have hy := Algebra.aeval_self_charpoly_lmul (R := L) y
    change aeval y p = 0 at hy
    rw [hp] at hy
    have hy' := congrArg K.val hy
    push_cast [map_add, map_mul, map_pow, aeval_X, aeval_C, map_zero] at hy'
    exact constructible_of_quadratic (hcoeff _) (hcoeff _) hy'

private theorem totient_pow_two_iff (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, n.totient = 2 ^ k) ↔ GaussWantzelNumber n := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨hn, fun p hp hpn ↦ ?_⟩
    by_cases hp2 : p = 2
    · exact ⟨Or.inl hp2, by simp [hp2]⟩
    have hm : p - 1 ∣ 2 ^ k := by
      rw [← hk, ← Nat.totient_prime hp]
      exact Nat.totient_dvd_of_dvd hpn
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
    have hpgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl
      omega
    have heq : p = 2 ^ l + 1 := by omega
    obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hl0 (heq ▸ hp)
    refine ⟨Or.inr ⟨hp, j, by rw [heq, hj, Nat.fermatNumber]⟩, fun _ hsq ↦ ?_⟩
    have hd : p ∣ (p ^ 2).totient := by
      rw [show (2 : ℕ) = 1 + 1 by decide, Nat.totient_prime_pow_succ hp, pow_one]
      exact dvd_mul_right _ _
    have hpd : p ∣ 2 := hp.dvd_of_dvd_pow (hk ▸ hd.trans (Nat.totient_dvd_of_dvd hsq))
    exact hp2 ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp hpd).symm
  · rintro ⟨-, h⟩
    rw [Nat.totient_eq_prod_factorization hn.ne']
    have hfactor (p : ℕ) (hp : p ∈ n.factorization.support) :
        ∃ k : ℕ, p ^ (n.factorization p - 1) * (p - 1) = 2 ^ k := by
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hdiv := Nat.dvd_of_mem_primeFactors hp
      by_cases hp2 : p = 2
      · subst p
        exact ⟨n.factorization 2 - 1, by simp⟩
      obtain ⟨hF, hsq⟩ := h p hprime hdiv
      have hmult : n.factorization p = 1 := by
        have hpos := Finsupp.mem_support_iff.mp hp
        have hlt := mt (hprime.pow_dvd_iff_le_factorization hn.ne').mpr (hsq hp2)
        omega
      obtain ⟨-, j, rfl⟩ := hF.resolve_left hp2
      exact ⟨2 ^ j, by rw [hmult]; simp [Nat.fermatNumber]⟩
    exact Finset.prod_induction _ (fun a ↦ ∃ k : ℕ, a = 2 ^ k)
      (fun _ _ ⟨k, hk⟩ ⟨l, hl⟩ ↦ ⟨k + l, by rw [pow_add, ← hk, ← hl]⟩)
      ⟨0, rfl⟩ hfactor

-- The doubled cosine generates an abelian subextension of the cyclotomic field.
private theorem real_cyclotomic (n : ℕ) (hn : 3 ≤ n) :
    let x := 2 * Real.cos (2 * Real.pi / n)
    IsAbelianGalois ℚ ℚ⟮x⟯ ∧ finrank ℚ ℚ⟮x⟯ * 2 = n.totient := by
  intro x
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨hn0.ne'⟩
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  let L := ℚ⟮ζ⟯
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have : IsCyclotomicExtension {n} ℚ L := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {n} ℚ L
  have hsum : (x : ℂ) = ζ + ζ⁻¹ := by
    let θ : ℝ := 2 * Real.pi / n
    have harg : (θ : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I / n := by
      dsimp [θ]
      push_cast
      ring
    change ((2 * Real.cos θ : ℝ) : ℂ) = ζ + ζ⁻¹
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.two_cos,
      harg, neg_mul, harg, Complex.exp_neg]
  let f : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  have hle : ℚ⟮x⟯.map f ≤ L := by
    rw [adjoin_map, Set.image_singleton]
    apply adjoin_le_iff.mpr
    rw [Set.singleton_subset_iff]
    change (x : ℂ) ∈ L
    rw [hsum]
    exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
  let e := (ℚ⟮x⟯.equivMap f).toAlgHom
  let g := (inclusion hle).comp e
  have : FiniteDimensional ℚ L :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral hn0).tower_top
  have hint : IsIntegral ℚ x := by
    have hi := IsIntegral.of_finite ℚ (g ⟨x, mem_adjoin_simple_self ℚ x⟩)
    have hc := hi.map L.val
    exact (isIntegral_algHom_iff f f.injective).mp hc
  have hdegree : finrank ℚ (Algebra.adjoin ℚ ({x} : Set ℝ)) = n.totient / 2 := by
    have heq : 2 * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / n) = x := by
      simp only [Nat.cast_one, mul_one, x]
    exact (congrArg (fun t : ℝ ↦ finrank ℚ (Algebra.adjoin ℚ ({t} : Set ℝ))) heq.symm).trans
      (MetaMathlibExt.finrank_adjoin_two_cos n 1 (by omega) (Nat.coprime_one_left n))
  rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    finrank_eq_finrank_subalgebra] at hdegree
  refine ⟨IsAbelianGalois.of_algHom g, ?_⟩
  obtain ⟨m, hm⟩ := Nat.totient_even (show 2 < n by omega)
  change finrank ℚ ℚ⟮x⟯ = n.totient / 2 at hdegree
  omega

set_option linter.dupNamespace false in
/- **Gauss-Wantzel constructible polygon theorem** (§174): a regular `n`-gon
is straightedge-and-compass constructible exactly for the Gauss-Wantzel
integers. -/
/-- **Gauss–Wantzel theorem.** For every natural number $n \ge 3$, the real number
$\cos(2\pi/n)$ is constructible (it lies in the smallest subfield of $\mathbb{R}$ closed under
square roots) if and only if $n$ is a Gauss–Wantzel number, that is, every prime factor of $n$ is
$2$ or a Fermat prime and every odd prime factor of $n$ divides $n$ only once.

Source: C. F. Gauss, Disquisitiones Arithmeticae (1801), §365-366; P. L. Wantzel, Recherches sur les
moyens de reconnaître si un problème de géométrie peut se résoudre avec la règle et le compas, J.
Math. Pures Appl. 1 (1837). Listed as §174 in O. Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Knill, §174. Via
leanprover/lean-eval@38361be, problem `gauss_wantzel_constructible_polygon`. -/
public theorem gauss_wantzel_constructible_polygon (n : ℕ) (hn : 3 ≤ n) :
    IsConstructible (Real.cos (2 * Real.pi / n)) ↔ GaussWantzelNumber n := by
  let x := 2 * Real.cos (2 * Real.pi / n)
  have htwo : IsConstructible (2 : ℝ) := by simpa using IsConstructible.base 2
  have hc : IsConstructible (Real.cos (2 * Real.pi / n)) ↔ IsConstructible x := by
    refine ⟨htwo.mul, fun hx ↦ ?_⟩
    convert htwo.inv.mul hx using 1
    dsimp [x]
    ring
  rw [hc, ← totient_pow_two_iff n (by omega)]
  obtain ⟨hgal, hdegree⟩ := real_cyclotomic n hn
  change IsAbelianGalois ℚ ℚ⟮x⟯ at hgal
  change finrank ℚ ℚ⟮x⟯ * 2 = n.totient at hdegree
  constructor
  · intro hx
    obtain ⟨K, k, hxK, hk⟩ := exists_pow_two_extension hx ℚ
    have hle : ℚ⟮x⟯ ≤ K := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK)
    have hd : finrank ℚ ℚ⟮x⟯ ∣ 2 ^ k := hk ▸ finrank_dvd_of_le_right hle
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact ⟨l + 1, by rw [← hdegree, hl, pow_succ]⟩
  · rintro ⟨k, hk⟩
    have hd : finrank ℚ ℚ⟮x⟯ ∣ 2 ^ k := ⟨2, hk.symm.trans hdegree.symm⟩
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact constructible_of_abelian l ℚ⟮x⟯ hl (mem_adjoin_simple_self ℚ x)

end NumberTheory.GaussWantzel

end MathlibExt.NumberTheory.GaussWantzelWanted
