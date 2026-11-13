/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Degree of the real cyclotomic polynomial

This file records the degree formula for the real cyclotomic polynomial
`realCyclotomicPolynomial n`: for `2 < n`, its `natDegree` is half of Euler's
totient `n.totient`.
-/

namespace MetaMathlibExt

/-- For `2 < n`, `n.totient` is even and the `natDegree` of the real cyclotomic
polynomial `realCyclotomicPolynomial n` equals `n.totient / 2`. The `Even`
conjunct makes the source's exact half machine-visible under natural-number
division.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials
of Algebraic Cosine Values at Rational Multiples of π", Journal of Integer
Sequences 19 (2016), source lines 83–90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 `15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455`
normalized no-final-newline span SHA-256
`e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039`

Proves `Wanted` entry `natDegree_realCyclotomicPolynomial`.
-/
theorem natDegree_realCyclotomicPolynomial (n : ℕ) (hn : 2 < n) :
    Even n.totient ∧ (realCyclotomicPolynomial n).natDegree = n.totient / 2 := by
  have hn0 : n ≠ 0 := by omega
  have hn0' : 0 < n := by omega
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) with hζdef
  set α : ℂ := ζ + ζ⁻¹ with hαdef
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζne : ζ ≠ 0 := hprim.ne_zero hn0
  -- Conjugation sends `ζ` to `ζ⁻¹` and fixes `α`.
  have hcw : starRingEnd ℂ (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := by
    simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast,
      map_ofNat]
    ring
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := by
    rw [hζdef, ← Complex.exp_conj, hcw, Complex.exp_neg]
  have hconjα : starRingEnd ℂ α = α := by
    have h1 : starRingEnd ℂ ζ⁻¹ = ζ := by rw [map_inv₀, hconj, inv_inv]
    rw [hαdef, map_add, hconj, h1, add_comm]
  -- Integrality over `ℤ` and over `ℚ`.
  have hζZ : IsIntegral ℤ ζ := hprim.isIntegral hn0'
  have hζZi : IsIntegral ℤ ζ⁻¹ := by
    refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
    · have e : (Polynomial.X ^ n - 1 : Polynomial ℤ)
          = Polynomial.X ^ n - Polynomial.C 1 := by
        rw [Polynomial.C_1]
      rw [e]
      exact Polynomial.monic_X_pow_sub_C 1 (ne_of_gt hn0')
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one]
      rw [inv_pow, hprim.pow_eq_one, inv_one, sub_self]
  have hαZ : IsIntegral ℤ α := hζZ.add hζZi
  have hαQ : IsIntegral ℚ α := hαZ.tower_top
  have hζQ : IsIntegral ℚ ζ := hζZ.tower_top
  -- The intermediate fields `K = ℚ(α)` and `L = ℚ(ζ)`.
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {α} with hKdef
  set L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ} with hLdef
  have hαK : α ∈ K := IntermediateField.subset_adjoin ℚ {α} (Set.mem_singleton α)
  have hζL : ζ ∈ L := IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)
  have hαL : α ∈ L := L.add_mem hζL (L.inv_mem hζL)
  have hKL : K ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαL)
  -- Manual `K`-algebra structure on `L` and the scalar tower.
  let instAlg : Algebra ↥K ↥L :=
    RingHom.toAlgebra (IntermediateField.inclusion hKL).toRingHom
  have hcoeAlg : ∀ k : ↥K, ((algebraMap ↥K ↥L k : ↥L) : ℂ) = ((k : ↥K) : ℂ) :=
    fun k => IntermediateField.coe_inclusion hKL k
  have instTower : IsScalarTower ℚ ↥K ↥L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext q
    change ((algebraMap ℚ ↥L q : ↥L) : ℂ) = _
    rw [RingHom.comp_apply, hcoeAlg]
    simp
  -- `finrank ℚ L = totient` via the cyclotomic polynomial.
  have hfinL : Module.finrank ℚ ↥L = n.totient := by
    have h1 : Module.finrank ℚ ↥L = (minpoly ℚ ζ).natDegree :=
      IntermediateField.adjoin.finrank hζQ
    have h2 : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ :=
      (Polynomial.cyclotomic_eq_minpoly_rat hprim hn0').symm
    rw [h1, h2, Polynomial.natDegree_cyclotomic]
  -- Conjugation fixes every rational polynomial in `α`.
  have hrat : ∀ a : ℚ, starRingEnd ℂ (algebraMap ℚ ℂ a) = algebraMap ℚ ℂ a := by
    intro a
    simp
  have key : ∀ p : Polynomial ℚ,
      starRingEnd ℂ (Polynomial.aeval α p) = Polynomial.aeval α p := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => rw [Polynomial.aeval_C]; exact hrat a
    | add p q hp hq => rw [Polynomial.aeval_add, map_add, hp, hq]
    | monomial m a ih =>
      have e : Polynomial.C a * Polynomial.X ^ (m + 1)
          = (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [e, Polynomial.aeval_mul, map_mul, ih, Polynomial.aeval_X, hconjα]
  have hfix : ∀ x ∈ K, starRingEnd ℂ x = x := by
    intro x hx
    have hx' : x ∈ IntermediateField.adjoin ℚ {α} := hx
    rw [IntermediateField.mem_adjoin_simple_iff] at hx'
    obtain ⟨r, s, rfl⟩ := hx'
    rw [map_div₀, key r, key s]
  -- Hence `ζ ∉ K`: otherwise `ζ = ζ⁻¹`, forcing `n ∣ 2`.
  have hζnK : ζ ∉ K := by
    intro hmem
    have h1 : starRingEnd ℂ ζ = ζ := hfix ζ hmem
    rw [hconj] at h1
    have h2 : ζ ^ 2 = 1 := by
      have h3 : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζne
      have h4 : ζ * ζ = ζ * ζ⁻¹ := by rw [h1]
      rw [pow_two, h4]
      exact h3
    have hdvd : n ∣ 2 := hprim.dvd_of_pow_eq_one 2 h2
    have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  -- Work over `L`: `y` is `ζ` viewed in `L`, `q` is `X² - αX + 1` over `K`.
  set y : ↥L := ⟨ζ, hζL⟩ with hydef
  set a : ↥K := ⟨α, hαK⟩ with hadef
  set q : Polynomial ↥K :=
    Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + 1 with hqdef
  have hcoe_a : ((a : ↥K) : ℂ) = α := rfl
  have hvaly : (IntermediateField.val L).toRingHom y = ζ := rfl
  -- Transfer of evaluations from `L` to `ℂ`.
  have htransfer : ∀ p : Polynomial ↥K,
      ((Polynomial.aeval y p : ↥L) : ℂ) = Polynomial.aeval (ζ : ℂ) p := by
    intro p
    change (IntermediateField.val L).toRingHom (Polynomial.aeval y p) = _
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
    have hcomp : ((IntermediateField.val L).toRingHom).comp (algebraMap ↥K ↥L)
        = algebraMap ↥K ℂ := by
      ext k
      change ((algebraMap ↥K ↥L k : ↥L) : ℂ) = algebraMap ↥K ℂ k
      exact hcoeAlg k
    rw [hcomp, hvaly, ← Polynomial.aeval_def]
  have hQaeval : ∀ t : Polynomial ℚ,
      (IntermediateField.val L).toRingHom (Polynomial.aeval y t)
        = Polynomial.aeval (ζ : ℂ) t := by
    intro t
    show (IntermediateField.val L).toRingHom (Polynomial.aeval y t) = _
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
    have hcompQ : ((IntermediateField.val L).toRingHom).comp (algebraMap ℚ ↥L)
        = algebraMap ℚ ℂ :=
      Subsingleton.elim _ _
    rw [hcompQ, hvaly, ← Polynomial.aeval_def]
  -- `ζ` (hence `y`) satisfies `X² - αX + 1 = 0`.
  have hval_C : Polynomial.aeval (ζ : ℂ) q = 0 := by
    have ha : algebraMap ↥K ℂ a = α := rfl
    rw [hqdef]
    simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Polynomial.aeval_one]
    rw [ha, hαdef]
    have h3 : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hζne
    have h4 : (ζ + ζ⁻¹) * ζ = ζ ^ 2 + 1 := by rw [add_mul, h3]; ring
    rw [h4]; ring
  have hval_L : Polynomial.aeval y q = 0 := by
    have hinj :=
      RingHom.injective (R := ↥L) (S := ℂ) (IntermediateField.val L).toRingHom
    have h0 : (IntermediateField.val L).toRingHom (Polynomial.aeval y q)
        = (IntermediateField.val L).toRingHom 0 := by
      rw [map_zero]
      change ((Polynomial.aeval y q : ↥L) : ℂ) = 0
      rw [htransfer]
      exact hval_C
    exact hinj h0
  -- Degree bounds for `q`.
  have h1deg : (-(Polynomial.C a * Polynomial.X) + 1 : Polynomial ↥K).degree ≤ 1 := by
    refine le_trans (Polynomial.degree_add_le _ _) ?_
    rw [Polynomial.degree_neg]
    refine max_le ?_ ?_
    · have e2 : (Polynomial.C a * Polynomial.X : Polynomial ↥K)
          = Polynomial.C a * Polynomial.X ^ 1 := by rw [pow_one]
      rw [e2]
      exact Polynomial.degree_C_mul_X_pow_le 1 a
    · rw [Polynomial.degree_one]
      decide
  have hbound : (-(Polynomial.C a * Polynomial.X) + 1 : Polynomial ↥K).degree < 2 :=
    lt_of_le_of_lt h1deg (by decide)
  have hmonic_q : q.Monic := by
    have e : (Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + 1 : Polynomial ↥K)
        = Polynomial.X ^ 2 + (-(Polynomial.C a * Polynomial.X) + 1) := by ring
    rw [hqdef, e]
    exact Polynomial.monic_X_pow_add hbound
  have hq0 : q ≠ 0 := hmonic_q.ne_zero
  have hqdeg : q.natDegree ≤ 2 := by
    have e : (Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + 1 : Polynomial ↥K)
        = Polynomial.X ^ 2 + (-(Polynomial.C a * Polynomial.X) + 1) := by ring
    rw [hqdef, e]
    have hdeg : (Polynomial.X ^ 2
        + (-(Polynomial.C a * Polynomial.X) + 1) : Polynomial ↥K).degree ≤ 2 := by
      refine le_trans (Polynomial.degree_add_le _ _) ?_
      refine max_le ?_ ?_
      · rw [Polynomial.degree_X_pow]; simp
      · exact le_of_lt hbound
    exact Polynomial.natDegree_le_of_degree_le hdeg
  -- `y` is integral over `K`, with minpoly of degree exactly 2.
  have hζKint : IsIntegral ↥K y := ⟨q, hmonic_q, hval_L⟩
  have hmin_le : (minpoly ↥K y).natDegree ≤ 2 := by
    have hdvd : minpoly ↥K y ∣ q := minpoly.dvd ↥K y hval_L
    exact le_trans (Polynomial.natDegree_le_of_dvd hdvd hq0) hqdeg
  have hmin_ne1 : (minpoly ↥K y).natDegree ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := (minpoly.natDegree_eq_one_iff).mp h1
    have hkk : ((k : ↥K) : ℂ) = ζ := by
      have h2 := congrArg (fun w : ↥L => ((w : ↥L) : ℂ)) hk
      rw [hcoeAlg] at h2
      exact h2
    have hmemK : ζ ∈ K := by
      have hkK : ((k : ↥K) : ℂ) ∈ K := k.property
      rw [hkk] at hkK
      exact hkK
    exact hζnK hmemK
  have hmin_pos : 1 ≤ (minpoly ↥K y).natDegree := by
    rcases Nat.eq_zero_or_pos (minpoly ↥K y).natDegree with h0 | hpos
    · exfalso
      have hC : minpoly ↥K y = Polynomial.C ((minpoly ↥K y).coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero h0
      have hae : Polynomial.aeval y (minpoly ↥K y) = 0 := minpoly.aeval ↥K y
      rw [hC, Polynomial.aeval_C] at hae
      have hinj := RingHom.injective (R := ↥K) (S := ↥L) (algebraMap ↥K ↥L)
      have hc0 : (minpoly ↥K y).coeff 0 = 0 := hinj (by simpa using hae)
      have hmp0 : minpoly ↥K y = 0 := by rw [hC, hc0, Polynomial.C_0]
      exact minpoly.ne_zero hζKint hmp0
    · exact hpos
  -- `y` generates `L` over `K`, so `finrank K L = 2`.
  have htop : IntermediateField.adjoin ↥K ({y} : Set ↥L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hzC : ((z : ↥L) : ℂ) ∈ L := z.property
    have hzL : ((z : ↥L) : ℂ) ∈ IntermediateField.adjoin ℚ {ζ} := hzC
    rw [IntermediateField.mem_adjoin_simple_iff] at hzL
    obtain ⟨r, s, hrs⟩ := hzL
    refine (IntermediateField.mem_adjoin_simple_iff ↥K z).mpr
      ⟨r.map (algebraMap ℚ ↥K), s.map (algebraMap ℚ ↥K), ?_⟩
    have hinjL :=
      RingHom.injective (R := ↥L) (S := ℂ) (IntermediateField.val L).toRingHom
    apply hinjL
    rw [map_div₀, Polynomial.aeval_map_algebraMap ↥K y r,
      Polynomial.aeval_map_algebraMap ↥K y s, hQaeval r, hQaeval s]
    exact hrs
  have hfinKL : Module.finrank ↥K ↥L = 2 := by
    have hfr := IntermediateField.adjoin.finrank hζKint
    rw [htop] at hfr
    have heq := LinearEquiv.finrank_eq
      (IntermediateField.topEquiv (F := ↥K) (E := ↥L)).toLinearEquiv
    rw [heq] at hfr
    have h2 : (minpoly ↥K y).natDegree = 2 := by omega
    rw [hfr]
    exact h2
  -- Tower law and the transfer `ℤ → ℚ`.
  have hfinK : Module.finrank ℚ ↥K = (minpoly ℚ α).natDegree :=
    IntermediateField.adjoin.finrank hαQ
  have htower : Module.finrank ℚ ↥K * Module.finrank ↥K ↥L
      = Module.finrank ℚ ↥L :=
    Module.finrank_mul_finrank ℚ ↥K ↥L
  rw [hfinKL, hfinL] at htower
  have hmap : minpoly ℚ α = (minpoly ℤ α).map (algebraMap ℤ ℚ) := by
    have h := minpoly.isIntegrallyClosed_eq_field_fractions
      (R := ℤ) (S := ℂ) (K := ℚ) (L := ℂ) (s := α) hαZ
    simpa using h
  have hdegZ : (minpoly ℤ α).natDegree = (minpoly ℚ α).natDegree := by
    rw [hmap, Polynomial.Monic.natDegree_map (minpoly.monic hαZ)]
  refine ⟨Nat.totient_even hn, ?_⟩
  have hdef : realCyclotomicPolynomial n = minpoly ℤ α := rfl
  rw [hdef, hdegZ]
  have heven : Even n.totient := Nat.totient_even hn
  omega

end MetaMathlibExt
