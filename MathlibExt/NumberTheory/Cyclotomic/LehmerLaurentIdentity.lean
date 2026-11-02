/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- The canonical primitive `n`-th root of unity `ζₙ = exp (2 * π * I / n)`. -/
private noncomputable def zeta (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))

private lemma zeta_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

private lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 :=
  Complex.exp_ne_zero _

private lemma zeta_pow_two_ne_one (n : ℕ) (hn : 2 < n) : (zeta n) ^ 2 ≠ 1 := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  intro h
  have hdvd : n ∣ 2 := (IsPrimitiveRoot.pow_eq_one_iff_dvd hζ 2).mp h
  have hle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma zeta_norm (n : ℕ) : ‖zeta n‖ = 1 := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))
      = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  unfold zeta
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- Complex conjugation fixes `ζₙ` up to inversion: `conj ζ = ζ⁻¹`. -/
private lemma zeta_conj (n : ℕ) :
    (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ := by
  have h1 : zeta n * (starRingEnd ℂ) (zeta n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, zeta_norm n]
    norm_num
  have h3 := congrArg (· ⁻¹) (eq_inv_of_mul_eq_one_left h1)
  simpa using h3.symm

/-- For `n > 2`, `ζₙ` is not real. -/
private lemma zeta_not_real (n : ℕ) (hn : 2 < n) :
    (starRingEnd ℂ) (zeta n) ≠ zeta n := by
  intro h
  have hc := zeta_conj n
  rw [h] at hc
  have h2 : (zeta n) ^ 2 = 1 := by
    calc (zeta n) ^ 2 = zeta n * zeta n := by ring
    _ = zeta n * (zeta n)⁻¹ := by rw [← hc]
    _ = 1 := mul_inv_cancel₀ (zeta_ne_zero n)
  exact zeta_pow_two_ne_one n hn h2

/-- The trace `s = ζ + ζ⁻¹` is real (fixed by conjugation). -/
private lemma trace_conj (n : ℕ) :
    (starRingEnd ℂ) (zeta n + (zeta n)⁻¹) = zeta n + (zeta n)⁻¹ := by
  have hc := zeta_conj n
  have hci : (starRingEnd ℂ) ((zeta n)⁻¹) = zeta n := by
    rw [map_inv₀, hc, inv_inv]
  rw [map_add, hc, hci, add_comm]

/-- Conjugation fixes every element of `ℚ⟮s⟯`, where `s = ζ + ζ⁻¹`. -/
private lemma conj_fix_adjoin (n : ℕ) (z : ℂ)
    (hz : z ∈ IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) :
    (starRingEnd ℂ) z = z := by
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact trace_conj n
  · intro x
    exact Complex.conj_ofReal x
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro x _ hx
    rw [map_inv₀, hx]
  · intro x y _ _ hx hy
    rw [map_mul, hx, hy]

/-- For `n > 2`, `ζₙ ∉ ℚ⟮s⟯`. -/
private lemma zeta_not_mem_adjoin (n : ℕ) (hn : 2 < n) :
    zeta n ∉ IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ) := by
  intro hmem
  exact zeta_not_real n hn (conj_fix_adjoin n _ hmem)

/-- `ζ⁻¹ = ζ^(n-1)`. -/
private lemma zeta_inv_eq_pow (n : ℕ) (hn : 0 < n) :
    (zeta n)⁻¹ = (zeta n) ^ (n - 1) := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have h1 : zeta n * (zeta n) ^ (n - 1) = 1 := by
    have hnp : 1 + (n - 1) = n := by omega
    calc zeta n * (zeta n) ^ (n - 1)
        = (zeta n) ^ (1 + (n - 1)) := by rw [pow_add, pow_one]
      _ = (zeta n) ^ n := by rw [hnp]
      _ = 1 := hζ.pow_eq_one
  have h2 := congrArg (· ⁻¹) (eq_inv_of_mul_eq_one_left h1)
  simpa using h2

/-- `ζₙ` is integral over `ℤ`. -/
private lemma zeta_isIntegral (n : ℕ) (hn : 0 < n) : IsIntegral ℤ (zeta n) := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  refine ⟨Polynomial.X ^ n - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
  simp [hζ.pow_eq_one]

/-- `ζₙ⁻¹` is integral over `ℤ`. -/
private lemma zeta_inv_isIntegral (n : ℕ) (hn : 0 < n) :
    IsIntegral ℤ ((zeta n)⁻¹) := by
  rw [zeta_inv_eq_pow n hn]
  exact (zeta_isIntegral n hn).pow _

/-- `s = ζ + ζ⁻¹` is integral over `ℤ`. -/
private lemma trace_isIntegral (n : ℕ) (hn : 0 < n) :
    IsIntegral ℤ (zeta n + (zeta n)⁻¹) :=
  (zeta_isIntegral n hn).add (zeta_inv_isIntegral n hn)

/-- The `ℤ`-minpoly of `s` is monic. -/
private lemma psi_monic (n : ℕ) (hn : 0 < n) :
    (minpoly ℤ (zeta n + (zeta n)⁻¹)).Monic :=
  minpoly.monic (trace_isIntegral n hn)

/-- The `ℚ`-degree of `s` equals its `ℤ`-minpoly degree. -/
private lemma natDegree_psi_rat (n : ℕ) (hn : 0 < n) :
    (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree
      = (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  have hmap := minpoly.isIntegrallyClosed_eq_field_fractions
    (R := ℤ) (S := ℂ) (K := ℚ) (L := ℂ) (trace_isIntegral n hn)
  simp only [Algebra.algebraMap_self_apply] at hmap
  rw [hmap, (psi_monic n hn).natDegree_map]

/-- The quadratic relation `ζ² = s·ζ - 1`. -/
private lemma zeta_quad (n : ℕ) :
    (zeta n) ^ 2 = (zeta n + (zeta n)⁻¹) * zeta n - 1 := by
  have h0 := zeta_ne_zero n
  field_simp
  ring

/-- The quadratic `X² - sX + 1` over `ℚ⟮s⟯`, where `s = ζ + ζ⁻¹`. -/
private noncomputable def quadPoly (n : ℕ) :
    Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) :=
  Polynomial.X ^ 2 + (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
        IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ * Polynomial.X) + 1)

private lemma quadPoly_rest_degree (n : ℕ) :
    (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
        IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ *
        Polynomial.X) + 1 :
      Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree
      < 2 := by
  compute_degree
  decide

private lemma quadPoly_monic (n : ℕ) : (quadPoly n).Monic :=
  Polynomial.monic_X_pow_add (quadPoly_rest_degree n)

private lemma quadPoly_natDegree (n : ℕ) : (quadPoly n).natDegree = 2 := by
  have hlt : (-(Polynomial.C ⟨zeta n + (zeta n)⁻¹,
          IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩ *
          Polynomial.X) + 1 :
        Polynomial (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree
        < (Polynomial.X ^ 2 : Polynomial
          (IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))).degree := by
    rw [Polynomial.degree_X_pow]
    exact quadPoly_rest_degree n
  have hdeg : (quadPoly n).degree = 2 := by
    have h := Polynomial.degree_add_eq_left_of_degree_lt hlt
    rwa [Polynomial.degree_X_pow] at h
  have hnat := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  exact hnat

private lemma quadPoly_aeval (n : ℕ) :
    Polynomial.aeval (zeta n) (quadPoly n) = 0 := by
  have hq := zeta_quad n
  have hcoe : algebraMap ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)) ℂ
      ⟨zeta n + (zeta n)⁻¹, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩
      = zeta n + (zeta n)⁻¹ := rfl
  unfold quadPoly
  simp only [map_add, map_neg, map_mul, map_pow, map_one, Polynomial.aeval_X,
    Polynomial.aeval_C, hcoe]
  linear_combination hq

/-- The minpoly of `ζ` over `ℚ⟮s⟯` has degree 2. -/
private lemma minpoly_K1_natDegree_eq_two (n : ℕ) (hn : 2 < n) :
    (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n)).natDegree = 2 := by
  have hQ : IsIntegral ℚ (zeta n) := (zeta_isIntegral n (by omega)).tower_top
  have hint : IsIntegral ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n) :=
    hQ.tower_top
  have hupper : (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n)).natDegree ≤ 2 := by
    have hdvd : minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
        (zeta n) ∣ quadPoly n :=
      minpoly.dvd _ _ (quadPoly_aeval n)
    calc (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
            (zeta n)).natDegree
          ≤ (quadPoly n).natDegree :=
            (minpoly.monic hint).natDegree_le_of_dvd (quadPoly_monic n).ne_zero hdvd
        _ = 2 := quadPoly_natDegree n
  have hlower : 2 ≤ (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
      (zeta n)).natDegree := by
    have hpos := minpoly.natDegree_pos hint
    by_contra hlt
    have h1 : (minpoly ↥(IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ))
        (zeta n)).natDegree = 1 := by omega
    rw [minpoly.natDegree_eq_one_iff] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : ℂ) = zeta n := hc
    have hmem := c.property
    rw [hc'] at hmem
    exact zeta_not_mem_adjoin n hn hmem
  omega

/-- `ℚ⟮s⟯`, the base field for the quadratic step, where `s = ζ + ζ⁻¹`. -/
private noncomputable abbrev baseField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)

/-- Every element of `ℚ⟮ζ⟯` is a `ℚ⟮s⟯`-affine combination of `1` and `ζ`. -/
private lemma mem_affine (n : ℕ) (w : ℂ)
    (hw : w ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :
    ∃ a b : ↥(baseField n),
      algebraMap ↥(baseField n) ℂ a + algebraMap ↥(baseField n) ℂ b * zeta n = w := by
  have hmem_s : zeta n + (zeta n)⁻¹ ∈ baseField n :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hw
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  · intro q
    exact ⟨algebraMap ℚ ↥(baseField n) q, 0, by simp⟩
  · intro x y _ _ ihx ihy
    obtain ⟨a₁, b₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, h₂⟩ := ihy
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    simp only [map_add]
    linear_combination h₁ + h₂
  · intro x _ ihx
    obtain ⟨a, b, h⟩ := ihx
    by_cases hu : algebraMap ↥(baseField n) ℂ a
        + algebraMap ↥(baseField n) ℂ b * zeta n = 0
    · refine ⟨0, 0, ?_⟩
      rw [← h, hu, inv_zero]
      simp
    · have hca : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a)
          = algebraMap ↥(baseField n) ℂ a :=
        conj_fix_adjoin n _ a.property
      have hcb : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ b)
          = algebraMap ↥(baseField n) ℂ b :=
        conj_fix_adjoin n _ b.property
      have hcu : (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
            + algebraMap ↥(baseField n) ℂ b * zeta n)
            = algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹ := by
        rw [map_add, map_mul, hca, hcb, zeta_conj n]
      have hN0 : (algebraMap ↥(baseField n) ℂ a
            + algebraMap ↥(baseField n) ℂ b * zeta n)
            * (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n) ≠ 0 :=
        mul_ne_zero hu (by
          intro h0
          apply hu
          have h1 := congrArg (starRingEnd ℂ) h0
          simpa using h1)
      have hzz : zeta n * (zeta n)⁻¹ = 1 := mul_inv_cancel₀ (zeta_ne_zero n)
      have hs' : algebraMap ↥(baseField n) ℂ ⟨zeta n + (zeta n)⁻¹, hmem_s⟩
          = zeta n + (zeta n)⁻¹ := rfl
      have hNval : (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n)
              * (starRingEnd ℂ) (algebraMap ↥(baseField n) ℂ a
                + algebraMap ↥(baseField n) ℂ b * zeta n)
            = algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
        rw [hcu]
        simp only [map_add, map_mul, map_pow, hs']
        linear_combination (algebraMap ↥(baseField n) ℂ b ^ 2) * hzz
      have hN'0 : a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2 ≠ 0 := by
        intro hz
        apply hN0
        rw [hNval, hz, map_zero]
      refine ⟨(a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
          / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2),
        (-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2), ?_⟩
      rw [← h]
      have hinv : (zeta n)⁻¹ = (zeta n + (zeta n)⁻¹) - zeta n := by ring
      have hNv0 : algebraMap ↥(baseField n) ℂ
          (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) ≠ 0 := by
        intro hz
        apply hN'0
        exact Subtype.val_injective
          (show ((a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2 :
            ↥(baseField n)) : ℂ) = ((0 : ↥(baseField n)) : ℂ) from hz)
      have hCeq : (algebraMap ↥(baseField n) ℂ
              ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            + algebraMap ↥(baseField n) ℂ
              ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              * zeta n)
            = (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹)
            / algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
        simp only [map_div₀, map_add, map_mul, map_neg, map_pow]
        rw [div_mul_eq_mul_div, ← add_div]
        congr 1
        linear_combination (algebraMap ↥(baseField n) ℂ b) * hs'
          - (algebraMap ↥(baseField n) ℂ b) * hinv
      have hCN : (algebraMap ↥(baseField n) ℂ
              ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            + algebraMap ↥(baseField n) ℂ
              ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              * zeta n)
            * algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
            = (algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹) := by
        rw [hCeq]
        exact div_mul_cancel₀ _ hNv0
      have key : (algebraMap ↥(baseField n) ℂ a
            + algebraMap ↥(baseField n) ℂ b * zeta n)
            * (algebraMap ↥(baseField n) ℂ
              ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
            + algebraMap ↥(baseField n) ℂ
              ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              * zeta n) = 1 := by
        have h1 : ((algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n)
              * (algebraMap ↥(baseField n) ℂ
                ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                  / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              + algebraMap ↥(baseField n) ℂ
                ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                * zeta n))
              * algebraMap ↥(baseField n) ℂ
                (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
            = algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
          calc ((algebraMap ↥(baseField n) ℂ a
                + algebraMap ↥(baseField n) ℂ b * zeta n)
                * (algebraMap ↥(baseField n) ℂ
                  ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                    / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                + algebraMap ↥(baseField n) ℂ
                  ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                  * zeta n))
                * algebraMap ↥(baseField n) ℂ
                  (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
              = (algebraMap ↥(baseField n) ℂ a
                + algebraMap ↥(baseField n) ℂ b * zeta n)
                * ((algebraMap ↥(baseField n) ℂ
                  ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                    / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                + algebraMap ↥(baseField n) ℂ
                  ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                  * zeta n)
                * algebraMap ↥(baseField n) ℂ
                  (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)) := by
                ring
            _ = (algebraMap ↥(baseField n) ℂ a
                + algebraMap ↥(baseField n) ℂ b * zeta n)
                * (algebraMap ↥(baseField n) ℂ a
                + algebraMap ↥(baseField n) ℂ b * (zeta n)⁻¹) := by
                rw [hCN]
            _ = algebraMap ↥(baseField n) ℂ
                (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
                rw [← hcu]
                exact hNval
        have h2 : ((algebraMap ↥(baseField n) ℂ a
              + algebraMap ↥(baseField n) ℂ b * zeta n)
              * (algebraMap ↥(baseField n) ℂ
                ((a + b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩)
                  / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
              + algebraMap ↥(baseField n) ℂ
                ((-b) / (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2))
                * zeta n))
              * algebraMap ↥(baseField n) ℂ
                (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2)
            = 1 * algebraMap ↥(baseField n) ℂ
              (a ^ 2 + a * b * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩ + b ^ 2) := by
          rw [h1, one_mul]
        exact mul_right_cancel₀ hNv0 h2
      exact eq_inv_of_mul_eq_one_right key
  · intro x y _ _ ihx ihy
    obtain ⟨a₁, b₁, h₁⟩ := ihx
    obtain ⟨a₂, b₂, h₂⟩ := ihy
    refine ⟨a₁ * a₂ - b₁ * b₂,
      a₁ * b₂ + a₂ * b₁ + b₁ * b₂ * ⟨zeta n + (zeta n)⁻¹, hmem_s⟩, ?_⟩
    have hq := zeta_quad n
    have hs' : algebraMap ↥(baseField n) ℂ ⟨zeta n + (zeta n)⁻¹, hmem_s⟩
        = zeta n + (zeta n)⁻¹ := rfl
    rw [← h₁, ← h₂]
    simp only [map_add, map_sub, map_mul, hs']
    linear_combination (-(algebraMap ↥(baseField n) ℂ b₁
      * algebraMap ↥(baseField n) ℂ b₂)) * hq

/-- `ℚ⟮s⟯ ≤ ℚ⟮ζ⟯`. -/
private lemma baseField_le (n : ℕ) :
    baseField n ≤ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [hx]
  apply add_mem
  · exact IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  · exact inv_mem (IntermediateField.mem_adjoin_simple_self ℚ (zeta n))

/-- `finrank ℚ ℚ⟮ζ⟯ = φ(n)`. -/
private lemma finrank_adjoin_zeta (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) = n.totient := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have hInt : IsIntegral ℚ (zeta n) := (zeta_isIntegral n hn).tower_top
  rw [IntermediateField.adjoin.finrank hInt,
    ← Polynomial.cyclotomic_eq_minpoly_rat hζ hn,
    Polynomial.natDegree_cyclotomic]

/-- `finrank ℚ ℚ⟮s⟯ = natDegree (minpoly ℚ s)`. -/
private lemma finrank_adjoin_trace (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ ↥(baseField n)
      = (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree :=
  IntermediateField.adjoin.finrank ((trace_isIntegral n hn).tower_top)

/-- Tower algebra `ℚ⟮s⟯ → ℚ⟮ζ⟯` from the inclusion. -/
private noncomputable instance towerAlgebra (n : ℕ) : Algebra ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  (IntermediateField.inclusion (baseField_le n)).toRingHom.toAlgebra

/-- Tower property for `ℚ → ℚ⟮s⟯ → ℚ⟮ζ⟯`. -/
private noncomputable instance towerIsScalarTower (n : ℕ) : IsScalarTower ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    have hcomm := (IntermediateField.inclusion (baseField_le n)).commutes x
    have hdef : ∀ y : ↥(baseField n),
        algebraMap ↥(baseField n)
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) y
        = IntermediateField.inclusion (baseField_le n) y := fun y => rfl
    rw [hdef]
    exact hcomm)

/-- The tower algebra acts by inclusion. -/
private lemma towerAlgebra_apply (n : ℕ) (c : ↥(baseField n)) :
    algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
    = IntermediateField.inclusion (baseField_le n) c := rfl

/-- Coercion of the tower inclusion is the field coercion. -/
private lemma towerCoe (n : ℕ) (c : ↥(baseField n)) :
    ((algebraMap ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) c
      : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
    = algebraMap ↥(baseField n) ℂ c := by
  rw [towerAlgebra_apply, IntermediateField.coe_inclusion]
  simp only [IntermediateField.algebraMap_apply]

/-- Push coercions out of `ℚ⟮ζ⟯` operations. -/
private lemma coeE_add (n : ℕ) (u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :
    ((u + v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
    = (u : ℂ) + (v : ℂ) := by simp

private lemma coeE_mul (n : ℕ) (u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :
    ((u * v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
    = (u : ℂ) * (v : ℂ) := by simp

private lemma coeE_one (n : ℕ) :
    ((1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ) = 1 := by simp

private lemma coeE_zero (n : ℕ) :
    ((0 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ) = 0 := by simp

private lemma coeE_zeta (n : ℕ) (hmemE : zeta n ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :
    (((⟨zeta n, hmemE⟩ : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) : ℂ)
    = zeta n := rfl

/-- `finrank ℚ⟮s⟯ ℚ⟮ζ⟯ = 2`. -/
private lemma finrank_baseField (n : ℕ) (hn : 2 < n) :
    Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) = 2 := by
  have hQint : IsIntegral ℚ (zeta n) :=
    (zeta_isIntegral n (by omega)).tower_top
  have hKint : IsIntegral ↥(baseField n) (zeta n) := hQint.tower_top
  have hmemE : zeta n ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) :=
    IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  have hfinQ : Module.Finite ℚ ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
    IntermediateField.adjoin.finiteDimensional hQint
  have hfin : Module.Finite ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) :=
    Module.Finite.right ℚ ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
  have h2le : 2 ≤ Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) := by
    have hindep : LinearIndependent ↥(baseField n)
        ![1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero] at hst
        have hs0 : s = 0 := by
          apply Subtype.val_injective
          have h2 := congrArg Subtype.val hst
          rw [Algebra.smul_def, coeE_mul, coeE_one, mul_one, towerCoe] at h2
          rw [coeE_zero] at h2
          exact h2
        exact ⟨hs0, rfl⟩
      · exfalso
        have e1 : t • (⟨zeta n, hmemE⟩ :
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
            = -(s • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) :=
          eq_neg_of_add_eq_zero_right hst
        have e2 : t • algebraMap ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
            = -(s • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) := by
          rw [Algebra.smul_def, ← map_mul]
          have hfield : t * (-(t⁻¹ * s)) = -s := by
            field_simp
          rw [hfield, map_neg, Algebra.smul_def, mul_one]
        have halg : algebraMap ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
            = (⟨zeta n, hmemE⟩ :
              ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) :=
          smul_right_injective _ ht (by
            change t • algebraMap ↥(baseField n)
              ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) (-(t⁻¹ * s))
              = t • (⟨zeta n, hmemE⟩ :
                ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
            rw [e2, e1])
        have hζc : (((-(t⁻¹ * s) : ↥(baseField n))) : ℂ) = zeta n := by
          have h2 := congrArg Subtype.val halg
          rw [towerCoe, coeE_zeta] at h2
          exact h2
        have hmem : zeta n ∈ baseField n := by
          rw [← hζc]
          exact (-(t⁻¹ * s)).property
        exact zeta_not_mem_adjoin n hn hmem
    have hcard := LinearIndependent.fintype_card_le_finrank hindep
    rwa [Fintype.card_fin 2] at hcard
  have hspan : Submodule.span ↥(baseField n)
      (Set.range ![1, (⟨zeta n, hmemE⟩ :
        ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))]) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨a, b, hab⟩ := mem_affine n (y : ℂ) y.property
    have hcomb : a • (1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))
        + b • (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) = y := by
      apply Subtype.ext
      rw [Algebra.smul_def, Algebra.smul_def]
      have push : ∀ u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)),
          ((u + v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = (u : ℂ) + (v : ℂ) := fun u v => rfl
      have pushm : ∀ u v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)),
          ((u * v : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = (u : ℂ) * (v : ℂ) := fun u v => rfl
      have pusho : ((1 : ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))) : ℂ)
          = 1 := rfl
      have pushz : (((⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))) : ℂ) = zeta n := rfl
      rw [push, pushm, pushm, pusho, pushz, towerCoe n a, towerCoe n b, mul_one]
      exact hab
    have hmem : y ∈ Submodule.span ↥(baseField n)
        ({1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))} : Set _) := by
      rw [Submodule.mem_span_pair]
      exact ⟨a, b, hcomb⟩
    have hset : ({1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))} : Set _)
        = Set.range ![1, (⟨zeta n, hmemE⟩ :
          ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)))] := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
      · rintro ⟨i, hi⟩
        fin_cases i
        · simp at hi
          exact Or.inl hi.symm
        · simp at hi
          exact Or.inr hi.symm
    rw [← hset]
    exact hmem
  have hle2 : Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) ≤ 2 := by
    have h := finrank_le_of_span_eq_top hspan
    calc Module.finrank ↥(baseField n)
            ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
        ≤ Fintype.card (Fin 2) := h
      _ = 2 := Fintype.card_fin 2
  have hpos : 0 < Module.finrank ↥(baseField n)
      ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) := Module.finrank_pos
  omega

/-- Tower equation: `deg ℚ s * 2 = φ(n)`. -/
private lemma tower_degree_eq (n : ℕ) (hn : 2 < n) :
    (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree * 2 = n.totient := by
  have h := Module.finrank_mul_finrank ℚ ↥(baseField n)
    ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ))
  rwa [finrank_adjoin_trace n (by omega),
    finrank_baseField n hn, finrank_adjoin_zeta n (by omega)] at h

/-- The `ℤ`-minpoly degree of `s` is `φ(n)/2`. -/
private lemma natDegree_psi_eq (n : ℕ) (hn : 2 < n) :
    (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree = n.totient / 2 := by
  have htow := tower_degree_eq n hn
  obtain ⟨d, hd⟩ := Nat.totient_even hn
  have he : (minpoly ℚ (zeta n + (zeta n)⁻¹)).natDegree = d := by omega
  rw [← natDegree_psi_rat n (by omega), he]
  omega

/-- For `2 < n`, `n.totient` is even and the `natDegree` of the real cyclotomic
polynomial `realCyclotomicPolynomial n` equals `n.totient / 2`. The `Even`
conjunct makes the source's exact half machine-visible under natural-number
division.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials
of Algebraic Cosine Values at Rational Multiples of π", Journal of Integer
Sequences 19 (2016), source lines 83–90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex

Proves `Wanted` entry `natDegree_realCyclotomicPolynomial`.
-/
theorem natDegree_realCyclotomicPolynomial (n : ℕ) (hn : 2 < n) :
    Even n.totient ∧ (realCyclotomicPolynomial n).natDegree = n.totient / 2 :=
  ⟨Nat.totient_even hn, natDegree_psi_eq n hn⟩

/-- The cleared polynomial `R(X) = Σₖ aₖ X^(e-k) (X²+1)^k`, where `ψ = Σₖ aₖ X^k`
is the real cyclotomic polynomial of degree `e`. -/
private noncomputable def clearPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + 1),
    Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
        * (Polynomial.X ^ 2 + 1) ^ k)

/-- `R(ζ) = 0`. -/
private lemma clearPoly_aeval (n : ℕ) :
    Polynomial.aeval (zeta n) (clearPoly n) = 0 := by
  have hψ0 : Polynomial.aeval (zeta n + (zeta n)⁻¹)
      (minpoly ℤ (zeta n + (zeta n)⁻¹)) = 0 :=
    minpoly.aeval ℤ _
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range (e + 1),
      Polynomial.aeval (zeta n)
        (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
          * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k))
      = (zeta n) ^ e * (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * (zeta n + (zeta n)⁻¹) ^ k) := by
    intro k hk
    have hke : k ≤ e := by
      have hmem := Finset.mem_range.mp hk
      omega
    simp only [map_mul, map_pow, map_add, map_one, Polynomial.aeval_C,
      Polynomial.aeval_X]
    have hZ : (zeta n) ^ 2 + 1 = zeta n * (zeta n + (zeta n)⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ (zeta_ne_zero n)]
      ring
    have hpow : (zeta n) ^ (e - k) * (zeta n) ^ k = (zeta n) ^ e := by
      rw [← pow_add, Nat.sub_add_cancel hke]
    rw [hZ, mul_pow]
    linear_combination (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (zeta n + (zeta n)⁻¹) ^ k) * hpow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsum2 : (∑ k ∈ Finset.range (e + 1),
        (algebraMap ℤ ℂ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
          * (zeta n + (zeta n)⁻¹) ^ k))
      = Polynomial.aeval (zeta n + (zeta n)⁻¹)
        (minpoly ℤ (zeta n + (zeta n)⁻¹)) := by
    have h := Polynomial.as_sum_range_C_mul_X_pow (minpoly ℤ (zeta n + (zeta n)⁻¹))
    have h2 := congrArg (Polynomial.aeval (zeta n + (zeta n)⁻¹)) h
    simp only [map_sum, Polynomial.aeval_C, map_mul, map_pow,
      Polynomial.aeval_X] at h2
    rw [← he] at h2
    rw [← h2]
  rw [hsum2, hψ0, mul_zero]

/-- Per-term degree bound: each summand has degree `≤ e + k`. -/
private lemma clearPoly_term_natDegree (n : ℕ) (k : ℕ)
    (hke : k ≤ (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree) :
    (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ ((minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree - k)
        * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
    ≤ (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree + k := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hX2 : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact one_ne_zero
  have hC : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)).natDegree
      ≤ 0 :=
    le_of_eq (Polynomial.natDegree_C _)
  have hX : (Polynomial.X ^ (e - k) : Polynomial ℤ).natDegree = e - k :=
    Polynomial.natDegree_X_pow (e - k)
  have hQ : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree = k * 2 := by
    rw [Polynomial.natDegree_pow, hX2]
  have hmul : (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree
      ≤ (Polynomial.X ^ (e - k) : Polynomial ℤ).natDegree
        + ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree :=
    Polynomial.natDegree_mul_le
  have hmul2 : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
      * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k)).natDegree
      ≤ (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)).natDegree
        + (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ k).natDegree :=
    Polynomial.natDegree_mul_le
  omega

/-- `natDegree R ≤ 2e`. -/
private lemma clearPoly_natDegree_le (n : ℕ) :
    (clearPoly n).natDegree ≤ 2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have key : ∀ t : Finset ℕ, t ⊆ Finset.range (e + 1) →
      (∑ k ∈ t, Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
      ≤ 2 * e := by
    intro t
    induction t using Finset.induction with
    | empty =>
      intro _
      simp
    | @insert a s has ih =>
      intro hsub
      rw [Finset.sum_insert has]
      refine le_trans (Polynomial.natDegree_add_le _ _) (Nat.max_le.mpr ⟨?_, ?_⟩)
      · have hamem : a ∈ Finset.range (e + 1) := hsub (Finset.mem_insert_self a s)
        have hale : a ≤ e := by
          have hmem := Finset.mem_range.mp hamem
          omega
        have hle : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff a)
              * (Polynomial.X ^ (e - a) * (Polynomial.X ^ 2 + 1) ^ a)).natDegree
              ≤ e + a :=
          clearPoly_term_natDegree n a (by omega)
        omega
      · exact ih ((Finset.subset_insert a s).trans hsub)
  exact key _ (Finset.Subset.rfl)

/-- The leading coefficient of `R` is `1`. -/
private lemma clearPoly_coeff (n : ℕ) (hn : 2 < n) :
    (clearPoly n).coeff (2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree) = 1 := by
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hae : (minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e = 1 :=
    (psi_monic n (by omega)).coeff_natDegree
  have hXe : (Polynomial.X ^ (e - e) : Polynomial ℤ) = 1 := by
    rw [Nat.sub_self, pow_zero]
  have hX2monic : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_add
    rw [Polynomial.degree_one]
    decide
  have hX2deg : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact one_ne_zero
  have hmain : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e)
        * (Polynomial.X ^ (e - e) * (Polynomial.X ^ 2 + 1) ^ e)).coeff (2 * e)
      = 1 := by
    have hterm : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff e)
          * (Polynomial.X ^ (e - e) * (Polynomial.X ^ 2 + 1) ^ e))
        = (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e := by
      simp only [hae, hXe, Polynomial.C_1, one_mul]
    rw [hterm]
    have hmonic : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e).Monic :=
      hX2monic.pow e
    have hdeg : ((Polynomial.X ^ 2 + 1 : Polynomial ℤ) ^ e).natDegree = 2 * e := by
      rw [Polynomial.natDegree_pow, hX2deg]
      ring
    have hcoeff := hmonic.coeff_natDegree
    rwa [hdeg] at hcoeff
  rw [Polynomial.finsetSum_coeff, ← hmain]
  apply Finset.sum_eq_single e
  · intro k hk hke
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hkle : k < e := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hle : (Polynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
          * (Polynomial.X ^ (e - k) * (Polynomial.X ^ 2 + 1) ^ k)).natDegree
          ≤ e + k :=
      clearPoly_term_natDegree n k (by omega)
    omega
  · intro hcon
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self e)) hcon

/-- `R` is monic of degree `2e`. -/
private lemma clearPoly_natDegree (n : ℕ) (hn : 2 < n) :
    (clearPoly n).natDegree = 2 * (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hle := clearPoly_natDegree_le n
  have hc := clearPoly_coeff n hn
  by_contra hne
  have hlt : (clearPoly n).natDegree < 2 * e := lt_of_le_of_ne hle hne
  have h0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
  rw [hc] at h0
  exact one_ne_zero h0

private lemma clearPoly_monic (n : ℕ) (hn : 2 < n) : (clearPoly n).Monic := by
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have heq := clearPoly_natDegree n hn
  have hc := clearPoly_coeff n hn
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [heq]
  exact hc

/-- `R = Φₙ`. -/
private lemma clearPoly_eq (n : ℕ) (hn : 2 < n) :
    clearPoly n = Polynomial.cyclotomic n ℤ := by
  have hζ := zeta_isPrimitiveRoot n (by omega)
  have hP : Polynomial.cyclotomic n ℤ = minpoly ℤ (zeta n) :=
    Polynomial.cyclotomic_eq_minpoly hζ (by omega)
  have hdvd : Polynomial.cyclotomic n ℤ ∣ clearPoly n := by
    rw [hP]
    apply minpoly.isIntegrallyClosed_dvd (zeta_isIntegral n (by omega))
    exact clearPoly_aeval n
  have hdegP : (Polynomial.cyclotomic n ℤ).natDegree = n.totient :=
    Polynomial.natDegree_cyclotomic n ℤ
  have he := natDegree_psi_eq n hn
  have hRdeg := clearPoly_natDegree n hn
  have hle : (clearPoly n).natDegree ≤ (Polynomial.cyclotomic n ℤ).natDegree := by
    rw [hRdeg, hdegP, he]
    obtain ⟨d, hd⟩ := Nat.totient_even hn
    omega
  have h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.cyclotomic.monic n ℤ) (clearPoly_monic n hn) hdvd hle
  exact h

/-- Laurent transfer: `toLaurent R = T^d · ψ(T + T⁻¹)`. -/
private lemma transfer (n : ℕ) (hn : 2 < n) :
    Polynomial.toLaurent (clearPoly n)
      = LaurentPolynomial.T (((n.totient / 2 : ℕ)) : ℤ)
        * Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
          (minpoly ℤ (zeta n + (zeta n)⁻¹)) := by
  have hTS : (LaurentPolynomial.T (2 : ℤ) + 1 : LaurentPolynomial ℤ)
      = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) := by
    have h2 : (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)
        = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) := by
      have h22 : (2 : ℤ) = 1 + 1 := by norm_num
      rw [h22, LaurentPolynomial.T_add]
    have h10 : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)
        = (1 : LaurentPolynomial ℤ) := by
      have h00 : (1 : ℤ) + (-1) = 0 := by norm_num
      have hT : (LaurentPolynomial.T ((1 : ℤ) + (-1)) : LaurentPolynomial ℤ)
          = (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ) :=
        LaurentPolynomial.T_add (1 : ℤ) (-1)
      rw [h00, LaurentPolynomial.T_zero] at hT
      exact hT.symm
    rw [h2, ← h10, mul_add]
  have hT1k : ∀ k : ℕ, ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ k
      = (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)) := by
    intro k
    rw [LaurentPolynomial.T_pow, mul_one]
  unfold clearPoly
  set e := (minpoly ℤ (zeta n + (zeta n)⁻¹)).natDegree with he
  have hed : e = n.totient / 2 := by
    rw [he]
    exact natDegree_psi_eq n hn
  have hcast : ∀ k : ℕ, k ≤ e →
      ((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ) = ((((e : ℕ))) : ℤ) := by
    intro k hke
    rw [← Nat.cast_add]
    congr 1
    omega
  have hterm : ∀ k : ℕ, k ≤ e →
      (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
      = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    intro k hke
    calc (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ) + 1) ^ k
        = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) ^ k := by
          rw [hTS]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * (((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)) ^ k
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [mul_pow]
      _ = (LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
              + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k) := by
          rw [hT1k k]
      _ = ((LaurentPolynomial.T ((((e - k : ℕ))) : ℤ) : LaurentPolynomial ℤ)
            * (LaurentPolynomial.T ((((k : ℕ))) : ℤ) : LaurentPolynomial ℤ))
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          ring
      _ = (LaurentPolynomial.T (((((e - k : ℕ))) : ℤ) + ((((k : ℕ))) : ℤ)) :
              LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [← LaurentPolynomial.T_add]
      _ = (LaurentPolynomial.T ((((e : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hcast k hke]
      _ = (LaurentPolynomial.T ((((n.totient / 2 : ℕ))) : ℤ) : LaurentPolynomial ℤ)
          * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
            + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
          rw [hed]
  have haeval : Polynomial.aeval
      ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))
      (minpoly ℤ (zeta n + (zeta n)⁻¹))
      = ∑ k ∈ Finset.range (e + 1),
        LaurentPolynomial.C ((minpoly ℤ (zeta n + (zeta n)⁻¹)).coeff k)
        * ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
          + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ)) ^ k := by
    have h := Polynomial.as_sum_range_C_mul_X_pow (minpoly ℤ (zeta n + (zeta n)⁻¹))
    have h2 := congrArg
      (Polynomial.aeval ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ)
        + (LaurentPolynomial.T (-1 : ℤ) : LaurentPolynomial ℤ))) h
    simp only [map_sum, Polynomial.aeval_C, map_mul, map_pow, Polynomial.aeval_X,
      ← LaurentPolynomial.C_eq_algebraMap] at h2
    rw [← he] at h2
    rw [← h2]
  rw [map_sum, haeval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := by
    have hmem := Finset.mem_range.mp hk
    omega
  simp only [map_mul, map_pow, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X]
  have h2' : ((LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ℤ) ^ 2
      = (LaurentPolynomial.T (2 : ℤ) : LaurentPolynomial ℤ)) := by
    simpa only [Nat.cast_ofNat] using hT1k 2
  rw [hT1k (e - k), h2', hterm k hke]
  ring

/-- **Lehmer's identity for the real cyclotomic polynomial.** Let $n > 2$ be a natural number, let
$\psi_n$ be the real cyclotomic polynomial, let $\Phi_n \in \mathbb{Z}[X]$ be the $n$-th
cyclotomic polynomial, and let $\varphi$ be Euler's totient function. Then in the ring
$\mathbb{Z}[x, x^{-1}]$ of Laurent polynomials over $\mathbb{Z}$,
$x^{\varphi(n)/2} \, \psi_n(x + x^{-1}) = \Phi_n(x)$, that is,
$\psi_n(x + x^{-1}) = x^{-\varphi(n)/2} \, \Phi_n(x)$.

Proves `Wanted` entry `lehmer_cyclotomic_identity`.

Source: Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of
Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19
(2016), source lines 83-90:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex
source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455
normalized no-final-newline span SHA-256
e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039
-/
theorem lehmer_cyclotomic_identity (n : ℕ) (hn : 2 < n) :
    LaurentPolynomial.T (↑(n.totient / 2)) *
      Polynomial.aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
        (realCyclotomicPolynomial n) =
      Polynomial.toLaurent (Polynomial.cyclotomic n ℤ) := by
  have hR := clearPoly_eq n hn
  have htrans := transfer n hn
  have hdef : realCyclotomicPolynomial n
      = minpoly ℤ (zeta n + (zeta n)⁻¹) := rfl
  rw [hdef, ← hR]
  exact htrans.symm

end MetaMathlibExt
