/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The source-shaped consumer copies the statement type from
Theorems/Thm_Polynomial_irreducible_of_transitive_ringAut.lean in
fermats-last-theorem at commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
No individual authors are named. Only the statement type is copied here;
the importing applications and independent input certificates are new.
-/

module

public import MathlibExt.Algebra.Polynomial.IrreducibleOfCycle
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Independent clients of the root-cycle irreducibility criterion

The real quadratic has a singleton cycle and the identity automorphism.
The rational cubic uses the real rpow cube root and complex conjugation.
Every input certificate is proved before invoking irreducibility. The output
clients concern the full Galois action and the actual quotient-field property.
-/

set_option linter.mathlibStandardSet false
set_option linter.privateModule false
set_option pp.mvars.anonymous false

@[expose] public section

noncomputable section

open Polynomial

namespace IrreducibleOfCycleTest

/-- Verbatim source type, consumed through the renamed public endpoint. -/
theorem source_consumer {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits)
    (σ : L ≃+* L) (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a)
    (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup)
    (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P :=
  Polynomial.irreducible_of_cycle_on_other_roots
    P hP hPs (AlgEquiv.ofRingEquiv hσ) y₀ r n hroots hnodup hcycle hy₀

/-- The full Galois group is pretransitive, not necessarily the chosen cycle. -/
theorem full_galois_action {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits)
    (σ : L ≃ₐ[F] L)
    (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup)
    (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) :
    letI : Fact ((P.map (algebraMap F L)).Splits) := ⟨hPs⟩
    MulAction.IsPretransitive P.Gal (P.rootSet L) := by
  let : Fact ((P.map (algebraMap F L)).Splits) := ⟨hPs⟩
  exact Polynomial.Gal.galAction_isPretransitive P L
    (Polynomial.irreducible_of_cycle_on_other_roots
      P hP hPs σ y₀ r n hroots hnodup hcycle hy₀)

/-- The quotient is a field; no quotient-field assumption constructs the
inputs. -/
theorem adjoinRoot_isField {F L : Type*} [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits)
    (σ : L ≃ₐ[F] L)
    (y₀ : L) (r : ℕ → L) (n : ℕ)
    (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r)
    (hnodup : (P.map (algebraMap F L)).roots.Nodup)
    (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n))
    (hy₀ : y₀ ∉ (algebraMap F L).range) : IsField (AdjoinRoot P) :=
  AdjoinRoot.isField_iff_irreducible.mpr
    (Polynomial.irreducible_of_cycle_on_other_roots
      P hP hPs σ y₀ r n hroots hnodup hcycle hy₀)

local notation "realP" => (X ^ 2 + 1 : ℝ[X])

/-- Monicity is independent of irreducibility. -/
theorem real_monic : (realP).Monic := by
  simpa only [map_one] using monic_X_pow_add_C (1 : ℝ) (by decide : 2 ≠ 0)

/-- The explicit two linear factors certify the entire root multiset. -/
theorem real_factorization : (realP).map (algebraMap ℝ ℂ) =
    (X - C Complex.I) * (X - C (-Complex.I)) := by
  simp only [Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one]
  calc
    (X : ℂ[X]) ^ 2 + 1 = X ^ 2 - C (Complex.I ^ 2) := by simp
    _ = (X - C Complex.I) * (X - C (-Complex.I)) := by
      simp only [map_pow, map_neg]
      ring

theorem real_splits : ((realP).map (algebraMap ℝ ℂ)).Splits := by
  rw [real_factorization]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)

theorem real_roots : ((realP).map (algebraMap ℝ ℂ)).roots =
    Complex.I ::ₘ (Multiset.range 1).map (fun _ => -Complex.I) := by
  rw [real_factorization,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  simp [Multiset.range_succ]

theorem real_nodup : ((realP).map (algebraMap ℝ ℂ)).roots.Nodup := by
  rw [real_roots]
  have h : Complex.I ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  simp [Multiset.range_succ, h]

theorem real_cycle : ∀ i < 1, (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ) ((fun _ : ℕ => -Complex.I) i) =
    (fun _ : ℕ => -Complex.I) ((i + 1) % 1) := by
  intro i hi
  rfl

theorem real_nonbase : Complex.I ∉ (algebraMap ℝ ℂ).range := by
  rintro ⟨a, ha⟩
  have := congrArg Complex.im ha
  norm_num at this

/-- A closed, noncircular full-Galois-action application with n=1 and
sigma=id. -/
theorem real_full_galois_action :
    letI : Fact (((realP).map (algebraMap ℝ ℂ)).Splits) := ⟨real_splits⟩
    MulAction.IsPretransitive (realP).Gal ((realP).rootSet ℂ) :=
  full_galois_action realP real_monic real_splits (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)
    Complex.I (fun _ => -Complex.I) 1 real_roots real_nodup
    real_cycle real_nonbase

local notation "rho" => Real.rpow 2 ((3 : ℝ)⁻¹)

/-- This uses rpow, not polynomial irreducibility. -/
theorem rho_cube : rho ^ 3 = 2 :=
  Real.rpow_inv_natCast_pow (by norm_num) (by decide : (3 : ℕ) ≠ 0)

theorem rho_bounds : 1 < rho ∧ rho < 2 := by
  have hodd : Odd (3 : ℕ) := by decide
  constructor
  · apply hodd.pow_lt_pow.mp
    rw [rho_cube]
    norm_num
  · apply hodd.pow_lt_pow.mp
    rw [rho_cube]
    norm_num

theorem rho_not_integer : ¬ ∃ z : ℤ, rho = z := by
  rintro ⟨z, hz⟩
  have hb := rho_bounds
  rw [hz] at hb
  have h1 : (1 : ℤ) < z := by exact_mod_cast hb.1
  have h2 : z < (2 : ℤ) := by exact_mod_cast hb.2
  omega

theorem rho_irrational : Irrational rho :=
  irrational_nrt_of_notint_nrt 3 2 (by simpa using rho_cube)
    rho_not_integer (by decide)

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

local notation "upperRoot" => (((-rho / 2 : ℝ) : ℂ) +
  ((rho * Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I)

local notation "lowerRoot" => (((-rho / 2 : ℝ) : ℂ) -
  ((rho * Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I)

local notation "cubicP" => (X ^ 3 - 2 : ℚ[X])

local notation "cubicR" => (fun k : ℕ => ite (k % 2 = 0) upperRoot lowerRoot)

theorem cubic_sum : upperRoot + lowerRoot = -(rho : ℂ) := by
  apply Complex.ext <;> simp

theorem cubic_product : upperRoot * lowerRoot = (rho : ℂ) ^ 2 := by
  have aux (a b : ℝ) (hb : b ^ 2 = 3) :
      (((-a / 2 : ℝ) : ℂ) + ((a * b / 2 : ℝ) : ℂ) * Complex.I) *
      (((-a / 2 : ℝ) : ℂ) - ((a * b / 2 : ℝ) : ℂ) * Complex.I) =
        (a : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => a ^ 2 * x) hb
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [h]
  exact aux rho (Real.sqrt 3) sqrt_three_sq

theorem imaginary_height_pos : 0 < rho * Real.sqrt 3 / 2 :=
  div_pos
    (mul_pos (lt_trans (by norm_num) rho_bounds.1) sqrt_three_pos) (by norm_num)

theorem cubic_distinct : (rho : ℂ) ≠ upperRoot ∧
    (rho : ℂ) ≠ lowerRoot ∧ upperRoot ≠ lowerRoot := by
  have aux (a b : ℝ) (hb : 0 < b) :
      (a : ℂ) ≠ ((-a / 2 : ℝ) : ℂ) + (b : ℂ) * Complex.I ∧
      (a : ℂ) ≠ ((-a / 2 : ℝ) : ℂ) - (b : ℂ) * Complex.I ∧
      ((-a / 2 : ℝ) : ℂ) + (b : ℂ) * Complex.I ≠
        ((-a / 2 : ℝ) : ℂ) - (b : ℂ) * Complex.I := by
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
      have hi := congrArg Complex.im h <;> simp at hi <;> linarith
  exact aux rho (rho * Real.sqrt 3 / 2) imaginary_height_pos

theorem cubic_monic : (cubicP).Monic := by
  simpa only [map_ofNat] using monic_X_pow_sub_C (2 : ℚ) (by decide : 3 ≠ 0)

/-- The rpow and square-root equations give all three linear factors. -/
theorem cubic_factorization : (cubicP).map (algebraMap ℚ ℂ) =
    (X - C (rho : ℂ)) * (X - C upperRoot) * (X - C lowerRoot) := by
  have hc : (rho : ℂ) ^ 3 = 2 := by exact_mod_cast rho_cube
  have hq : (X - C upperRoot) * (X - C lowerRoot) =
      (X : ℂ[X]) ^ 2 + C (rho : ℂ) * X + C ((rho : ℂ) ^ 2) := by
    calc
      _ = X ^ 2 - C (upperRoot + lowerRoot) * X +
          C (upperRoot * lowerRoot) := by
        simp only [map_add, map_mul]
        ring
      _ = _ := by
        rw [cubic_sum, cubic_product, map_neg]
        ring
  have hf : (X - C (rho : ℂ)) * (X - C upperRoot) * (X - C lowerRoot) =
      (X : ℂ[X]) ^ 3 - 2 := by
    rw [mul_assoc, hq]
    calc
      _ = X ^ 3 - C ((rho : ℂ) ^ 3) := by
        simp only [map_pow]
        ring
      _ = _ := by rw [hc, C_ofNat]
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat] using hf.symm

theorem cubic_splits : ((cubicP).map (algebraMap ℚ ℂ)).Splits := by
  rw [cubic_factorization]
  exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

theorem cubic_roots : ((cubicP).map (algebraMap ℚ ℂ)).roots =
    (rho : ℂ) ::ₘ (Multiset.range 2).map cubicR := by
  rw [cubic_factorization,
    roots_mul (mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
      (X_sub_C_ne_zero _)),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  simp [Multiset.range_succ]
  exact Multiset.cons_swap ..

theorem cubic_nodup : ((cubicP).map (algebraMap ℚ ℂ)).roots.Nodup := by
  rw [cubic_roots]
  have h :
      ((rho : ℂ) ≠ lowerRoot ∧ (rho : ℂ) ≠ upperRoot) ∧ lowerRoot ≠ upperRoot :=
    ⟨⟨cubic_distinct.2.1, cubic_distinct.1⟩, Ne.symm cubic_distinct.2.2⟩
  simpa [Multiset.range_succ] using h

/-- Complex conjugation as a `ℚ`-algebra equivalence. -/
def cubicConj : ℂ ≃ₐ[ℚ] ℂ :=
  AlgEquiv.ofRingEquiv (f := Complex.conjAe.toRingEquiv) (by simp)

theorem cubic_cycle : ∀ i < 2,
    cubicConj (cubicR i) = cubicR ((i + 1) % 2) := by
  intro i hi
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl <;>
    simp only [cubicConj, AlgEquiv.ofRingEquiv_apply] <;>
    norm_num [sub_eq_add_neg, map_ofNat]

theorem cubic_nonbase : (rho : ℂ) ∉ (algebraMap ℚ ℂ).range := by
  rintro ⟨a, ha⟩
  apply rho_irrational
  refine ⟨a, ?_⟩
  simpa using congrArg Complex.re ha

/-- A closed quotient-field application with an independently irrational
rpow root. -/
theorem cubic_adjoinRoot_isField : IsField (AdjoinRoot cubicP) :=
  adjoinRoot_isField cubicP cubic_monic cubic_splits cubicConj
    (rho : ℂ) cubicR 2 cubic_roots cubic_nodup
    cubic_cycle cubic_nonbase

/-- Identity cannot replace conjugation on the two distinct nonreal
cubic roots. -/
theorem cubic_identity_not_cycle : ¬ (∀ i < 2,
    (RingEquiv.refl ℂ) (cubicR i) = cubicR ((i + 1) % 2)) := by
  intro h
  exact cubic_distinct.2.2 (h 0 (by norm_num))

/-- One other listed root does not enumerate this cubic's entire
root multiset. -/
theorem cubic_one_other_root_incomplete :
    ((cubicP).map (algebraMap ℚ ℂ)).roots ≠
      (rho : ℂ) ::ₘ (Multiset.range 1).map (fun _ => upperRoot) := by
  intro h
  rw [cubic_roots] at h
  have hc := congrArg Multiset.card h
  norm_num at hc

/-- n=0 is not banned by the API; the source premises themselves rule it out. -/
theorem zero_other_roots_impossible {F L : Type*}
    [Field F] [Field L] [Algebra F L]
    (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits)
    (y₀ : L) (hroots : (P.map (algebraMap F L)).roots = {y₀})
    (hy₀ : y₀ ∉ (algebraMap F L).range) : False := by
  have hd : P.natDegree = 1 := by
    rw [← Polynomial.natDegree_map (algebraMap F L),
      hPs.natDegree_eq_card_roots, hroots, Multiset.card_singleton]
  have hm : P.map (algebraMap F L) ≠ 0 := (hP.map _).ne_zero
  have hr : y₀ ∈ (P.map (algebraMap F L)).roots := by simp [hroots]
  exact hy₀ ((Splits.of_natDegree_eq_one hd).mem_range_of_isRoot hP.ne_zero
    ((mem_roots hm).mp hr))

end IrreducibleOfCycleTest
