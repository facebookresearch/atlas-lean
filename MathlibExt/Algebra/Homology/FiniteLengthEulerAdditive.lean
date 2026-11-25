/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.RingTheory.Length.ExactEulerChain
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import MathlibExt.Algebra.Homology.FiniteLengthEuler

/-!
# Additivity of finite-length Euler characteristics

For a short exact sequence of nonnegative module complexes, the homology
long exact sequence gives consecutive range-length identities. Their finite
alternating sums telescope. With finite homology lengths and a common bound
above which homology vanishes, the Euler characteristic of the middle
complex is the sum of those of the other two complexes.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {R : Type u} [CommRing R]

/-- Exact range-length identity in each positive degree of the original
homology long exact sequence. -/
theorem homology_exact_length_range_succ
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (j : ℕ)
    (h₁ : Module.length R (S.X₁.homology (j + 1)) ≠ ⊤)
    (h₂ : Module.length R (S.X₂.homology (j + 1)) ≠ ⊤)
    (h₃ : Module.length R (S.X₃.homology (j + 1)) ≠ ⊤) :
    ((Module.length R (S.X₁.homology (j + 1))).toNat : ℤ) -
      (Module.length R (S.X₂.homology (j + 1))).toNat +
      (Module.length R (S.X₃.homology (j + 1))).toNat =
      (Module.length R (hS.δ (j + 2) (j + 1) rfl).hom.range).toNat +
        (Module.length R (hS.δ (j + 1) j rfl).hom.range).toNat := by
  have hL := Module.exactPair_length_toNat R
    (hS.δ (j + 2) (j + 1) rfl).hom (homologyMap S.f (j + 1)).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ (j + 2) (j + 1) rfl)) h₁
  have hM := Module.exactPair_length_toNat R
    (homologyMap S.f (j + 1)).hom (homologyMap S.g (j + 1)).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ (j + 1))) h₂
  have hR := Module.exactPair_length_toNat R
    (homologyMap S.g (j + 1)).hom (hS.δ (j + 1) j rfl).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ (j + 1) j rfl)) h₃
  omega

/-- The true zero endpoint of the original homology long exact sequence. -/
theorem homology_exact_length_range_zero
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (h₁ : Module.length R (S.X₁.homology 0) ≠ ⊤)
    (h₂ : Module.length R (S.X₂.homology 0) ≠ ⊤) :
    ((Module.length R (S.X₁.homology 0)).toNat : ℤ) -
      (Module.length R (S.X₂.homology 0)).toNat +
      (Module.length R (S.X₃.homology 0)).toNat =
      (Module.length R (hS.δ 1 0 rfl).hom.range).toNat := by
  have hL := Module.exactPair_length_toNat R
    (hS.δ 1 0 rfl).hom (homologyMap S.f 0).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ 1 0 rfl)) h₁
  have hM := Module.exactPair_length_toNat R
    (homologyMap S.f 0).hom (homologyMap S.g 0).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ 0)) h₂
  let : Epi S.g := hS.epi_g
  let : Epi (S.g.f 0) := inferInstance
  have hepi : Epi (homologyMap S.g 0) :=
    epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
  let : Epi (homologyMap S.g 0) := hepi
  have hsurj := (ModuleCat.epi_iff_surjective (homologyMap S.g 0)).mp hepi
  have hR : (Module.length R (homologyMap S.g 0).hom.range).toNat =
      (Module.length R (S.X₃.homology 0)).toNat := by
    rw [LinearMap.range_eq_top.mpr hsurj, Module.length_top]
  omega

/-- Euler additivity for the original short exact complexes, with actual
finite homology lengths and actual vanishing above the common bound. -/
theorem finiteLengthEulerCharacteristic_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)) (hS : S.ShortExact)
    (h₁ : FiniteLengthHomologyData R S.X₁)
    (h₂ : FiniteLengthHomologyData R S.X₂)
    (h₃ : FiniteLengthHomologyData R S.X₃) :
    finiteLengthEulerCharacteristic R h₂ =
      finiteLengthEulerCharacteristic R h₁ + finiteLengthEulerCharacteristic R h₃ := by
  let n := max (max h₁.cutoff h₂.cutoff) h₃.cutoff
  have hlen (K : ChainComplex (ModuleCat.{v} R) ℕ)
      (h : FiniteLengthHomologyData R K) (j : ℕ) :
      Module.length R (K.homology j) ≠ ⊤ := by
    by_cases hj : j < h.cutoff
    · exact h.length_ne_top j hj
    · have hz := h.vanishes j (Nat.le_of_not_gt hj)
      rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
      exact ENat.zero_ne_top
  let a : ℕ → ℤ := fun j =>
    ((Module.length R (S.X₁.homology j)).toNat : ℤ) -
      (Module.length R (S.X₂.homology j)).toNat +
      (Module.length R (S.X₃.homology j)).toNat
  let r : ℕ → ℤ := fun j =>
    (Module.length R (hS.δ (j + 1) j rfl).hom.range).toNat
  have h0 : a 0 = r 0 := homology_exact_length_range_zero S hS
    (hlen _ h₁ 0) (hlen _ h₂ 0)
  have hstep : ∀ i < n, a (i + 1) = r i + r (i + 1) := by
    intro i _
    have h := homology_exact_length_range_succ S hS i
      (hlen _ h₁ (i + 1)) (hlen _ h₂ (i + 1)) (hlen _ h₃ (i + 1))
    exact h.trans (add_comm _ _)
  have he := Module.alternating_sum_of_consecutive_ranges a r n h0 hstep
  have hn₃ : h₃.cutoff ≤ n + 1 := by dsimp [n]; omega
  have hz := h₃.vanishes (n + 1) hn₃
  have hr : r n = 0 := by
    have hδ : hS.δ (n + 1) n rfl = 0 := hz.eq_of_src _ _
    dsimp [r]
    rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero, Module.length_eq_zero]
    rfl
  rw [hr, mul_zero] at he
  have sum_eq (K : ChainComplex (ModuleCat.{v} R) ℕ)
      (h : FiniteLengthHomologyData R K) (hn : h.cutoff ≤ n + 1) :
      finiteLengthEulerCharacteristic R h =
        ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
          (Module.length R (K.homology j)).toNat := by
    unfold finiteLengthEulerCharacteristic
    apply Finset.sum_subset (Finset.range_mono hn)
    intro j _ hj
    have hz := h.vanishes j (by simpa only [Finset.mem_range, not_lt] using hj)
    rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
    simp
  rw [sum_eq _ h₁ (by dsimp [n]; omega), sum_eq _ h₂ (by dsimp [n]; omega),
    sum_eq _ h₃ (by dsimp [n]; omega)]
  dsimp [a] at he
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at he
  omega

end HomologicalComplex
