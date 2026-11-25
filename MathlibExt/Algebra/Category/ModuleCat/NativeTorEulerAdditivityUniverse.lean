/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import MathlibExt.RingTheory.Length.ExactEulerChain
public import MathlibExt.CategoryTheory.Monoidal.Tor.FiniteEuler

/-!
# Finite Euler additivity for the original native Tor

Actual ranges in the canonical native Tor long exact sequence give the
consecutive length relations. Their finite alternating sums telescope, with
the genuine zero boundary at the cutoff. The sum uses the literal original
native objects, arbitrary ring and module universes, and either coefficient.
The explicitly named raw cutoff sum uses `ENat.toNat`, so infinite lengths
contribute zero. It is a computational expression, not a finite Euler
characteristic without finiteness data. The guarded `torEulerCharacteristic`
remains the canonical finite Euler characteristic. All additivity results
retain explicit finite-length and eventual-vanishing hypotheses.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v
variable (R : Type u) [CommRing R]

/-- The raw cutoff sum of naturalized native Tor lengths.

Infinite `ENat` lengths contribute zero through `ENat.toNat`. Use
`CategoryTheory.torEulerCharacteristic` with `FiniteTorData` for a guarded
finite Euler characteristic. -/
def rawNativeTorEulerSum (M N : ModuleCat.{max u v} R) (cutoff : ℕ) : ℤ :=
  ∑ q ∈ Finset.range cutoff, (-1 : ℤ) ^ q *
    (Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N)).toNat

/-- A zero cutoff is the genuine empty native Euler sum. -/
@[simp]
theorem rawNativeTorEulerSum_zero (M N : ModuleCat.{max u v} R) :
    rawNativeTorEulerSum R M N 0 = 0 := by
  simp [rawNativeTorEulerSum]

/-- Valid eventual-zero cutoffs give the same literal native Euler sum. -/
theorem rawNativeTorEulerSum_eq_of_vanishing (M N : ModuleCat.{max u v} R)
    (n n' : ℕ)
    (hn : ∀ q, n ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N))
    (hn' : ∀ q, n' ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N)) :
    rawNativeTorEulerSum R M N n = rawNativeTorEulerSum R M N n' := by
  wlog hle : n ≤ n' generalizing n n'
  · exact (this n' n hn' hn (le_of_not_ge hle)).symm
  unfold rawNativeTorEulerSum
  apply Finset.sum_subset (Finset.range_mono hle)
  intro q _ hq
  have hz := hn q (by simpa only [Finset.mem_range, not_lt] using hq)
  rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp hz)]
  simp

/-- Canonical native symmetry preserves the literal cutoff sum. -/
theorem rawNativeTorEulerSum_symm (M N : ModuleCat.{max u v} R) (n : ℕ) :
    rawNativeTorEulerSum R M N n = rawNativeTorEulerSum R N M n := by
  unfold rawNativeTorEulerSum
  apply Finset.sum_congr rfl
  intro q _
  rw [nativeTor_length_symm R M N q]

/-- Positive native degrees satisfy the actual adjacent-boundary range relation. -/
theorem nativeTor_length_relation_succ (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (j : ℕ)
    (h₁ : Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₃) ≠ ⊤) :
    ((Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₁)).toNat : ℤ) -
      (Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₂)).toNat +
      (Module.length R (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).obj S.X₃)).toNat =
      (Module.length R (nativeTorConnecting R M S hS (j + 1)).hom.range).toNat +
        (Module.length R (nativeTorConnecting R M S hS j).hom.range).toNat := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  obtain ⟨_, hA⟩ := LeftDerivedDelta.LDexact_A F (j + 1) S hS
  obtain ⟨_, hB⟩ := LeftDerivedDelta.LDexact_B F (j + 1) S hS
  obtain ⟨_, hC⟩ := LeftDerivedDelta.LDexact_C F j S hS
  have hL := Module.exactPair_length_toNat R
    (nativeTorConnecting R M S hS (j + 1)).hom
    (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).map S.f).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hA) h₁
  have hM := Module.exactPair_length_toNat R
    (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).map S.f).hom
    (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).map S.g).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hB) h₂
  have hR := Module.exactPair_length_toNat R
    (((Tor (ModuleCat.{max u v} R) (j + 1)).obj M).map S.g).hom
    (nativeTorConnecting R M S hS j).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hC) h₃
  omega

/-- The actual degree-zero quotient endpoint leaves only the first boundary range. -/
theorem nativeTor_length_relation_zero (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact)
    (h₁ : Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₂) ≠ ⊤) :
    ((Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₁)).toNat : ℤ) -
      (Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₂)).toNat +
      (Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₃)).toNat =
      (Module.length R (nativeTorConnecting R M S hS 0).hom.range).toNat := by
  let F := (tensoringLeft (ModuleCat.{max u v} R)).obj M
  obtain ⟨_, hA⟩ := LeftDerivedDelta.LDexact_A F 0 S hS
  obtain ⟨_, hB⟩ := LeftDerivedDelta.LDexact_B F 0 S hS
  have hL := Module.exactPair_length_toNat R (nativeTorConnecting R M S hS 0).hom
    (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.f).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hA) h₁
  have hM := Module.exactPair_length_toNat R
    (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.f).hom
    (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.g).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hB) h₂
  have hepi := nativeTor_epi_zero R M S hS
  have hsurj := (ModuleCat.epi_iff_surjective _).mp hepi
  have hR : (Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).map S.g).hom.range).toNat =
      (Module.length R (((Tor (ModuleCat.{max u v} R) 0).obj M).obj S.X₃)).toNat := by
    rw [LinearMap.range_eq_top.mpr hsurj, Module.length_top]
  omega

/-- A real short exact sequence and a genuine zero native boundary give Euler additivity. -/
theorem rawNativeTorEulerSum_shortExactSecond (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤)
    (hn : IsZero (((Tor (ModuleCat.{max u v} R) n).obj M).obj S.X₃)) :
    rawNativeTorEulerSum R M S.X₂ n =
      rawNativeTorEulerSum R M S.X₁ n + rawNativeTorEulerSum R M S.X₃ n := by
  cases n with
  | zero => simp
  | succ n =>
    let a : ℕ → ℤ := fun q =>
      ((Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁)).toNat : ℤ) -
        (Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂)).toNat +
        (Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃)).toNat
    let r : ℕ → ℤ := fun q =>
      (Module.length R (nativeTorConnecting R M S hS q).hom.range).toNat
    have h0 : a 0 = r 0 := nativeTor_length_relation_zero R M S hS
      (h₁ 0 (Nat.zero_lt_succ n)) (h₂ 0 (Nat.zero_lt_succ n))
    have hstep : ∀ i < n, a (i + 1) = r i + r (i + 1) := by
      intro i hi
      exact (nativeTor_length_relation_succ R M S hS i
        (h₁ (i + 1) (Nat.succ_lt_succ hi)) (h₂ (i + 1) (Nat.succ_lt_succ hi))
        (h₃ (i + 1) (Nat.succ_lt_succ hi))).trans (add_comm _ _)
    have he := Module.alternating_sum_of_consecutive_ranges a r n h0 hstep
    have hr : r n = 0 := by
      have hδ : nativeTorConnecting R M S hS n = 0 := hn.eq_of_src _ _
      dsimp [r]
      rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero, Module.length_eq_zero]
      rfl
    rw [hr, mul_zero] at he
    dsimp [a] at he
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at he
    unfold rawNativeTorEulerSum
    omega

/-- Honest finite native lengths and eventual zero modules permit independent valid cutoffs. -/
theorem rawNativeTorEulerSum_shortExactSecond_of_finite (M : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (n₁ n₂ n₃ : ℕ)
    (h₁ : ∀ q < n₁,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁) ≠ ⊤)
    (h₂ : ∀ q < n₂,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂) ≠ ⊤)
    (h₃ : ∀ q < n₃,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃) ≠ ⊤)
    (hz₁ : ∀ q, n₁ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₁))
    (hz₂ : ∀ q, n₂ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₂))
    (hz₃ : ∀ q, n₃ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj S.X₃)) :
    rawNativeTorEulerSum R M S.X₂ n₂ =
      rawNativeTorEulerSum R M S.X₁ n₁ + rawNativeTorEulerSum R M S.X₃ n₃ := by
  let n := max (max n₁ n₂) n₃
  have hn₁ : n₁ ≤ n := by dsimp [n]; omega
  have hn₂ : n₂ ≤ n := by dsimp [n]; omega
  have hn₃ : n₃ ≤ n := by dsimp [n]; omega
  have hlen (N : ModuleCat.{max u v} R) (k : ℕ)
      (hf : ∀ q < k, Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) ≠ ⊤)
      (hz : ∀ q, k ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj M).obj N)) (q : ℕ) :
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj M).obj N) ≠ ⊤ := by
    by_cases hq : q < k
    · exact hf q hq
    · rw [Module.length_eq_zero_iff.mpr
        (ModuleCat.isZero_iff_subsingleton.mp (hz q (Nat.le_of_not_gt hq)))]
      exact ENat.zero_ne_top
  have h := rawNativeTorEulerSum_shortExactSecond R M S hS n
    (fun q _ => hlen S.X₁ n₁ h₁ hz₁ q) (fun q _ => hlen S.X₂ n₂ h₂ hz₂ q)
    (fun q _ => hlen S.X₃ n₃ h₃ hz₃ q) (hz₃ n hn₃)
  have e₁ := rawNativeTorEulerSum_eq_of_vanishing R M S.X₁ n₁ n hz₁
    (fun q hq => hz₁ q (Nat.le_trans hn₁ hq))
  have e₂ := rawNativeTorEulerSum_eq_of_vanishing R M S.X₂ n₂ n hz₂
    (fun q hq => hz₂ q (Nat.le_trans hn₂ hq))
  have e₃ := rawNativeTorEulerSum_eq_of_vanishing R M S.X₃ n₃ n hz₃
    (fun q hq => hz₃ q (Nat.le_trans hn₃ hq))
  rw [← e₁, ← e₂, ← e₃] at h
  exact h

/-- Canonical native symmetry gives the same real short-exact additivity in the first variable. -/
theorem rawNativeTorEulerSum_shortExactFirst (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (n : ℕ)
    (h₁ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ q < n,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₃).obj N) ≠ ⊤)
    (hn : IsZero (((Tor (ModuleCat.{max u v} R) n).obj S.X₃).obj N)) :
    rawNativeTorEulerSum R S.X₂ N n =
      rawNativeTorEulerSum R S.X₁ N n + rawNativeTorEulerSum R S.X₃ N n := by
  have h := rawNativeTorEulerSum_shortExactSecond R N S hS n
    (fun q hq => by rw [nativeTor_length_symm R N S.X₁ q]; exact h₁ q hq)
    (fun q hq => by rw [nativeTor_length_symm R N S.X₂ q]; exact h₂ q hq)
    (fun q hq => by rw [nativeTor_length_symm R N S.X₃ q]; exact h₃ q hq)
    (hn.of_iso (nativeTorSymmetry R N S.X₃ n))
  rw [rawNativeTorEulerSum_symm R N S.X₂ n, rawNativeTorEulerSum_symm R N S.X₁ n,
    rawNativeTorEulerSum_symm R N S.X₃ n] at h
  exact h

/-- Actual first-variable finite-length and eventual-zero data allow distinct valid cutoffs. -/
theorem rawNativeTorEulerSum_shortExactFirst_of_finite (N : ModuleCat.{max u v} R)
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (n₁ n₂ n₃ : ℕ)
    (h₁ : ∀ q < n₁,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N) ≠ ⊤)
    (h₂ : ∀ q < n₂,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₂).obj N) ≠ ⊤)
    (h₃ : ∀ q < n₃,
      Module.length R (((Tor (ModuleCat.{max u v} R) q).obj S.X₃).obj N) ≠ ⊤)
    (hz₁ : ∀ q, n₁ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj S.X₁).obj N))
    (hz₂ : ∀ q, n₂ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj S.X₂).obj N))
    (hz₃ : ∀ q, n₃ ≤ q → IsZero (((Tor (ModuleCat.{max u v} R) q).obj S.X₃).obj N)) :
    rawNativeTorEulerSum R S.X₂ N n₂ =
      rawNativeTorEulerSum R S.X₁ N n₁ + rawNativeTorEulerSum R S.X₃ N n₃ := by
  have h := rawNativeTorEulerSum_shortExactSecond_of_finite R N S hS n₁ n₂ n₃
    (fun q hq => by rw [nativeTor_length_symm R N S.X₁ q]; exact h₁ q hq)
    (fun q hq => by rw [nativeTor_length_symm R N S.X₂ q]; exact h₂ q hq)
    (fun q hq => by rw [nativeTor_length_symm R N S.X₃ q]; exact h₃ q hq)
    (fun q hq => (hz₁ q hq).of_iso (nativeTorSymmetry R N S.X₁ q))
    (fun q hq => (hz₂ q hq).of_iso (nativeTorSymmetry R N S.X₂ q))
    (fun q hq => (hz₃ q hq).of_iso (nativeTorSymmetry R N S.X₃ q))
  rw [rawNativeTorEulerSum_symm R N S.X₂ n₂, rawNativeTorEulerSum_symm R N S.X₁ n₁,
    rawNativeTorEulerSum_symm R N S.X₃ n₃] at h
  exact h

end ModuleCat.UniverseTensor

namespace CategoryTheory

universe u
variable (R : Type u) [CommRing R]

/-- At the original universe, the existing finite Tor API is the same literal sum. -/
theorem torEulerCharacteristic_eq_rawNativeTorEulerSum {M N : ModuleCat.{u} R}
    (h : FiniteTorData R M N) :
    torEulerCharacteristic R h =
      ModuleCat.UniverseTensor.rawNativeTorEulerSum.{u,0} R M N h.cutoff := rfl

end CategoryTheory
