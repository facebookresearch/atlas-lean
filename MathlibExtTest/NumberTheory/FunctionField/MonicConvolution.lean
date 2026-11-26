/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.FunctionField.MonicConvolution

/-! # Tests for weighted convolution over monic polynomials -/

open MetaMathlibExt Polynomial UniqueFactorizationMonoid

namespace MonicConvolutionTest

example (α β : (ZMod 2)[X] → ℂ) :
    monicConvPartialSum α β (1 - ((X : (ZMod 2)[X]) * X).natDegree) = 0 := by
  apply monicConvPartialSum_of_neg
  simp [natDegree_mul X_ne_zero X_ne_zero]

example {F : Type*} [Field F] (γ α β : F[X] → ℂ) :
    weightedMonicConvSum γ α β 0 = γ 1 * (α 1 * β 1) :=
  weightedMonicConvSum_zero γ α β

private theorem monicDivisors_X :
    {g : (ZMod 2)[X] | g.Monic ∧ g ∣ X} = {1, X} := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hm, hd⟩
    rcases irreducible_X.dvd_iff.mp hd with hu | ha
    · exact .inl (hm.isUnit_iff.mp hu)
    · exact .inr (eq_of_monic_of_associated hm monic_X ha.symm)
  · rintro (rfl | rfl)
    · exact ⟨monic_one, one_dvd _⟩
    · exact ⟨monic_X, dvd_rfl⟩

private noncomputable def weight (f : (ZMod 2)[X]) : ℂ :=
  if f = X then 1 else 0

-- Only X is weighted. Its two monic divisors each contribute one.
private theorem weighted_at_X :
    weightedMonicConvSum weight (fun _ => 1) (fun _ => 1) 1 = 2 := by
  classical
  have hconv : monicDirichletConv (fun _ => (1 : ℂ)) (fun _ => 1) (X : (ZMod 2)[X]) = 2 := by
    have h : (1 : (ZMod 2)[X]) ∉ ({X} : Set (ZMod 2)[X]) := by
      simp only [Set.mem_singleton_iff]
      intro he
      simpa using congrArg natDegree he
    rw [monicDirichletConv, monicDivisors_X, finsum_mem_insert _ h (Set.finite_singleton _),
      finsum_mem_singleton]
    norm_num
  unfold weightedMonicConvSum
  rw [finsum_eq_single _ X]
  · simp [monic_X, weight, hconv]
  · intro f hf
    simp [weight, hf]

-- For f = d = ℓ = X the inner cutoff is -1, so that term is dropped.
example :
    (∑ᶠ f ∈ {f : (ZMod 2)[X] | f.Monic ∧ f.natDegree ≤ 1},
      monicDirichletConv weight (fun g => (moebius g : ℂ)) f *
        ∑ᶠ d ∈ {d : (ZMod 2)[X] | d.Monic ∧ d ∣ f},
          ∑ᶠ ℓ ∈ {ℓ : (ZMod 2)[X] | ℓ.Monic ∧ ℓ ∣ d},
            (moebius ℓ : ℂ) *
              monicConvPartialSum (1 : (ZMod 2)[X] →* ℂ) (1 : (ZMod 2)[X] →* ℂ)
                (1 - (f * ℓ).natDegree)) = 2 := by
  simpa only [MonoidHom.one_apply, mul_one, one_mul, Nat.cast_one] using
    (weightedMonicConvSum_eq_of_completelyMultiplicative weight 1 1 1).symm.trans weighted_at_X

private theorem commonMonicDivisors_X (g : (ZMod 2)[X]) (hg : ¬ (X : (ZMod 2)[X]) ∣ g) :
    {ℓ : (ZMod 2)[X] | ℓ.Monic ∧ ℓ ∣ X ∧ ℓ ∣ g} = {1} := by
  ext ℓ
  simp only [Set.mem_ofPred_eq, ← and_assoc]
  change (ℓ ∈ {d : (ZMod 2)[X] | d.Monic ∧ d ∣ X} ∧ ℓ ∣ g) ↔ _
  rw [monicDivisors_X]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · rfl
    · exact (hg h).elim
  · rintro rfl
    exact ⟨.inl rfl, one_dvd _⟩

private theorem conv_one_X :
    monicDirichletConv (1 : (ZMod 2)[X] →* ℂ) (1 : (ZMod 2)[X] →* ℂ) X = 2 := by
  classical
  have h : (1 : (ZMod 2)[X]) ∉ ({X} : Set (ZMod 2)[X]) := by
    simp only [Set.mem_singleton_iff]
    intro he
    simpa using congrArg natDegree he
  rw [monicDirichletConv, monicDivisors_X, finsum_mem_insert _ h (Set.finite_singleton _),
    finsum_mem_singleton]
  norm_num

-- A unit gives one common divisor; the convolution at that unit is one.
example : monicDirichletConv (1 : (ZMod 2)[X] →* ℂ) (1 : (ZMod 2)[X] →* ℂ) (X * 1) = 2 := by
  have h : ¬ (X : (ZMod 2)[X]) ∣ 1 := fun h => irreducible_X.not_isUnit (isUnit_of_dvd_one h)
  rw [monicDirichletConv_mul_of_completelyMultiplicative 1 1 monic_X monic_one,
    commonMonicDivisors_X 1 h, finsum_mem_singleton]
  simp [monicDirichletConv_one, conv_one_X]

-- The two distinct linear factors over ZMod 2 have no nontrivial common divisor.
example (α β : (ZMod 2)[X] →* ℂ) :
    monicDirichletConv α β (X * (X + 1)) =
      monicDirichletConv α β X * monicDirichletConv α β (X + 1) := by
  have hm : (X + 1 : (ZMod 2)[X]).Monic := by simpa using monic_X_add_C (1 : ZMod 2)
  have h : ¬ (X : (ZMod 2)[X]) ∣ X + 1 := by simp [X_dvd_iff]
  rw [monicDirichletConv_mul_of_completelyMultiplicative α β monic_X hm,
    commonMonicDivisors_X _ h, finsum_mem_singleton]
  simp

-- At X * X the two common divisors give 2 * 2 and −1, not the coprime value 4.
example : monicDirichletConv (1 : (ZMod 2)[X] →* ℂ) (1 : (ZMod 2)[X] →* ℂ) (X * X) = 3 := by
  classical
  have hset : {ℓ : (ZMod 2)[X] | ℓ.Monic ∧ ℓ ∣ X ∧ ℓ ∣ X} = {1, X} := by
    simpa only [and_self] using monicDivisors_X
  have h : (1 : (ZMod 2)[X]) ∉ ({X} : Set (ZMod 2)[X]) := by
    simp only [Set.mem_singleton_iff]
    intro he
    simpa using congrArg natDegree he
  have hxx : (X /ₘ X : (ZMod 2)[X]) = 1 := by
    simpa using mul_divByMonic_cancel_left (1 : (ZMod 2)[X]) monic_X
  rw [monicDirichletConv_mul_of_completelyMultiplicative 1 1 monic_X monic_X, hset,
    finsum_mem_insert _ h (Set.finite_singleton _), finsum_mem_singleton]
  norm_num [conv_one_X, hxx, monicDirichletConv_one, irreducible_X.moebius_eq]

end MonicConvolutionTest
