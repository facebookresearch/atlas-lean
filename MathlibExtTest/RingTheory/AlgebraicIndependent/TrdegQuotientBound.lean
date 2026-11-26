/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumers reproduce the theorem type from
`Theorems/Thm_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.RingTheory.AlgebraicIndependent.TrdegQuotientBound

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod

@[expose] public section

universe u v

-- exactSource consumer: the original binders apply verbatim.
example {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le 𝔮

-- Higher-universe consumer: the statement is universe-polymorphic.
example {A : Type 1} {B : Type 2} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le 𝔮

-- Field boundary: for `A = B = ℚ` and `𝔮 = ⊥`, every prime of `ℚ` is `⊥`, so the avoidance
-- condition holds automatically for the element `s ∉ ⊥.under ℚ` produced (it only says
-- `s ≠ 0`): no specialization is excluded, and the bound applies at every prime of `ℚ`.
example : ∀ (𝔔 : Ideal ℚ) [𝔔.IsPrime],
    Algebra.trdeg (ℚ ⧸ 𝔔.under ℚ) (ℚ ⧸ 𝔔) ≤
      Algebra.trdeg (ℚ ⧸ (⊥ : Ideal ℚ).under ℚ) (ℚ ⧸ (⊥ : Ideal ℚ)) := by
  obtain ⟨s, hs, hbound⟩ :=
    Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le (A := ℚ) (B := ℚ)
      (⊥ : Ideal ℚ)
  intro 𝔔 _
  obtain rfl := Ideal.eq_bot_of_prime 𝔔
  exact hbound ⊥ le_rfl hs

/-! ### A specialization where avoidance matters

The `ℤ[X]`-algebra `ℤ[Y]` with `X ↦ 2Y`, presented as `ℤ[X][T] ⧸ ker φ` for
`φ : ℤ[X][T] → ℤ[T]`, `X ↦ 2T`, `T ↦ T`. Its generic transcendence degree is `0`. Over the
contraction of the prime `(2)` the fibre is `𝔽₂[Y]`, of degree `1`, so the bound fails there
and the theorem's element must lie in that contraction; over `(3)`, where `2` is a unit, the
fibre `𝔽₃[Y]` has degree `0`. -/

namespace TrdegQuotientBoundTest

open Polynomial

/-- `ℤ[X][T] → ℤ[T]`, `X ↦ 2T`, `T ↦ T`; its image is all of `ℤ[T]`. -/
private noncomputable def φ : ℤ[X][X] →+* ℤ[X] :=
  eval₂RingHom (eval₂RingHom (Int.castRingHom ℤ[X]) (2 * X)) X

/-- `φ` followed by reduction modulo `p`. -/
private noncomputable def ψ (p : ℕ) : ℤ[X][X] →+* (ZMod p)[X] :=
  (mapRingHom (Int.castRingHom (ZMod p))).comp φ

/-- The generic prime `ker φ`; `ℤ[X][T] ⧸ ker φ` is `ℤ[Y]` with `X ↦ 2Y`. -/
private noncomputable def genericIdeal : Ideal ℤ[X][X] := RingHom.ker φ

/-- The prime over `(p)`: the kernel of `ℤ[X][T] → ℤ[Y] → 𝔽_p[Y]`. -/
private noncomputable def fibreIdeal (p : ℕ) : Ideal ℤ[X][X] := RingHom.ker (ψ p)

private instance : genericIdeal.IsPrime := RingHom.ker_isPrime φ

private instance (p : ℕ) [Fact p.Prime] : (fibreIdeal p).IsPrime := RingHom.ker_isPrime (ψ p)

private lemma genericIdeal_le (p : ℕ) : genericIdeal ≤ fibreIdeal p := fun x hx => by
  change ψ p x = 0
  rw [ψ, RingHom.comp_apply, show φ x = 0 from hx, map_zero]

private lemma φ_two_mul_sub : φ (C 2 * X - C X) = 0 := by
  simp [φ]

/-- If `2T - X ∈ I` and `2 ∉ I`, the class of `T` is algebraic over `ℤ[X] ⧸ I.under ℤ[X]` and
generates `ℤ[X][T] ⧸ I`, so the transcendence degree is `0`. -/
private lemma trdeg_eq_zero_of_mem (I : Ideal ℤ[X][X]) [I.IsPrime]
    (ht : (C 2 * X - C X : ℤ[X][X]) ∈ I) (h2 : (2 : ℤ[X][X]) ∉ I) :
    Algebra.trdeg (ℤ[X] ⧸ I.under ℤ[X]) (ℤ[X][X] ⧸ I) = 0 := by
  have hmk : ∀ a : ℤ[X], (algebraMap (ℤ[X] ⧸ I.under ℤ[X]) (ℤ[X][X] ⧸ I) :
      ℤ[X] ⧸ I.under ℤ[X] →+* ℤ[X][X] ⧸ I) (Ideal.Quotient.mk (I.under ℤ[X]) a) =
        Ideal.Quotient.mk I (C a) := fun _ => rfl
  have hT : IsAlgebraic (ℤ[X] ⧸ I.under ℤ[X]) (Ideal.Quotient.mk I X) := by
    refine ⟨C (Ideal.Quotient.mk (I.under ℤ[X]) 2) * X - C (Ideal.Quotient.mk (I.under ℤ[X]) X),
      fun h => h2 ?_, ?_⟩
    · have h1 := congrArg (fun q => q.coeff 1) h
      simp only [coeff_sub, coeff_C_mul_X, coeff_C, ↓reduceIte, one_ne_zero, sub_zero,
        coeff_zero] at h1
      have h1' := Ideal.mem_comap.mp (Ideal.Quotient.eq_zero_iff_mem.mp h1)
      rwa [map_ofNat] at h1'
    · rw [map_sub, map_mul, aeval_C, aeval_X, aeval_C, hmk, hmk, ← map_mul, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact ht
  have : Algebra.IsAlgebraic (ℤ[X] ⧸ I.under ℤ[X]) (ℤ[X][X] ⧸ I) := by
    refine ⟨fun y => (Algebra.isAlgebraic_adjoin_singleton_iff (R := ℤ[X] ⧸ I.under ℤ[X])
      (s := Ideal.Quotient.mk I X)).mpr hT y ?_⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction f using Polynomial.induction_on with
    | C a => rw [← hmk]; exact Subalgebra.algebraMap_mem _ _
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem h (Algebra.subset_adjoin rfl)
  exact trdeg_eq_zero

private lemma trdeg_generic :
    Algebra.trdeg (ℤ[X] ⧸ genericIdeal.under ℤ[X]) (ℤ[X][X] ⧸ genericIdeal) = 0 :=
  trdeg_eq_zero_of_mem _ φ_two_mul_sub fun h => by
    change φ 2 = 0 at h
    rw [map_ofNat] at h
    exact two_ne_zero h

private lemma trdeg_fibre_three :
    Algebra.trdeg (ℤ[X] ⧸ (fibreIdeal 3).under ℤ[X]) (ℤ[X][X] ⧸ fibreIdeal 3) = 0 := by
  refine trdeg_eq_zero_of_mem _ ?_ fun h => ?_
  · change ψ 3 _ = 0
    rw [ψ, RingHom.comp_apply, φ_two_mul_sub, map_zero]
  · change ψ 3 2 = 0 at h
    rw [map_ofNat, ← C_ofNat, C_eq_zero] at h
    exact absurd h (by decide)

/-- Over the contraction of `(2)` the class of `T` is transcendental: the fibre is `𝔽₂[T]`. -/
private lemma trdeg_fibre_two_ne_zero :
    Algebra.trdeg (ℤ[X] ⧸ (fibreIdeal 2).under ℤ[X]) (ℤ[X][X] ⧸ fibreIdeal 2) ≠ 0 := by
  set P := (fibreIdeal 2).under ℤ[X]
  let e₀ : ℤ[X] →+* ZMod 2 := (Int.castRingHom (ZMod 2)).comp (evalRingHom 0)
  have hψC : (ψ 2).comp C = C.comp e₀ := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · simp [ψ, φ, e₀]
    · simp [ψ, φ, e₀, CharTwo.two_eq_zero]
  have hP : ∀ a ∈ P, e₀ a = 0 := fun a ha =>
    C_eq_zero.mp ((RingHom.congr_fun hψC a).symm.trans ha)
  let e : ℤ[X] ⧸ P →+* ZMod 2 := Ideal.Quotient.lift P e₀ hP
  have he : Function.Injective e := by
    refine (injective_iff_map_eq_zero e).mpr fun x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    change ψ 2 (C a) = 0
    rw [← RingHom.comp_apply, hψC, RingHom.comp_apply]
    exact C_eq_zero.mpr hx
  let κ : ℤ[X][X] ⧸ fibreIdeal 2 →+* (ZMod 2)[X] := RingHom.kerLift (ψ 2)
  have hκ : κ.comp (algebraMap (ℤ[X] ⧸ P) (ℤ[X][X] ⧸ fibreIdeal 2)) = C.comp e :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun a => RingHom.congr_fun hψC a)
  have hX : κ (Ideal.Quotient.mk (fibreIdeal 2) X) = X := by
    change ψ 2 X = X
    simp [ψ, φ]
  have htr : Transcendental (ℤ[X] ⧸ P) (Ideal.Quotient.mk (fibreIdeal 2) X) := by
    rw [transcendental_iff]
    intro p hp
    have h1 := congrArg κ hp
    rw [aeval_def, hom_eval₂, hκ, hX, map_zero, ← eval₂_map, eval₂_C_X] at h1
    exact Polynomial.map_injective e he (h1.trans (Polynomial.map_zero e).symm)
  exact trdeg_ne_zero_iff.mpr ⟨⟨_, htr⟩⟩

-- Without the avoidance hypothesis the bound fails at `(2)`: the fibre there has degree `1`
-- over its contraction, the generic fibre degree `0`.
example : ¬ ∀ (𝔔 : Ideal ℤ[X][X]) [𝔔.IsPrime], genericIdeal ≤ 𝔔 →
    Algebra.trdeg (ℤ[X] ⧸ 𝔔.under ℤ[X]) (ℤ[X][X] ⧸ 𝔔) ≤
      Algebra.trdeg (ℤ[X] ⧸ genericIdeal.under ℤ[X]) (ℤ[X][X] ⧸ genericIdeal) := fun h =>
  trdeg_fibre_two_ne_zero <| nonpos_iff_eq_zero.mp <|
    (h (fibreIdeal 2) (genericIdeal_le 2)).trans_eq trdeg_generic

-- So the element the theorem produces lies in the contraction of `(2)`: that
-- specialization is excluded.
example : ∃ s : ℤ[X], s ∉ genericIdeal.under ℤ[X] ∧ s ∈ (fibreIdeal 2).under ℤ[X] := by
  obtain ⟨s, hs, hbound⟩ :=
    Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le (A := ℤ[X]) genericIdeal
  refine ⟨s, hs, not_not.mp fun h => trdeg_fibre_two_ne_zero ?_⟩
  exact nonpos_iff_eq_zero.mp
    ((hbound (fibreIdeal 2) (genericIdeal_le 2) h).trans_eq trdeg_generic)

-- Over `(3)` the fibre has degree `0` like the generic one, so the bound holds there for
-- every `s`.
example : Algebra.trdeg (ℤ[X] ⧸ (fibreIdeal 3).under ℤ[X]) (ℤ[X][X] ⧸ fibreIdeal 3) ≤
    Algebra.trdeg (ℤ[X] ⧸ genericIdeal.under ℤ[X]) (ℤ[X][X] ⧸ genericIdeal) := by
  rw [trdeg_fibre_three, trdeg_generic]

end TrdegQuotientBoundTest
