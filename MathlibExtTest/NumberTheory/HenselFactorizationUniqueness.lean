/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HenselFactorizationUniqueness
import Mathlib.NumberTheory.Padics.RingHoms

/-! Source-type consumers and boundary tests for coprime Hensel lifts. -/

open Polynomial

universe u

namespace HenselFactorizationUniquenessTest

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The two source wrappers, with every original hypothesis and conclusion.
example {T T' : Type u} [CommRing T] [CommRing T']
    (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (f : Polynomial T) (g' k' : Polynomial T') (hg' : g'.Monic)
    (hcop : IsCoprime g' k') (hfac : f.map π = g' * k') :
    ∃! g : Polynomial T, g.Monic ∧ g.map π = g' ∧ g ∣ f :=
  existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    π hπ hnil f g' k' hg' hcop hfac

example {R S : Type*} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R]
    {F : Polynomial R} (hF : F.Monic)
    {g₀ h₀ : Polynomial S} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : Polynomial R, g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g :=
  exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    π hπ hF hg₀ hh₀ hcop hF₀

-- The related local-ring source follows from the new general reflection API.
example {R k : Type*} [CommRing R] [IsLocalRing R] [Field k]
    (φ : R →+* k) (hφ : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ)
    (f g : R[X]) (hf : f.Monic) (h : IsCoprime (f.map φ) (g.map φ)) :
    IsCoprime f g := by
  have : IsLocalHom φ := ⟨fun x hx => by
    by_contra hxu
    exact hx.ne_zero (hφ ((IsLocalRing.mem_maximalIdeal x).mpr hxu))⟩
  exact hf.isCoprime_of_isCoprime_map φ h

private def reduce25 : ZMod 25 →+* ZMod 5 := ZMod.castHom (by decide) _

private theorem reduce25_nilpotent : RingHom.ker reduce25 ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  have h : ∀ x y : ZMod 25, reduce25 x = 0 → reduce25 y = 0 → x * y = 0 := by
    decide
  intro x hx y hy
  exact h x y hx hy

private noncomputable def nonmonicPolynomial : (ZMod 25)[X] := 2 * X ^ 2 - 2 * X + 5

private theorem five_eq_zero : (5 : (ZMod 5)[X]) = 0 := by
  rw [← C_ofNat]
  change C (0 : ZMod 5) = 0
  exact C_0

private theorem nonmonic_reduction :
    nonmonicPolynomial.map reduce25 = (X : (ZMod 5)[X]) * (2 * (X - 1)) := by
  simp only [nonmonicPolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, map_X, Polynomial.map_ofNat, five_eq_zero]
  ring

private theorem reduced_coprime : IsCoprime (X : (ZMod 5)[X]) (2 * (X - 1)) := by
  refine ⟨1, C 2, ?_⟩
  rw [C_ofNat]
  ring_nf
  have h4 : -(4 : (ZMod 5)[X]) = 1 := by rw [← C_ofNat, ← map_neg, ← C_1]; rfl
  rw [five_eq_zero, mul_zero, add_zero, h4]

-- A nonmonic polynomial over an Artinian thickening, with nonmonic cofactor.
example : ∃! g : (ZMod 25)[X], g.Monic ∧ g.map reduce25 = X ∧
    g ∣ nonmonicPolynomial :=
  existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    reduce25 (ZMod.castHom_surjective _) ⟨2, reduce25_nilpotent⟩
    nonmonicPolynomial X (2 * (X - 1)) monic_X reduced_coprime nonmonic_reduction

-- Identify the actual lifted factor, not just an existential smoke test.
example (g : (ZMod 25)[X]) (hg : g.Monic) (hmap : g.map reduce25 = X)
    (hdvd : g ∣ nonmonicPolynomial) : g = X - C 15 := by
  have h := existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    reduce25 (ZMod.castHom_surjective _) ⟨2, reduce25_nilpotent⟩
    nonmonicPolynomial X (2 * (X - 1)) monic_X reduced_coprime nonmonic_reduction
  apply h.unique ⟨hg, hmap, hdvd⟩
  refine ⟨monic_X_sub_C _, ?_, ⟨2 * X + 3, ?_⟩⟩
  · rw [Polynomial.map_sub, map_X, map_C]
    change X - C (0 : ZMod 5) = X
    simp
  · dsimp [nonmonicPolynomial]
    rw [C_ofNat]
    ring_nf
    have h45 : (45 : (ZMod 25)[X]) = 20 := by rw [← C_ofNat, ← C_ofNat]; rfl
    have h27 : (27 : (ZMod 25)[X]) = 2 := by rw [← C_ofNat, ← C_ofNat]; rfl
    have h20 : -(20 : (ZMod 25)[X]) = 5 := by
      rw [← C_ofNat, ← C_ofNat, ← map_neg]; rfl
    rw [h45, h27, h20]

example : ¬ nonmonicPolynomial.Monic := by
  intro h
  have hm := h.map reduce25
  rw [nonmonic_reduction] at hm
  have hlead := hm.leadingCoeff
  rw [leadingCoeff_mul, leadingCoeff_X, one_mul, ← C_ofNat,
    ← C_1, (monic_X_sub_C _).leadingCoeff_C_mul] at hlead
  exact (by decide : (2 : ZMod 5) ≠ 1) hlead

example : ¬ (2 * (X - 1) : (ZMod 5)[X]).Monic := by
  intro h
  have hlead := h.leadingCoeff
  rw [← C_ofNat, ← C_1, (monic_X_sub_C _).leadingCoeff_C_mul] at hlead
  exact (by decide : (2 : ZMod 5) ≠ 1) hlead

-- Both factors of X^2 + 1 lift to the complete DVR of 5-adic integers.

example : ∃ g h : (ℤ_[5])[X], g.Monic ∧ h.Monic ∧ g * h = X ^ 2 + 1 ∧
    g.map PadicInt.toZMod = X - C 2 ∧
    h.map PadicInt.toZMod = X - C (-2) ∧ IsCoprime g h ∧
    ∀ q : (ℤ_[5])[X], q.Monic → q.map PadicInt.toZMod = X - C 2 →
      q ∣ X ^ 2 + 1 → q = g := by
  have : IsAdicComplete (RingHom.ker (PadicInt.toZMod : ℤ_[5] →+* ZMod 5)) ℤ_[5] := by
    rw [PadicInt.ker_toZMod]
    infer_instance
  apply exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    PadicInt.toZMod (ZMod.ringHom_surjective _)
    (monic_X_pow_add (by simp)) (monic_X_sub_C _) (monic_X_sub_C _)
  · exact isCoprime_X_sub_C_of_isUnit_sub (by decide)
  · simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one,
      map_neg, C_ofNat]
    ring_nf
    have h4 : -(4 : (ZMod 5)[X]) = 1 := by rw [← C_ofNat, ← map_neg, ← C_1]; rfl
    rw [h4]

-- Without coprimality there are two distinct lifts of the same monic factor.
example : let π : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _
    (X : (ZMod 4)[X]) ≠ X - C 2 ∧
    (X : (ZMod 4)[X]).Monic ∧ (X - C 2 : (ZMod 4)[X]).Monic ∧
    (X : (ZMod 4)[X]).map π = X ∧ (X - C 2 : (ZMod 4)[X]).map π = X ∧
    (X : (ZMod 4)[X]) ∣ X ^ 2 ∧ (X - C 2 : (ZMod 4)[X]) ∣ X ^ 2 := by
  dsimp
  refine ⟨?_, monic_X, monic_X_sub_C _, by simp, ?_, ⟨X, by ring⟩, ?_⟩
  · intro h
    have hh := congrArg (fun p : (ZMod 4)[X] => p.coeff 0) h
    simp only [coeff_X_zero, coeff_sub, coeff_C_zero, zero_sub] at hh
    exact (by decide : (0 : ZMod 4) ≠ -2) hh
  · rw [Polynomial.map_sub, map_X, map_C]
    change X - C (0 : ZMod 2) = X
    simp
  · refine ⟨X + C 2, ?_⟩
    rw [C_ofNat]
    ring_nf
    rw [← C_ofNat]
    change X ^ 2 = -C (0 : ZMod 4) + X ^ 2
    simp

-- Zero polynomial and a constant factor are allowed.
example : ∃! g : (ZMod 25)[X], g.Monic ∧ g.map reduce25 = 1 ∧ g ∣ 0 := by
  exact existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    reduce25 (ZMod.castHom_surjective _) ⟨2, reduce25_nilpotent⟩
    0 1 0 monic_one isCoprime_one_left (by simp)

-- Trivial source and quotient; the nilpotence exponent may be zero.
example : ∃! g : PUnit[X], g.Monic ∧ g.map (RingHom.id PUnit) = 0 ∧ g ∣ 0 := by
  exact existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    (RingHom.id PUnit) Function.surjective_id ⟨0, Subsingleton.elim _ _⟩
    0 0 0 (monic_of_subsingleton _) ⟨0, 0, Subsingleton.elim _ _⟩
    (Subsingleton.elim _ _)

example : ∃ g h : PUnit[X], g.Monic ∧ h.Monic ∧ g * h = 0 ∧
    g.map (RingHom.id PUnit) = 0 ∧ h.map (RingHom.id PUnit) = 0 ∧ IsCoprime g h ∧
    ∀ q : PUnit[X], q.Monic → q.map (RingHom.id PUnit) = 0 → q ∣ 0 → q = g := by
  have : IsAdicComplete (RingHom.ker (RingHom.id PUnit)) PUnit := by
    have hk : RingHom.ker (RingHom.id PUnit) = ⊥ := by
      rw [← RingHom.injective_iff_ker_eq_bot]
      exact Function.injective_id
    rw [hk]
    infer_instance
  exact exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    (RingHom.id PUnit) Function.surjective_id (monic_of_subsingleton _)
    (monic_of_subsingleton _) (monic_of_subsingleton _)
    ⟨0, 0, Subsingleton.elim _ _⟩ (Subsingleton.elim _ _)

-- A nonlocal Artinian thickening also lifts nontrivial idempotents uniquely.
private def reduce36 : ZMod 36 →+* ZMod 6 := ZMod.castHom (by decide) _

private theorem reduce36_nilpotent : RingHom.ker reduce36 ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  have h : ∀ x y : ZMod 36, reduce36 x = 0 → reduce36 y = 0 → x * y = 0 := by
    decide
  intro x hx y hy
  exact h x y hx hy

example : ∃! a : ZMod 36, a * a = a ∧ reduce36 a = 4 := by
  have hfac : (X ^ 2 - X : (ZMod 36)[X]).map reduce36 =
      (X - C 4) * (X - C 3) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, C_ofNat]
    ring_nf
    have h12 : (12 : (ZMod 6)[X]) = 0 := by rw [← C_ofNat]; exact C_0
    have h7 : (7 : (ZMod 6)[X]) = 1 := by rw [← C_ofNat, ← C_1]; rfl
    rw [h12, h7]
    ring
  have hcop : IsCoprime (X - C 4 : (ZMod 6)[X]) (X - C 3) := by
    refine ⟨-1, 1, ?_⟩
    rw [C_ofNat, C_ofNat]
    ring
  have hu := existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    reduce36 (ZMod.castHom_surjective _) ⟨2, reduce36_nilpotent⟩
    (X ^ 2 - X) (X - C 4) (X - C 3) (monic_X_sub_C _) hcop hfac
  have hdvd (a : ZMod 36) (ha : a * a = a) : (X - C a) ∣ X ^ 2 - X := by
    apply dvd_iff_isRoot.mpr
    simpa [IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, pow_two] using
      sub_eq_zero.mpr ha
  refine ⟨28, ⟨by decide, by decide⟩, ?_⟩
  rintro a ⟨ha, hred⟩
  have hp : (X - C a : (ZMod 36)[X]) = X - C 28 := hu.unique
    ⟨monic_X_sub_C _, by simp [hred], hdvd a ha⟩
    ⟨monic_X_sub_C _, by
      rw [Polynomial.map_sub, map_X, map_C]
      rfl, hdvd 28 (by decide)⟩
  have hc := congrArg (fun p : (ZMod 36)[X] => p.coeff 0) hp
  simpa using hc

-- Removing monicity breaks reflection over a complete DVR.
example : IsCoprime ((1 + C 5 * X : (ℤ_[5])[X]).map PadicInt.toZMod)
    ((0 : (ℤ_[5])[X]).map PadicInt.toZMod) ∧
    ¬ IsCoprime (1 + C 5 * X : (ℤ_[5])[X]) 0 := by
  constructor
  · simp only [Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
      map_X, Polynomial.map_zero, _root_.map_ofNat, Polynomial.map_ofNat,
      five_eq_zero, zero_mul, add_zero]
    exact isCoprime_one_left
  · intro h
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp (isCoprime_zero_right.mp h)
    have hc := congrArg (fun p : (ℤ_[5])[X] => p.coeff 1) hr
    simp only [coeff_C, coeff_add, coeff_one, coeff_C_mul, coeff_X_one] at hc
    norm_num at hc

-- Coprime reduction alone does not give an integral root.
example : (X ^ 2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X - C (-2)) ∧
    IsCoprime (X - C 2 : (ZMod 5)[X]) (X - C (-2)) ∧
    ¬ ∃ a : ℤ, a ^ 2 + 1 = 0 := by
  refine ⟨?_, isCoprime_X_sub_C_of_isUnit_sub (by decide), ?_⟩
  · simp only [map_neg, C_ofNat]
    ring_nf
    have h4 : -(4 : (ZMod 5)[X]) = 1 := by rw [← C_ofNat, ← map_neg, ← C_1]; rfl
    rw [h4]
  · rintro ⟨a, ha⟩
    nlinarith [sq_nonneg a]

-- Injective homomorphisms give the nilpotence-exponent-one case.
example (f g h : ℤ[X]) (hg : g.Monic) (hcop : IsCoprime g h) (hf : f = g * h) :
    ∃! q : ℤ[X], q.Monic ∧ q.map (RingHom.id ℤ) = g ∧ q ∣ f := by
  have hnil : ∃ n : ℕ, RingHom.ker (RingHom.id ℤ) ^ n = ⊥ := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← RingHom.injective_iff_ker_eq_bot]
    exact Function.injective_id
  exact existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    (RingHom.id ℤ) Function.surjective_id hnil f g h hg hcop (by simpa using hf)

end HenselFactorizationUniquenessTest
