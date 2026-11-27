/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_
of_linearPart_of_span_eq.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_
of_linearPart_of_span_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

@[expose] public section

open MvPowerSeries


private theorem mem_pow_span_X_of_coeff_eq_zero (R : Type*) [CommRing R] :
    ∀ (n : ℕ) (F : MvPowerSeries (Fin 2) R),
      (∀ m : Fin 2 →₀ ℕ, Finsupp.degree m < n → coeff m F = 0) →
        F ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ n := by
  classical
  intro n
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
      intro F hF
      let F₁ : MvPowerSeries (Fin 2) R := fun m => if m 0 = 0 then F m else 0
      have hF₁c : ∀ m : Fin 2 →₀ ℕ, coeff m F₁ = if m 0 = 0 then coeff m F else 0 := fun m => rfl
      have h1 : (X 1 : MvPowerSeries (Fin 2) R) ∣ F₁ := by
        rw [X_dvd_iff]
        intro m hm1
        rw [hF₁c]
        split_ifs with hm0
        · have hm : m = 0 := by
            ext i; fin_cases i
            · simpa using hm0
            · simpa using hm1
          subst hm
          exact hF 0 (by simp)
        · rfl
      have h0 : (X 0 : MvPowerSeries (Fin 2) R) ∣ F - F₁ := by
        rw [X_dvd_iff]
        intro m hm0
        rw [map_sub, hF₁c, if_pos hm0, sub_self]
      obtain ⟨G₁, hG₁⟩ := h1
      obtain ⟨G₀, hG₀⟩ := h0
      have hcoefX : ∀ (k : Fin 2) (G : MvPowerSeries (Fin 2) R) (m : Fin 2 →₀ ℕ),
          coeff (m + Finsupp.single k 1) (X k * G) = coeff m G := by
        intro k G m
        rw [X_def k, coeff_monomial_mul, if_pos (by simp), one_mul, add_tsub_cancel_right]
      have hG₁z : ∀ m : Fin 2 →₀ ℕ, Finsupp.degree m < n → coeff m G₁ = 0 := by
        intro m hm
        rw [← hcoefX 1 G₁ m, ← hG₁, hF₁c]
        split_ifs with h
        · exact hF _ (by rw [map_add, Finsupp.degree_single]; omega)
        · rfl
      have hG₀z : ∀ m : Fin 2 →₀ ℕ, Finsupp.degree m < n → coeff m G₀ = 0 := by
        intro m hm
        rw [← hcoefX 0 G₀ m, ← hG₀, map_sub, hF₁c]
        have : coeff (m + Finsupp.single 0 1) F = 0 := hF _
          (by rw [map_add, Finsupp.degree_single]; omega)
        rw [this]
        split_ifs <;> simp
      have e : F = X 0 * G₀ + X 1 * G₁ := by rw [← hG₀, ← hG₁]; ring
      rw [e, pow_succ']
      exact Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih G₀ hG₀z))
        (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih G₁ hG₁z))

private theorem sub_coe_truncTotal_mem_pow (R : Type*) [CommRing R] (n : ℕ)
  (F : MvPowerSeries (Fin 2) R) :
    F - ((truncTotal n F : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ n :=
  mem_pow_span_X_of_coeff_eq_zero R n _ (fun m hm => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self])

private theorem span_mk_X_le_jacobson (R : Type*) [CommRing R]
  (I : Ideal (MvPowerSeries (Fin 2) R)) :
    Ideal.span {Ideal.Quotient.mk I (X 0), Ideal.Quotient.mk I (X 1)} ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
  have key : ∀ i : Fin 2, IsUnit (Ideal.Quotient.mk I (X i) * Ideal.Quotient.mk I G + 1) := by
    intro i
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]
    apply IsUnit.map
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  rcases hx with rfl | rfl
  · exact key 0
  · exact key 1

private theorem eq_zero_of_forall_mem_pow {A : Type*} [CommRing A] [IsNoetherianRing A]
  (J : Ideal A)
    (hJ : J ≤ Ideal.jacobson ⊥) (x : A) (hx : ∀ n : ℕ, x ∈ J ^ n) : x = 0 := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (I := J) (M := A)
    (hJ.trans_eq Ideal.jacobson_bot)
  have : x ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A A) := by
    rw [Submodule.mem_iInf]; intro i
    rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx i
  rw [h] at this
  exact (Submodule.mem_bot A).mp this

private theorem map_mem_pow_of_mem_pow {R A : Type*} [CommRing R] [CommRing A]
    (h : MvPowerSeries (Fin 2) R →+* A) (J' : Ideal A) (h0 : h (X 0) ∈ J') (h1 : h (X 1) ∈ J')
    (n : ℕ) (F : MvPowerSeries (Fin 2) R)
      (hF : F ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ^ n) :
    h F ∈ J' ^ n := by
  have hle : Ideal.map h (Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) ≤ J' := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have := Ideal.mem_map_of_mem h hF
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle n this

private theorem ringHom_apply_eq_of_eqOn_poly {R A : Type*} [CommRing R] [CommRing A]
  [IsNoetherianRing A]
    (h₁ h₂ : MvPowerSeries (Fin 2) R →+* A) (J' : Ideal A) (hJ' : J' ≤ Ideal.jacobson ⊥)
    (hpoly : ∀ p : MvPolynomial (Fin 2) R, h₁ (p : MvPowerSeries (Fin 2) R) = h₂
      (p : MvPowerSeries (Fin 2) R))
    (h₁0 : h₁ (X 0) ∈ J') (h₁1 : h₁ (X 1) ∈ J') (h₂0 : h₂ (X 0) ∈ J') (h₂1 : h₂ (X 1) ∈ J') :
    ∀ F : MvPowerSeries (Fin 2) R, h₁ F = h₂ F := by
  intro F
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_mem_pow J' hJ'
  intro n
  have e : h₁ F - h₂ F =
      h₁ (F - ((truncTotal n F : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R)) -
        h₂ (F - ((truncTotal n F : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R)) := by
    rw [map_sub, map_sub, hpoly]; ring
  rw [e]
  exact Ideal.sub_mem _
    (map_mem_pow_of_mem_pow h₁ J' h₁0 h₁1 n _ (sub_coe_truncTotal_mem_pow R n F))
    (map_mem_pow_of_mem_pow h₂ J' h₂0 h₂1 n _ (sub_coe_truncTotal_mem_pow R n F))

private theorem eqOn_poly_of_eqOn_C_X {R A : Type*} [CommRing R] [CommRing A]
    (h₁ h₂ : MvPowerSeries (Fin 2) R →+* A)
    (hC : ∀ r : R, h₁ (C r) = h₂ (C r)) (hX : ∀ i : Fin 2, h₁ (X i) = h₂ (X i)) :
    ∀ p : MvPolynomial (Fin 2) R, h₁ (p : MvPowerSeries (Fin 2) R) = h₂
      (p : MvPowerSeries (Fin 2) R) := by
  intro p
  have : h₁.comp (MvPolynomial.coeToMvPowerSeries.ringHom) = h₂.comp
    (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simpa using hC r
    · intro i; simpa using hX i
  exact congrArg (fun f => f p) this |>.trans rfl

private theorem constantCoeff_eq_zero_of_mem_span_X {R : Type*} [CommRing R]
  (P : MvPowerSeries (Fin 2) R)
    (hP : P ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1}) : constantCoeff P = 0 := by
  have hle : Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} ≤ RingHom.ker
    (constantCoeff : MvPowerSeries (Fin 2) R →+* R) := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hx with rfl | rfl <;> simp
  exact hle hP

private theorem exists_lift_mem_span_X {R : Type*} [CommRing R]
  (I : Ideal (MvPowerSeries (Fin 2) R))
    (s : MvPowerSeries (Fin 2) R ⧸ I)
    (hs : s ∈ Ideal.span {Ideal.Quotient.mk I (X 0), Ideal.Quotient.mk I (X 1)}) :
    ∃ P : MvPowerSeries (Fin 2) R, Ideal.Quotient.mk I P = s ∧
      P ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) R), X 1} := by
  rw [Ideal.mem_span_pair] at hs
  obtain ⟨a, b, rfl⟩ := hs
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨B, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨A * X 0 + B * X 1, by simp only [map_add, map_mul], ?_⟩
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

private theorem map_symm_le_of_map_le {A : Type*} [CommRing A] [IsNoetherianRing A] (θ : A ≃+* A)
  (J : Ideal A)
    (h : Ideal.map (θ : A →+* A) J ≤ J) : Ideal.map (θ.symm : A →+* A) J ≤ J := by

  let T : Ideal A → Ideal A := Ideal.map (θ.symm : A →+* A)
  have hTinv : ∀ I : Ideal A, Ideal.map (θ : A →+* A) (T I) = I := by
    intro I
    show Ideal.map (θ : A →+* A) (Ideal.map (θ.symm : A →+* A) I) = I
    rw [Ideal.map_map]
    have : (θ : A →+* A).comp (θ.symm : A →+* A) = RingHom.id A := by
      ext x; simp
    rw [this, Ideal.map_id]
  have hTinj : ∀ I I' : Ideal A, T I = T I' → I = I' := by
    intro I I' hh; rw [← hTinv I, ← hTinv I', hh]
  have hJT : J ≤ T J := by
    intro x hx
    have : θ (θ.symm x) ∈ J := by rw [θ.apply_symm_apply]; exact hx

    have hx' : θ.symm (θ x) ∈ T J := Ideal.mem_map_of_mem _ (h (Ideal.mem_map_of_mem _ hx))
    simpa using hx'
  have hmono : ∀ k : ℕ, T^[k] J ≤ T^[k + 1] J := by
    intro k
    induction k with
    | zero => simpa using hJT
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact Ideal.map_mono ih
  let f : ℕ →o Submodule A A := ⟨fun k => T^[k] J, monotone_nat_of_le_succ hmono⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A)) f
  have hNN : T^[N] J = T^[N + 1] J := hN (N + 1) (Nat.le_succ N)

  have hcancel : ∀ (k : ℕ) (I I' : Ideal A), T^[k] I = T^[k] I' → I = I' := by
    intro k
    induction k with
    | zero => intro I I' hh; simpa using hh
    | succ k ih =>
        intro I I' hh
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hh
        exact hTinj _ _ (ih _ _ hh)
  have : J = T J := by
    apply hcancel N
    rw [hNN, Function.iterate_succ_apply]
  exact le_of_eq this.symm


private theorem exists_of_mem_span_pair_sq {S : Type*} [CommRing S] (a b r : S)
    (hr : r ∈ (Ideal.span {a, b}) ^ 2) :
    ∃ z₁ ∈ Ideal.span {a, b}, ∃ z₂ ∈ Ideal.span {a, b}, r = a * z₁ + b * z₂ := by
  rw [pow_two, Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at hr
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
  rw [Ideal.mem_span_singleton_mul] at hr₁ hr₂
  obtain ⟨z₁, hz₁, rfl⟩ := hr₁
  obtain ⟨z₂, hz₂, rfl⟩ := hr₂
  refine ⟨z₁, ?_, z₂, ?_, rfl⟩
  · simpa [Ideal.span_insert] using hz₁
  · simpa [Ideal.span_insert] using hz₂

namespace MvPowerSeries

/-- Base change of a quotient automorphism of a two-variable power series
ring along a coefficient homomorphism, preserving the prescribed linear
part modulo the square of the ideal generated by the variables. -/

theorem exists_ringEquiv_quotient_span_comp_map_eq_of_ringEquiv_of_linearPart_of_span_eq
    (W₀ W : Type*) [CommRing W₀] [IsNoetherianRing W₀] [CommRing W] [IsNoetherianRing W]
    (ψ : W₀ →+* W) (g₀ : MvPowerSeries (Fin 2) W₀) (g : MvPowerSeries (Fin 2) W)
    (hg : Ideal.span {g} = Ideal.span {MvPowerSeries.map ψ g₀})
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) ≃+*
      (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}))
    (M₀ : Matrix (Fin 2) (Fin 2) W₀)

    (hθ₀C : ∀ w : W₀, θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (C w)) = Ideal.Quotient.mk
      (Ideal.span {g₀}) (C w))

    (hθ₀X : ∀ jj : Fin 2,
      θ₀ (Ideal.Quotient.mk (Ideal.span {g₀}) (X jj)) -
          Ideal.Quotient.mk (Ideal.span {g₀}) (∑ ii : Fin 2, C (M₀ ii jj) * X ii) ∈
        (Ideal.span {Ideal.Quotient.mk (Ideal.span {g₀}) (X 0 : MvPowerSeries (Fin 2) W₀),
          Ideal.Quotient.mk (Ideal.span {g₀}) (X 1)}) ^ 2) :
    let S₀ := MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}
    let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {g₀})
    let S := MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {g})
    ∃ θ : S ≃+* S,

      (∀ w : W, θ (mkS (C w)) = mkS (C w)) ∧

      (∀ s s' : MvPowerSeries (Fin 2) W₀, θ₀ (mkS₀ s) = mkS₀ s' →
        θ (mkS (MvPowerSeries.map ψ s)) = mkS (MvPowerSeries.map ψ s')) ∧

      (∀ jj : Fin 2,
        θ (mkS (X jj)) - mkS (∑ ii : Fin 2, C (ψ (M₀ ii jj)) * X ii) ∈
          (Ideal.span {mkS (X 0), mkS (X 1)}) ^ 2) := by
  intro S₀ mkS₀ S mkS
  classical
  haveI hN0 : IsNoetherianRing (MvPowerSeries (Fin 2) W₀) := inferInstance
  haveI hN1 : IsNoetherianRing (MvPowerSeries (Fin 2) W) := inferInstance
  haveI : IsNoetherianRing S₀ :=
    inferInstanceAs (IsNoetherianRing (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}))
  haveI : IsNoetherianRing S :=
    inferInstanceAs (IsNoetherianRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}))

  have hI₀ : ∀ x : MvPowerSeries (Fin 2) W₀, x ∈ Ideal.span {g₀} → MvPowerSeries.map ψ x ∈
    Ideal.span {g} := by
    intro x hx
    rw [Ideal.mem_span_singleton'] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hmkS₀ : ∀ x : MvPowerSeries (Fin 2) W₀, mkS₀ x = 0 ↔ x ∈ Ideal.span {g₀} := fun x =>
    Ideal.Quotient.eq_zero_iff_mem
  have hmkS : ∀ x : MvPowerSeries (Fin 2) W, mkS x = 0 ↔ x ∈ Ideal.span {g} := fun x =>
    Ideal.Quotient.eq_zero_iff_mem

  have hC₀ : ∀ w : W₀, (C w : MvPowerSeries (Fin 2) W₀) = algebraMap W₀ (MvPowerSeries (Fin 2) W₀)
    w := fun w => by simp [MvPowerSeries.algebraMap_apply]
  have hC₁ : ∀ w : W, (C w : MvPowerSeries (Fin 2) W) = algebraMap W (MvPowerSeries (Fin 2) W) w :=
    fun w => by simp [MvPowerSeries.algebraMap_apply]

  have hmkJ₀ : ∀ x : MvPowerSeries (Fin 2) W₀, x ∈ Ideal.span
    {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} → mkS₀ x ∈ Ideal.span {mkS₀ (X 0), mkS₀ (X 1)} := by
    intro x hx
    have := map_mem_pow_of_mem_pow mkS₀ (Ideal.span {mkS₀ (X 0), mkS₀ (X 1)})
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) 1 x (by simpa using hx)
    simpa using this
  have hmkJ : ∀ x : MvPowerSeries (Fin 2) W, x ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}
    → mkS x ∈ Ideal.span {mkS (X 0), mkS (X 1)} := by
    intro x hx
    have := map_mem_pow_of_mem_pow mkS (Ideal.span {mkS (X 0), mkS (X 1)})
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) 1 x (by simpa using hx)
    simpa using this
  have hmapX : ∀ i : Fin 2, MvPowerSeries.map ψ (X i : MvPowerSeries (Fin 2) W₀) = X i := fun i =>
    MvPowerSeries.map_X _ _
  have hmapJ : ∀ (n : ℕ) (x : MvPowerSeries (Fin 2) W₀), x ∈
    (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1}) ^ n → MvPowerSeries.map ψ x ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ n := by
    intro n x hx
    exact map_mem_pow_of_mem_pow (MvPowerSeries.map ψ)
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1})
        (by rw [hmapX]; exact Ideal.subset_span (by simp))
      (by rw [hmapX]; exact Ideal.subset_span (by simp)) n x hx

  have hP : ∀ jj : Fin 2, ∃ P : MvPowerSeries (Fin 2) W₀, mkS₀ P = θ₀ (mkS₀ (X jj)) ∧ P ∈
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ∧
      P - ∑ ii : Fin 2, C (M₀ ii jj) * X ii ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1})
        ^ 2 := by
    intro jj
    have hsq := exists_of_mem_span_pair_sq (mkS₀ (X 0)) (mkS₀ (X 1)) _ (hθ₀X jj)
    obtain ⟨z₁, hz₁, z₂, hz₂, hr⟩ := hsq
    obtain ⟨Z₁, hZ₁, hZ₁J⟩ := exists_lift_mem_span_X (Ideal.span {g₀}) z₁ hz₁
    obtain ⟨Z₂, hZ₂, hZ₂J⟩ := exists_lift_mem_span_X (Ideal.span {g₀}) z₂ hz₂
    refine ⟨(∑ ii : Fin 2, C (M₀ ii jj) * X ii) + (X 0 * Z₁ + X 1 * Z₂), ?_, ?_, ?_⟩
    · have e : θ₀ (mkS₀ (X jj)) = mkS₀ (∑ ii : Fin 2, C (M₀ ii jj) * X ii) +
      (mkS₀ (X 0) * z₁ + mkS₀ (X 1) * z₂) := by
        rw [← hr]; abel
      rw [e, map_add, map_add, map_mul, map_mul]
      show mkS₀ _ + (mkS₀ (X 0) * mkS₀ Z₁ + mkS₀ (X 1) * mkS₀ Z₂) = _
      rw [hZ₁, hZ₂]
    · have hsum : (∑ ii : Fin 2, C (M₀ ii jj) * X ii) ∈
          Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} := by
        apply Ideal.sum_mem
        intro ii _
        apply Ideal.mul_mem_left
        apply Ideal.subset_span
        fin_cases ii <;> simp
      exact Ideal.add_mem _ hsum (Ideal.add_mem _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
    · have e : (∑ ii : Fin 2, C (M₀ ii jj) * X ii) + (X 0 * Z₁ + X 1 * Z₂)
          - ∑ ii : Fin 2, C (M₀ ii jj) * X ii = X 0 * Z₁ + X 1 * Z₂ := by abel
      rw [e, pow_two]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hZ₁J)
        (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hZ₂J)
  choose P hPmk hPJ hPlin using hP

  have haP : MvPowerSeries.HasSubst P :=
    ⟨fun s => by rw [constantCoeff_eq_zero_of_mem_span_X _ (hPJ s)]; exact IsNilpotent.zero, fun d
      => Set.toFinite _⟩
  let Φ₀ : MvPowerSeries (Fin 2) W₀ →ₐ[W₀] MvPowerSeries (Fin 2) W₀ := MvPowerSeries.substAlgHom haP
  have hΦ₀X : ∀ i : Fin 2, Φ₀ (X i) = P i := fun i => MvPowerSeries.substAlgHom_X haP i
  have hΦ₀C : ∀ w : W₀, Φ₀ (C w) = C w := fun w => by rw [hC₀]; exact Φ₀.commutes w

  have hA : ∀ F : MvPowerSeries (Fin 2) W₀, θ₀ (mkS₀ F) = mkS₀ (Φ₀ F) := by
    have := ringHom_apply_eq_of_eqOn_poly ((θ₀ : S₀ →+* S₀).comp mkS₀)
      (mkS₀.comp (Φ₀ : MvPowerSeries (Fin 2) W₀ →+* MvPowerSeries (Fin 2) W₀))
      (Ideal.span {mkS₀ (X 0), mkS₀ (X 1)}) (span_mk_X_le_jacobson W₀ _)
      (eqOn_poly_of_eqOn_C_X _ _ (fun r => by simp [hΦ₀C]; exact hθ₀C r)
        (fun i => by simp [hΦ₀X, hPmk]))
      (by simpa [hPmk] using hmkJ₀ _ (hPJ 0)) (by simpa [hPmk] using hmkJ₀ _ (hPJ 1))
      (by simpa [hΦ₀X] using hmkJ₀ _ (hPJ 0)) (by simpa [hΦ₀X] using hmkJ₀ _ (hPJ 1))
    intro F; exact this F

  have hθ₀J : Ideal.map (θ₀ : S₀ →+* S₀) (Ideal.span {mkS₀ (X 0), mkS₀ (X 1)}) ≤ Ideal.span
    {mkS₀ (X 0), mkS₀ (X 1)} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show θ₀ (mkS₀ (X 0)) ∈ _; rw [← hPmk]; exact hmkJ₀ _ (hPJ 0)
    · show θ₀ (mkS₀ (X 1)) ∈ _; rw [← hPmk]; exact hmkJ₀ _ (hPJ 1)
  have hθ₀J' := map_symm_le_of_map_le θ₀ _ hθ₀J
  have hQ : ∀ jj : Fin 2, ∃ Q : MvPowerSeries (Fin 2) W₀, mkS₀ Q = θ₀.symm (mkS₀ (X jj)) ∧ Q ∈
    Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} := by
    intro jj
    have hmem : θ₀.symm (mkS₀ (X jj)) ∈ Ideal.span {mkS₀ (X 0), mkS₀ (X 1)} := by
      apply hθ₀J'
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by fin_cases jj <;> simp))
    exact exists_lift_mem_span_X (Ideal.span {g₀}) _ hmem
  choose Q hQmk hQJ using hQ
  have haQ : MvPowerSeries.HasSubst Q :=
    ⟨fun s => by rw [constantCoeff_eq_zero_of_mem_span_X _ (hQJ s)]; exact IsNilpotent.zero, fun d
      => Set.toFinite _⟩
  let Ψ₀ : MvPowerSeries (Fin 2) W₀ →ₐ[W₀] MvPowerSeries (Fin 2) W₀ := MvPowerSeries.substAlgHom haQ
  have hΨ₀X : ∀ i : Fin 2, Ψ₀ (X i) = Q i := fun i => MvPowerSeries.substAlgHom_X haQ i
  have hΨ₀C : ∀ w : W₀, Ψ₀ (C w) = C w := fun w => by rw [hC₀]; exact Ψ₀.commutes w
  have hθ₀C' : ∀ w : W₀, θ₀.symm (mkS₀ (C w)) = mkS₀ (C w) := by
    intro w
    have := congrArg θ₀.symm (hθ₀C w)
    rw [θ₀.symm_apply_apply] at this
    exact this.symm
  have hA' : ∀ F : MvPowerSeries (Fin 2) W₀, θ₀.symm (mkS₀ F) = mkS₀ (Ψ₀ F) := by
    have := ringHom_apply_eq_of_eqOn_poly ((θ₀.symm : S₀ →+* S₀).comp mkS₀)
      (mkS₀.comp (Ψ₀ : MvPowerSeries (Fin 2) W₀ →+* MvPowerSeries (Fin 2) W₀))
      (Ideal.span {mkS₀ (X 0), mkS₀ (X 1)}) (span_mk_X_le_jacobson W₀ _)
      (eqOn_poly_of_eqOn_C_X _ _ (fun r => by simp [hΨ₀C]; exact hθ₀C' r)
        (fun i => by simp [hΨ₀X, hQmk]))
      (by simpa [hQmk] using hmkJ₀ _ (hQJ 0)) (by simpa [hQmk] using hmkJ₀ _ (hQJ 1))
      (by simpa [hΨ₀X] using hmkJ₀ _ (hQJ 0)) (by simpa [hΨ₀X] using hmkJ₀ _ (hQJ 1))
    intro F; exact this F

  have haPW : MvPowerSeries.HasSubst (fun i => MvPowerSeries.map ψ (P i)) := haP.map ψ
  have haQW : MvPowerSeries.HasSubst (fun i => MvPowerSeries.map ψ (Q i)) := haQ.map ψ
  let Φ : MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries (Fin 2) W := MvPowerSeries.substAlgHom haPW
  let Ψ : MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries (Fin 2) W := MvPowerSeries.substAlgHom haQW
  have hΦX : ∀ i : Fin 2, Φ (X i) = MvPowerSeries.map ψ (P i) := fun i =>
    MvPowerSeries.substAlgHom_X haPW i
  have hΨX : ∀ i : Fin 2, Ψ (X i) = MvPowerSeries.map ψ (Q i) := fun i =>
    MvPowerSeries.substAlgHom_X haQW i
  have hΦC : ∀ w : W, Φ (C w) = C w := fun w => by rw [hC₁]; exact Φ.commutes w
  have hΨC : ∀ w : W, Ψ (C w) = C w := fun w => by rw [hC₁]; exact Ψ.commutes w
  have hΦmap : ∀ F : MvPowerSeries (Fin 2) W₀, Φ (MvPowerSeries.map ψ F) = MvPowerSeries.map ψ
    (Φ₀ F) := by
    intro F
    show MvPowerSeries.substAlgHom haPW (MvPowerSeries.map ψ F) = MvPowerSeries.map ψ
      (MvPowerSeries.substAlgHom haP F)
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply, MvPowerSeries.map_subst
      haP]
  have hΨmap : ∀ F : MvPowerSeries (Fin 2) W₀, Ψ (MvPowerSeries.map ψ F) = MvPowerSeries.map ψ
    (Ψ₀ F) := by
    intro F
    show MvPowerSeries.substAlgHom haQW (MvPowerSeries.map ψ F) = MvPowerSeries.map ψ
      (MvPowerSeries.substAlgHom haQ F)
    rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply, MvPowerSeries.map_subst
      haQ]

  have hg' : g ∈ Ideal.span {MvPowerSeries.map ψ g₀} := hg ▸ Ideal.mem_span_singleton_self g
  have hΦg : ∀ (Θ : MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries (Fin 2) W)
    (Θ₀ : MvPowerSeries (Fin 2) W₀ →ₐ[W₀] MvPowerSeries (Fin 2) W₀),
      (∀ F, Θ (MvPowerSeries.map ψ F) = MvPowerSeries.map ψ (Θ₀ F)) → Θ₀ g₀ ∈ Ideal.span {g₀} →
      Ideal.span {g} ≤ Ideal.comap (Θ : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W)
        (Ideal.span {g}) := by
    intro Θ Θ₀ hΘ hΘ₀
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    rw [Ideal.mem_span_singleton'] at hg'
    obtain ⟨c, hc⟩ := hg'
    show Θ g ∈ Ideal.span {g}
    have e : Θ g = Θ c * MvPowerSeries.map ψ (Θ₀ g₀) := by rw [← hc, map_mul, hΘ]
    rw [e]
    exact Ideal.mul_mem_left _ _ (hI₀ _ hΘ₀)
  have hΦ₀g : Φ₀ g₀ ∈ Ideal.span {g₀} := by
    rw [← hmkS₀, ← hA, (hmkS₀ g₀).mpr (Ideal.mem_span_singleton_self _), map_zero]
  have hΨ₀g : Ψ₀ g₀ ∈ Ideal.span {g₀} := by
    rw [← hmkS₀, ← hA', (hmkS₀ g₀).mpr (Ideal.mem_span_singleton_self _), map_zero]
  let θ' : S →+* S := Ideal.quotientMap (Ideal.span {g})
    (Φ : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W) (hΦg Φ Φ₀ hΦmap hΦ₀g)
  let θ'' : S →+* S := Ideal.quotientMap (Ideal.span {g})
    (Ψ : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W) (hΦg Ψ Ψ₀ hΨmap hΨ₀g)
  have hθ' : ∀ F : MvPowerSeries (Fin 2) W, θ' (mkS F) = mkS (Φ F) := fun F => Ideal.quotientMap_mk
  have hθ'' : ∀ F : MvPowerSeries (Fin 2) W, θ'' (mkS F) = mkS (Ψ F) := fun F =>
    Ideal.quotientMap_mk

  have hmkmap : ∀ F F' : MvPowerSeries (Fin 2) W₀, mkS₀ F = mkS₀ F' → mkS (MvPowerSeries.map ψ F) =
    mkS (MvPowerSeries.map ψ F') := by
    intro F F' h
    rw [Ideal.Quotient.eq] at h ⊢
    rw [← map_sub]
    exact hI₀ _ h

  have hθ'J : ∀ i : Fin 2, θ' (mkS (X i)) ∈ Ideal.span {mkS (X 0), mkS (X 1)} := by
    intro i; rw [hθ', hΦX]; exact hmkJ _ (by simpa using hmapJ 1 _ (by simpa using hPJ i))
  have hθ''J : ∀ i : Fin 2, θ'' (mkS (X i)) ∈ Ideal.span {mkS (X 0), mkS (X 1)} := by
    intro i; rw [hθ'', hΨX]; exact hmkJ _ (by simpa using hmapJ 1 _ (by simpa using hQJ i))
  have hθ'Jle : Ideal.map θ' (Ideal.span {mkS (X 0), mkS (X 1)}) ≤ Ideal.span
    {mkS (X 0), mkS (X 1)} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hθ'J 0
    · exact hθ'J 1
  have hθ''Jle : Ideal.map θ'' (Ideal.span {mkS (X 0), mkS (X 1)}) ≤ Ideal.span
    {mkS (X 0), mkS (X 1)} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hθ''J 0
    · exact hθ''J 1
  have hinv1 : ∀ F : MvPowerSeries (Fin 2) W, θ' (θ'' (mkS F)) = mkS F := by
    have := ringHom_apply_eq_of_eqOn_poly ((θ'.comp θ'').comp mkS) mkS
      (Ideal.span {mkS (X 0), mkS (X 1)}) (span_mk_X_le_jacobson W _)
      (eqOn_poly_of_eqOn_C_X _ _
        (fun r => by simp only [RingHom.comp_apply]; rw [hθ'', hΨC, hθ', hΦC])
        (fun i => by
          simp only [RingHom.comp_apply]
          rw [hθ'', hΨX, hθ', hΦmap]
          have e : mkS₀ (Φ₀ (Q i)) = mkS₀ (X i) := by rw [← hA, hQmk, θ₀.apply_symm_apply]
          rw [hmkmap _ _ e, hmapX]))
      (by simp only [RingHom.comp_apply]; exact hθ'Jle (Ideal.mem_map_of_mem _ (hθ''J 0)))
      (by simp only [RingHom.comp_apply]; exact hθ'Jle (Ideal.mem_map_of_mem _ (hθ''J 1)))
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    intro F; exact this F
  have hinv2 : ∀ F : MvPowerSeries (Fin 2) W, θ'' (θ' (mkS F)) = mkS F := by
    have := ringHom_apply_eq_of_eqOn_poly ((θ''.comp θ').comp mkS) mkS
      (Ideal.span {mkS (X 0), mkS (X 1)}) (span_mk_X_le_jacobson W _)
      (eqOn_poly_of_eqOn_C_X _ _
        (fun r => by simp only [RingHom.comp_apply]; rw [hθ', hΦC, hθ'', hΨC])
        (fun i => by
          simp only [RingHom.comp_apply]
          rw [hθ', hΦX, hθ'', hΨmap]
          have e : mkS₀ (Ψ₀ (P i)) = mkS₀ (X i) := by rw [← hA', hPmk, θ₀.symm_apply_apply]
          rw [hmkmap _ _ e, hmapX]))
      (by simp only [RingHom.comp_apply]; exact hθ''Jle (Ideal.mem_map_of_mem _ (hθ'J 0)))
      (by simp only [RingHom.comp_apply]; exact hθ''Jle (Ideal.mem_map_of_mem _ (hθ'J 1)))
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    intro F; exact this F
  let θ : S ≃+* S :=
    { toFun := θ'
      invFun := θ''
      left_inv := fun s => by obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective s; exact hinv2 F
      right_inv := fun s => by obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective s; exact hinv1 F
      map_mul' := θ'.map_mul
      map_add' := θ'.map_add }
  have hθ : ∀ s : S, θ s = θ' s := fun s => rfl

  refine ⟨θ, ?_, ?_, ?_⟩
  · intro w; rw [hθ, hθ', hΦC]
  · intro s s' hss'
    rw [hθ, hθ', hΦmap]
    apply hmkmap
    rw [← hA, hss']
  · intro jj
    rw [hθ, hθ', hΦX]
    have e : MvPowerSeries.map ψ (∑ ii : Fin 2, C (M₀ ii jj) * X ii)
        = ∑ ii : Fin 2, C (ψ (M₀ ii jj)) * X ii := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun ii _ => ?_)
      rw [map_mul, MvPowerSeries.map_C, hmapX]
    rw [← e, ← map_sub, ← map_sub]
    have h2 := hmapJ 2 _ (hPlin jj)
    exact map_mem_pow_of_mem_pow mkS (Ideal.span {mkS (X 0), mkS (X 1)})
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) 2 _ h2

end MvPowerSeries
