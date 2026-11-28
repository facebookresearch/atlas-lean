/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomialReps
public import MathlibExt.NumberTheory.ModularForms.Gamma0Index
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Right cosets of `Γ₀(N)` and the representatives `C_N`

For a positive integer `N` let `C_N` (`WLight.modularPolynomialReps N`) be the set of integer
matrices `!![a, b; 0, d]` with `a > 0`, `0 ≤ b < d`, `a d = N` and `gcd(a, b, d) = 1`.

* The right cosets `Γ₀(N) γ` of `Γ₀(N)` in `SL₂(ℤ)` are in bijection with `C_N`: the coset of
  `γ` goes to the unique `M ∈ C_N` with `!![N, 0; 0, 1] γ ∈ SL₂(ℤ) M`
  (`WLight.gamma0RightCosetsEquiv`, `WLight.gamma0RightCosetsEquiv_mk_eq_iff`).
* Hence `[SL₂(ℤ) : Γ₀(N)] = #C_N` (`WLight.index_gamma0_eq_card_modularPolynomialReps`), and
  with `ModularCurve.Gamma0_index` the number of elements of `C_N` is the Dedekind psi value
  `ψ(N) = N ∏_{p ∣ N} (1 + 1/p)` (`WLight.card_modularPolynomialReps`).

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Theorem 19.14 (p. 6) and its proof (pp. 6–7), and Definition 19.15 (p. 7).
-/

@[expose] public section

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup

namespace WLight

private theorem coe_mul_coe_inv (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) * ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
  congrArg Subtype.val (mul_inv_cancel g)

private theorem coe_inv_mul_coe (g : SL(2, ℤ)) :
    ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
  congrArg Subtype.val (inv_mul_cancel g)

private theorem diag_mul_apply (N : ℕ) (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    !![(N : ℤ), 0; 0, 1] * γ = !![N * γ 0 0, N * γ 0 1; γ 1 0, γ 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_diag_mul (N : ℕ) (γ : SL(2, ℤ)) :
    (!![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = N := by
  rw [Matrix.det_mul, γ.det_coe, mul_one, Matrix.det_fin_two_of]
  ring

private theorem prim_diag_mul (N : ℕ) (γ : SL(2, ℤ)) (n : ℤ)
    (h : ∀ i j, n ∣ (!![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j) :
    IsUnit n := by
  have h10 := h 1 0
  have h11 := h 1 1
  rw [diag_mul_apply] at h10 h11
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at h10 h11
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  apply isUnit_of_dvd_one
  rw [← hdet]
  exact dvd_sub (dvd_mul_of_dvd_right h11 _) (dvd_mul_of_dvd_right h10 _)

private theorem exists_rep (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    ∃ M : modularPolynomialReps N, ∃ δ : SL(2, ℤ),
      !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ : Matrix (Fin 2) (Fin 2) ℤ) * (M : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨δ, M, hM, h⟩ := exists_eq_mul_of_det _ (det_diag_mul N γ)
    (Nat.pos_of_ne_zero (NeZero.ne N)) (prim_diag_mul N γ)
  exact ⟨⟨M, hM⟩, δ, h⟩

private noncomputable def rep (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) : modularPolynomialReps N :=
  (exists_rep N γ).choose

private theorem rep_spec (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * (rep N γ : Matrix (Fin 2) (Fin 2) ℤ) :=
  (exists_rep N γ).choose_spec

private theorem eq_of_mul_eq_mul {N : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : M ∈ modularPolynomialReps N) (hM' : M' ∈ modularPolynomialReps N) (δ δ' : SL(2, ℤ))
    (h : (δ : Matrix (Fin 2) (Fin 2) ℤ) * M = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * M') :
    M = M' := by
  refine (modularPolynomialReps_eq_of_mul_eq hM hM' (δ'⁻¹ * δ) ?_).1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
    coe_inv_mul_coe, Matrix.one_mul]

private theorem rep_eq_of_mul_eq (N : ℕ) [NeZero N] (γ δ : SL(2, ℤ))
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ modularPolynomialReps N)
    (h : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * M) :
    (rep N γ : Matrix (Fin 2) (Fin 2) ℤ) = M := by
  obtain ⟨δ', h'⟩ := rep_spec N γ
  exact eq_of_mul_eq_mul (rep N γ).2 hM δ' δ (h'.symm.trans h)

private theorem diag_mul_of_mem_gamma0 {N : ℕ} {g : SL(2, ℤ)} (hg : g ∈ Gamma0 N) :
    ∃ g' : SL(2, ℤ), !![(N : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) =
      (g' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  refine ⟨⟨!![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0, N * (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
    c, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc
  · rw [diag_mul_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> ring

private theorem rep_eq_of_rel (N : ℕ) [NeZero N] (x y : SL(2, ℤ))
    (h : y * x⁻¹ ∈ Gamma0 N) : rep N x = rep N y := by
  obtain ⟨g', hg'⟩ := diag_mul_of_mem_gamma0 h
  obtain ⟨δ, hδ⟩ := rep_spec N x
  apply Subtype.ext
  symm
  apply rep_eq_of_mul_eq N y (g' * δ) (rep N x).2
  have hy : (y : Matrix (Fin 2) (Fin 2) ℤ) =
      ((y * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (x : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  rw [hy, ← Matrix.mul_assoc, hg', Matrix.mul_assoc, hδ, ← Matrix.mul_assoc,
    Matrix.SpecialLinearGroup.coe_mul]

private theorem mem_gamma0_of_diag_mul {N : ℕ} {η ε : SL(2, ℤ)}
    (h : !![(N : ℤ), 0; 0, 1] * (η : Matrix (Fin 2) (Fin 2) ℤ) =
      (ε : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1]) : η ∈ Gamma0 N := by
  have e : (η : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (ε : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * N := by
    have h' := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨(ε : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by rw [e]; ring⟩

private theorem rel_of_rep_eq (N : ℕ) [NeZero N] (x y : SL(2, ℤ)) (h : rep N x = rep N y) :
    y * x⁻¹ ∈ Gamma0 N := by
  obtain ⟨δx, hx⟩ := rep_spec N x
  obtain ⟨δy, hy⟩ := rep_spec N y
  rw [h] at hx
  apply mem_gamma0_of_diag_mul (ε := δy * δx⁻¹)
  have hR : (rep N y : Matrix (Fin 2) (Fin 2) ℤ) = ((δx⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      !![(N : ℤ), 0; 0, 1] * (x : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.mul_assoc, hx, ← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, hy, hR,
    Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_assoc]
  rw [coe_mul_coe_inv, Matrix.mul_one]

private theorem exists_isCoprime_mul_sub {a b d : ℤ} (hd : d ≠ 0)
    (hg : Int.gcd (Int.gcd a b) d = 1) : ∃ s : ℤ, IsCoprime d (a * s - b) := by
  classical
  set S := d.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ b) with hS
  refine ⟨∏ p ∈ S, (p : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : (p : ℤ) ∣ d := (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_left _ _)
  have hp2 : (p : ℤ) ∣ a * ∏ p ∈ S, (p : ℤ) - b :=
    (Int.natCast_dvd_natCast.mpr hpd).trans (Int.gcd_dvd_right _ _)
  by_cases hpb : (p : ℤ) ∣ b
  · have hpas : (p : ℤ) ∣ a * ∏ p ∈ S, (p : ℤ) := by
      have := dvd_add hp2 hpb
      rwa [sub_add_cancel] at this
    rcases hpZ.dvd_or_dvd hpas with hpa | hps
    · have h1 : (p : ℤ) ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd hpa hpb
      have h2 : (p : ℤ) ∣ (Int.gcd (Int.gcd a b) d : ℤ) := Int.dvd_coe_gcd h1 hp1
      rw [hg, Nat.cast_one] at h2
      exact hpZ.not_dvd_one h2
    · obtain ⟨q, hq, hpq⟩ := Prime.exists_mem_finset_dvd hpZ hps
      rw [hS, Finset.mem_filter] at hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq.1
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (Int.natCast_dvd_natCast.mp hpq)
      subst hpq'
      exact hq.2 hpb
  · have hmem : p ∈ S := by
      rw [hS, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hp, Int.natCast_dvd.mp hp1, Int.natAbs_ne_zero.mpr hd⟩, hpb⟩
    have hps : (p : ℤ) ∣ ∏ p ∈ S, (p : ℤ) := Finset.dvd_prod_of_mem _ hmem
    apply hpb
    have := dvd_sub (dvd_mul_of_dvd_right hps a) hp2
    rwa [sub_sub_cancel] at this

private theorem rep_surjective (N : ℕ) [NeZero N] : Function.Surjective (rep N) := by
  rintro ⟨M, hM⟩
  have hM' := hM
  rw [mem_modularPolynomialReps] at hM'
  obtain ⟨h10, h00, h01, h0111, hN, hg⟩ := hM'
  have hd : M 1 1 ≠ 0 := by omega
  obtain ⟨s, u, v, huv⟩ := exists_isCoprime_mul_sub hd hg
  let γ : SL(2, ℤ) := ⟨!![1, s; -v * M 0 0, -v * M 0 1 + u * M 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  let ε : SL(2, ℤ) := ⟨!![M 1 1, M 0 0 * s - M 0 1; -v, u], by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  refine ⟨γ, Subtype.ext (rep_eq_of_mul_eq N γ ε hM ?_)⟩
  rw [diag_mul_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [γ, ε, Matrix.mul_apply, Fin.sum_univ_two, h10]
    linear_combination -hN
  · simp [γ, ε, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -s * hN
  · simp [γ, ε, Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [γ, ε, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Right cosets of `Γ₀(N)` and `C_N`.** For `N > 0`, the right cosets `Γ₀(N) γ` of `Γ₀(N)`
in `SL₂(ℤ)` are in bijection with `C_N`: the coset of `γ` is sent to the unique `M ∈ C_N` such
that `!![N, 0; 0, 1] γ = δ M` for some `δ ∈ SL₂(ℤ)`
(`WLight.gamma0RightCosetsEquiv_mk_eq_iff`).

So a set `{γ₁, …, γₙ}` of right coset representatives of `Γ₀(N)` gives the matrices
`!![N, 0; 0, 1] γᵢ ∈ SL₂(ℤ) Mᵢ` with `{M₁, …, Mₙ} = C_N`; in particular the functions
`j(N γᵢ τ)` are the functions `j(M τ)`, `M ∈ C_N`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Definition 19.15, p. 7: "The modular polynomial ΦN is the minimal polynomial of jN
over C(j)", written as `ΦN(Y) = ∏ᵢ (Y − jN(γᵢ τ))` "where {γ1, . . . γn} is a set of right coset
representatives for Γ0(N)"; with `jN(τ) = j(Nτ)` (Theorem 19.13, p. 6), and `N` viewed as the
matrix `!![N, 0; 0, 1]` in the proof of Theorem 19.14, p. 7. -/
@[no_expose] noncomputable def gamma0RightCosetsEquiv (N : ℕ) [NeZero N] :
    Quotient (QuotientGroup.rightRel (Gamma0 N)) ≃ modularPolynomialReps N :=
  Equiv.ofBijective
    (Quotient.lift (rep N) fun x y h => rep_eq_of_rel N x y (QuotientGroup.rightRel_apply.mp h))
    ⟨fun p q => Quotient.inductionOn₂ p q fun x y hxy =>
        Quotient.sound (QuotientGroup.rightRel_apply.mpr (rel_of_rep_eq N x y hxy)),
      fun M => by
        obtain ⟨γ, hγ⟩ := rep_surjective N M
        exact ⟨Quotient.mk _ γ, hγ⟩⟩

/-- **Characterization of `WLight.gamma0RightCosetsEquiv`.** For `N > 0`, `γ ∈ SL₂(ℤ)` and
`M ∈ C_N`, the coset `Γ₀(N) γ` is sent to `M` if and only if `!![N, 0; 0, 1] γ = δ M` for some
`δ ∈ SL₂(ℤ)`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.14, pp. 6–7 (the matrix `N = !![N, 0; 0, 1]` and the products
`N γᵢ`), and Definition 19.15, p. 7. -/
theorem gamma0RightCosetsEquiv_mk_eq_iff (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (M : modularPolynomialReps N) :
    gamma0RightCosetsEquiv N (Quotient.mk _ γ) = M ↔
      ∃ δ : SL(2, ℤ), !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (δ : Matrix (Fin 2) (Fin 2) ℤ) * (M : Matrix (Fin 2) (Fin 2) ℤ) := by
  change rep N γ = M ↔ _
  constructor
  · rintro rfl
    exact rep_spec N γ
  · rintro ⟨δ, h⟩
    exact Subtype.ext (rep_eq_of_mul_eq N γ δ M.2 h)

/-- **`N γ` lies in the `SL₂(ℤ)`-orbit of its representative.** For `N > 0` and `γ ∈ SL₂(ℤ)`,
`!![N, 0; 0, 1] γ = δ M` for some `δ ∈ SL₂(ℤ)`, where `M ∈ C_N` is the image of the right coset
`Γ₀(N) γ` under `WLight.gamma0RightCosetsEquiv`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, proof of Theorem 19.14, pp. 6–7, and Definition 19.15, p. 7. -/
theorem exists_mul_eq_gamma0RightCosetsEquiv (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) *
        (gamma0RightCosetsEquiv N (Quotient.mk _ γ) : Matrix (Fin 2) (Fin 2) ℤ) :=
  (gamma0RightCosetsEquiv_mk_eq_iff N γ _).mp rfl

/-- **`[SL₂(ℤ) : Γ₀(N)] = #C_N`.** For `N > 0`, the index of `Γ₀(N)` in `SL₂(ℤ)` equals the
number of elements of `C_N`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Theorem 19.14, p. 6: "an extension of C(j) of degree n := [Γ(1) : Γ0(N)]", and
Definition 19.15, p. 7, where `ΦN` is the product over the `n` right coset representatives. -/
theorem index_gamma0_eq_card_modularPolynomialReps (N : ℕ) [NeZero N] :
    (Gamma0 N).index = (modularPolynomialReps N).card := by
  rw [Subgroup.index_eq_card,
    ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Gamma0 N)),
    Nat.card_congr (gamma0RightCosetsEquiv N), Nat.card_eq_finsetCard]

/-- **`#C_N = ψ(N)`.** For `N > 0`, the number of elements of `C_N` is the Dedekind psi value
`ψ(N) = N ∏_{p ∣ N} (1 + 1/p)` (`ArithmeticFunction.dedekindPsi`): it is the index of `Γ₀(N)`
(`WLight.index_gamma0_eq_card_modularPolynomialReps`), which is `ψ(N)` by
`ModularCurve.Gamma0_index`.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT, Fall 2025,
Lecture 19, Theorem 19.14, p. 6, for the degree `n := [Γ(1) : Γ0(N)]`; the closed form `ψ(N)` is
not stated in that lecture. -/
theorem card_modularPolynomialReps (N : ℕ) [NeZero N] :
    (modularPolynomialReps N).card = ArithmeticFunction.dedekindPsi N := by
  rw [← index_gamma0_eq_card_modularPolynomialReps, ModularCurve.Gamma0_index]

end WLight
