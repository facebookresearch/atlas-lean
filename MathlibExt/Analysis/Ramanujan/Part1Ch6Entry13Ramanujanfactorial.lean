/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial
open Asymptotics Filter Finset Complex Topology

noncomputable section

private noncomputable def signW (k : ℕ+) : ℝ := (-1 : ℝ) ^ ((k : ℕ) + 1)

private noncomputable def dblL (t : ℝ) (c : ℕ+ × ℕ+) : ℝ :=
  signW c.1 * t ^ ((c.1 : ℕ) * (c.2 : ℕ))

private lemma dblL_summable {t : ℝ} (ht : ‖t‖ < 1) : Summable (dblL t) := by
  apply Summable.of_norm
  have hU := (summable_prod_mul_pow (𝕜 := ℝ) 0 ht).norm
  refine hU.congr (fun c => ?_)
  simp only [dblL, signW]
  have h1 : ‖(((c.2 : ℕ+) : ℕ) : ℝ) ^ (0:ℕ)‖ = 1 := by simp
  have hs : ‖(-1 : ℝ) ^ ((c.1 : ℕ) + 1)‖ = 1 := by simp
  rw [norm_mul, norm_mul, h1, hs, one_mul]

private lemma tsum_pnat_pow (u : ℝ) (hu : ‖u‖ < 1) :
    ∑' m : ℕ+, u ^ ((m : ℕ)) = u / (1 - u) := by
  have hgeo := tsum_geometric_of_norm_lt_one (K := ℝ) (ξ := u) hu
  have h2 : ∑' m : ℕ+, u ^ ((m : ℕ)) = ∑' n : ℕ, u ^ (n + 1) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n => u ^ n)]
  rw [h2]
  simp only [pow_succ']
  rw [tsum_mul_left, hgeo, div_eq_mul_inv]

private lemma inner_eq {t : ℝ} (ht : ‖t‖ < 1) (k : ℕ+) :
    ∑' m : ℕ+, dblL t (k, m) = signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))) := by
  have hk : (k:ℕ) ≠ 0 := ne_of_gt k.2
  have htk : ‖t ^ (k:ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht hk
  simp only [dblL]
  have hexp : ∀ m : ℕ+, t ^ ((k:ℕ) * (m:ℕ)) = (t ^ (k:ℕ)) ^ ((m:ℕ)) := by
    intro m; rw [pow_mul]
  simp only [hexp]
  rw [tsum_mul_left]
  congr 1
  exact tsum_pnat_pow _ htk

private lemma finite_left (N : ℕ) (t : ℝ) :
    ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2))
      = (∑ d ∈ N.divisors, (-1:ℝ)^(d+1)) * t^N := by
  have h1 : ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2))
      = ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^N) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hmem := Nat.mem_divisorsAntidiagonal.mp hx
    rw [hmem.1]
  rw [h1, ← Finset.sum_mul]
  congr 1
  have h2 := Nat.sum_divisorsAntidiagonal (M := ℝ) (f := fun a b => (-1:ℝ)^(a+1)) (n := N)
  simpa using h2

private lemma left_tsum_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' c : ℕ+ × ℕ+, dblL t c
      = ∑' N : ℕ+, (∑ d ∈ (N:ℕ).divisors, (-1:ℝ)^(d+1)) * t^((N:ℕ)) := by
  have hsum : Summable (dblL t) := dblL_summable ht
  have hsig : Summable (fun c : (N : ℕ+) × ↥((N:ℕ).divisorsAntidiagonal) ↦
      dblL t (sigmaAntidiagonalEquivProd c)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hsum
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma hsig]
  refine tsum_congr fun N => ?_
  have hgx : ∀ x : ↥((N:ℕ).divisorsAntidiagonal),
      dblL t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
        = ((-1:ℝ)^(x.1.1+1) * t^(x.1.1*x.1.2)) := by
    intro x
    simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, dblL, signW,
      Equiv.coe_fn_mk, PNat.mk_coe]
  rw [tsum_fintype]
  have hstep : ∑ x : ↥((N:ℕ).divisorsAntidiagonal),
        dblL t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
      = ∑ x ∈ (N:ℕ).divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2)) := by
    rw [← Finset.sum_attach ((N:ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => (-1:ℝ)^(p.1+1) * t^(p.1*p.2))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hgx]
  rw [hstep]
  exact finite_left (N:ℕ) t

private lemma left_single_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ)))
      = ∑' N : ℕ+, (∑ d ∈ (N:ℕ).divisors, (-1:ℝ)^(d+1)) * t^((N:ℕ)) := by
  have hsum := dblL_summable ht
  have e1 : (∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))))
      = ∑' k : ℕ+, ∑' m : ℕ+, dblL t (k, m) := by
    refine tsum_congr fun k => ?_
    rw [inner_eq ht k]
  rw [e1, ← hsum.tsum_prod]
  exact left_tsum_eq ht

private noncomputable def dblR (t : ℝ) (c : ℕ+ × ℕ+) : ℝ :=
  if (c.2:ℕ) % 2 = (c.1:ℕ) % 2 ∧ (c.1:ℕ) ≤ (c.2:ℕ) then
    if (c.1:ℕ) = (c.2:ℕ) then signW c.1 * t ^ ((c.1:ℕ) * (c.2:ℕ))
    else 2 * signW c.1 * t ^ ((c.1:ℕ) * (c.2:ℕ))
  else 0
private noncomputable def singleR (t : ℝ) (k : ℕ+) : ℝ :=
  signW k * (t ^ ((k:ℕ)^2) * (1 + t ^ (2*(k:ℕ))) / (1 - t ^ (2*(k:ℕ))))
private noncomputable def arithEquiv (k : ℕ+) :
    ℕ ≃ { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) } where
  toFun m :=
    let v : ℕ := (k:ℕ) + 2 * m
    have hkpos : 0 < (k:ℕ) := k.2
    have hv : 0 < v := by omega
    have hmod : v % 2 = (k:ℕ) % 2 := by omega
    have hle : (k:ℕ) ≤ v := by omega
    ⟨⟨v, hv⟩, hmod, hle⟩
  invFun j := (((j:ℕ+) : ℕ) - (k:ℕ)) / 2
  left_inv m := by
    have hkpos : 0 < (k:ℕ) := k.2
    simp only
    have : ((k:ℕ) + 2 * m - (k:ℕ)) / 2 = m := by omega
    exact this
  right_inv j := by
    obtain ⟨⟨jv, hjpos⟩, hmod, hle⟩ := j
    simp only [PNat.mk_coe] at hmod hle ⊢
    have hval : (k:ℕ) + 2 * ((jv - (k:ℕ)) / 2) = jv := by omega
    apply Subtype.ext
    apply PNat.eq
    exact hval

private lemma dblR_summable {t : ℝ} (ht : ‖t‖ < 1) : Summable (dblR t) := by
  have hL := dblL_summable ht
  have hLn := hL.norm
  have hmaj : Summable (fun c : ℕ+ × ℕ+ => 2 * ‖dblL t c‖) := hLn.mul_left 2
  apply Summable.of_norm_bounded hmaj
  intro c
  simp only [dblR]
  by_cases hC : (c.2:ℕ) % 2 = (c.1:ℕ) % 2 ∧ (c.1:ℕ) ≤ (c.2:ℕ)
  · rw [ite_eq_left hC]
    by_cases hE : (c.1:ℕ) = (c.2:ℕ)
    · rw [ite_eq_left hE]
      have heq : signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ)) = dblL t c := rfl
      rw [heq]
      have hnn := norm_nonneg (dblL t c)
      linarith
    · rw [ite_eq_right hE]
      have hD : ‖dblL t c‖ = ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
        simp only [dblL, signW, norm_mul]
        simp
      have h2n : ‖(2:ℝ)‖ = 2 := by
        rw [Real.norm_eq_abs]
        norm_num
      have hsn : ‖signW c.1‖ = 1 := by simp [signW]
      have hR : ‖(2:ℝ) * signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ))‖
          = 2 * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
        calc ‖(2:ℝ) * signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ))‖
            = ‖(2:ℝ)‖ * ‖signW c.1‖ * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
              rw [norm_mul, norm_mul]
          _ = 2 * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by rw [h2n, hsn, mul_one]
      rw [hR, hD]
  · rw [ite_eq_right hC]
    simp only [norm_zero]
    have hnn := norm_nonneg (dblL t c)
    linarith

private lemma dblR_zero (t : ℝ) (k : ℕ+) :
    dblR t (k, ((arithEquiv k) 0).val) = signW k * t ^ ((k:ℕ)^2) := by
  have h0 : (((arithEquiv k) 0).val : ℕ+) = k := by
    simp only [arithEquiv]
    apply PNat.eq
    simp
  rw [h0]
  simp only [dblR]
  simp only [le_refl, and_self]
  simp only [ite_true]
  congr 1
  congr 1
  rw [pow_two]

private lemma dblR_succ (t : ℝ) (k : ℕ+) (m : ℕ) :
    dblR t (k, ((arithEquiv k) (m+1)).val)
      = 2 * signW k * t ^ ((k:ℕ) * ((k:ℕ) + 2 * (m+1))) := by
  have hC1 : ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) % 2 = (k:ℕ) % 2 := by
    show ((k:ℕ) + 2 * (m+1)) % 2 = (k:ℕ) % 2
    omega
  have hC2 : (k:ℕ) ≤ ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) := by
    show (k:ℕ) ≤ (k:ℕ) + 2 * (m+1)
    omega
  have hne : (k:ℕ) ≠ ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) := by
    show (k:ℕ) ≠ (k:ℕ) + 2 * (m+1)
    omega
  have hexp : (k:ℕ) * ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ)
      = (k:ℕ) * ((k:ℕ) + 2 * (m+1)) := by
    show (k:ℕ) * ((k:ℕ) + 2 * (m+1)) = _
    rfl
  simp only [dblR]
  rw [ite_eq_left ⟨hC1, hC2⟩]
  rw [ite_eq_right hne]
  rw [hexp]

private lemma dblR_fiber_support (t : ℝ) (k : ℕ+) :
    Function.support (fun j : ℕ+ => dblR t (k, j))
      ⊆ { j : ℕ+ | (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) } := by
  intro j hj
  simp only [Function.support, ne_eq] at hj
  show (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ)
  by_contra hcon
  have h0 : dblR t (k, j) = 0 := by
    simp only [dblR]
    rw [ite_eq_right]
    exact hcon
  exact hj h0

private lemma per_k_R {t : ℝ} (ht : ‖t‖ < 1) (k : ℕ+) :
    ∑' j : ℕ+, dblR t (k, j) = singleR t k := by
  have hRsumm := dblR_summable ht
  have e1 : (∑' j : ℕ+, dblR t (k, j))
      = ∑' jm : { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) },
          dblR t (k, jm.val) := by
    have hsup := dblR_fiber_support t k
    have h := tsum_subtype_eq_of_support_subset (f := fun j : ℕ+ => dblR t (k, j))
      (s := { j : ℕ+ | (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) }) hsup
    exact h.symm
  have e2 : (∑' jm : { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) },
          dblR t (k, jm.val))
      = ∑' m : ℕ, dblR t (k, ((arithEquiv k) m).val) := by
    have h := (arithEquiv k).tsum_eq (f := fun jm : { j : ℕ+ // _ } => dblR t (k, jm.val))
    exact h.symm
  rw [e1, e2]
  have hfibM : Summable (fun m : ℕ => dblR t (k, ((arithEquiv k) m).val)) := by
    apply hRsumm.comp_injective
    intro a b hab
    have hval : (((arithEquiv k) a).val : ℕ+) = (((arithEquiv k) b).val : ℕ+) :=
      congrArg Prod.snd hab
    have := (arithEquiv k).injective (Subtype.ext hval)
    exact this
  rw [hfibM.tsum_eq_zero_add]
  rw [dblR_zero]
  have htail_eq : ∀ m : ℕ, dblR t (k, ((arithEquiv k) (m+1)).val)
      = (2 * signW k * t ^ ((k:ℕ)^2 + 2*(k:ℕ))) * (t ^ (2*(k:ℕ))) ^ m := by
    intro m
    rw [dblR_succ]
    have hexp : (k:ℕ) * ((k:ℕ) + 2 * (m+1)) = ((k:ℕ)^2 + 2*(k:ℕ)) + m * (2*(k:ℕ)) := by
      ring
    rw [hexp, pow_add, pow_mul]
    ring
  simp only [htail_eq]
  rw [tsum_mul_left]
  have hkpos : 0 < (k:ℕ) := k.2
  have h2k : 2 * (k:ℕ) ≠ 0 := by omega
  have htk2 : ‖t ^ (2*(k:ℕ))‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht h2k
  have hgeo := tsum_geometric_of_norm_lt_one (K := ℝ) (ξ := t ^ (2*(k:ℕ))) htk2
  rw [hgeo]
  simp only [singleR]
  have hR_ne : (1:ℝ) - t ^ (2*(k:ℕ)) ≠ 0 := by
    intro h
    have h1 : t ^ (2*(k:ℕ)) = 1 := by linarith
    have hn : ‖t ^ (2*(k:ℕ))‖ = 1 := by rw [h1, norm_one]
    linarith [htk2]
  have hAB : t ^ ((k:ℕ)^2) * t ^ (2*(k:ℕ)) = t ^ ((k:ℕ)^2 + 2*(k:ℕ)) := by
    rw [← pow_add]
  field_simp
  linear_combination (-2 * signW k) * hAB

private noncomputable def wR (p : ℕ × ℕ) : ℝ :=
  if p.2 % 2 = p.1 % 2 ∧ p.1 ≤ p.2 then
    (if p.1 = p.2 then (-1:ℝ)^(p.1+1) else 2 * (-1:ℝ)^(p.1+1))
  else 0
private noncomputable def Rcoeff (N : ℕ) : ℝ := ∑ x ∈ N.divisorsAntidiagonal, wR x

private lemma finite_right (N : ℕ) (t : ℝ) :
    ∑ x ∈ N.divisorsAntidiagonal, (wR x * t^(x.1*x.2))
      = Rcoeff N * t^N := by
  simp only [Rcoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem := Nat.mem_divisorsAntidiagonal.mp hx
  rw [hmem.1]

private lemma hgx (t : ℝ) (N : ℕ+) (x : ↥((N:ℕ).divisorsAntidiagonal)) :
    dblR t (sigmaAntidiagonalEquivProd ⟨N, x⟩) = wR x.1 * t^(x.1.1*x.1.2) := by
  simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, dblR, wR, signW,
    Equiv.coe_fn_mk, PNat.mk_coe]
  by_cases hC : x.1.2 % 2 = x.1.1 % 2 ∧ x.1.1 ≤ x.1.2
  · simp only [hC]
    by_cases hE : x.1.1 = x.1.2
    · simp [hE]
    · simp [hE]
  · simp [hC]

private lemma right_tsum_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' c : ℕ+ × ℕ+, dblR t c
      = ∑' N : ℕ+, Rcoeff (N:ℕ) * t^((N:ℕ)) := by
  have hsum : Summable (dblR t) := dblR_summable ht
  have hsig : Summable ((dblR t) ∘ sigmaAntidiagonalEquivProd) :=
    (sigmaAntidiagonalEquivProd.summable_iff (f := dblR t)).mpr hsum
  have heq := sigmaAntidiagonalEquivProd.tsum_eq (f := dblR t)
  rw [← heq]
  have hsig2 : Summable (fun c : (N : ℕ+) × ↥((N:ℕ).divisorsAntidiagonal) ↦
      dblR t (sigmaAntidiagonalEquivProd c)) := hsig
  rw [Summable.tsum_sigma hsig2]
  refine tsum_congr fun N => ?_
  rw [tsum_fintype]
  have hstep : ∑ x : ↥((N:ℕ).divisorsAntidiagonal),
        dblR t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
      = ∑ x ∈ (N:ℕ).divisorsAntidiagonal, (wR x * t^(x.1*x.2)) := by
    rw [← Finset.sum_attach ((N:ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => wR p * t^(p.1*p.2))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hgx]
  rw [hstep]
  exact finite_right (N:ℕ) t

private lemma sign_odd (d : ℕ) (hd : Odd d) : (-1:ℝ)^(d+1) = 1 := by
  have h : Even (d+1) := hd.add_odd (by decide)
  exact h.neg_one_pow

private lemma sign_even (d : ℕ) (hd : Even d) : (-1:ℝ)^(d+1) = -1 := by
  have h : Odd (d+1) := hd.add_odd (by decide)
  exact h.neg_one_pow

private lemma sign_add_same (a b : ℕ) (h : a % 2 = b % 2) :
    (-1:ℝ)^(a+1) + (-1:ℝ)^(b+1) = 2 * (-1:ℝ)^(a+1) := by
  have hab : (-1:ℝ)^(b+1) = (-1:ℝ)^(a+1) := by
    rcases Nat.even_or_odd a with ha|ha
    · have hb : Even b := by rw [Nat.even_iff] at ha ⊢; omega
      rw [sign_even a ha, sign_even b hb]
    · have hb : Odd b := by rw [Nat.odd_iff] at ha ⊢; omega
      rw [sign_odd a ha, sign_odd b hb]
  linarith

private lemma sign_add_ne (a b : ℕ) (h : a % 2 ≠ b % 2) :
    (-1:ℝ)^(a+1) + (-1:ℝ)^(b+1) = 0 := by
  rcases Nat.even_or_odd a with ha|ha
  · have hb : Odd b := by
      by_contra hcon
      have he : Even b := Nat.not_odd_iff_even.mp hcon
      rw [Nat.even_iff] at ha he
      exact h (by omega)
    rw [sign_even a ha, sign_odd b hb]; norm_num
  · have hb : Even b := by
      by_contra hcon
      have ho : Odd b := Nat.not_even_iff_odd.mp hcon
      rw [Nat.odd_iff] at ha ho
      exact h (by omega)
    rw [sign_odd a ha, sign_even b hb]; norm_num

private noncomputable def Rdiff2 (x : ℕ × ℕ) : ℝ := wR x - (-1:ℝ)^(x.1+1)

private lemma Rdiff_pair2 (a b : ℕ) : Rdiff2 (a, b) + Rdiff2 (b, a) = 0 := by
  simp only [Rdiff2, wR]
  by_cases hab : a = b
  · subst hab
    simp
  · have hlt : a < b ∨ b < a := by omega
    rcases hlt with h|h
    · have hab_le : a ≤ b := le_of_lt h
      have hba_nle : ¬ (b ≤ a) := by omega
      by_cases hpar : b % 2 = a % 2
      · have hpar2 : a % 2 = b % 2 := hpar.symm
        have hs := sign_add_same a b hpar2
        simp [hab, hpar, hab_le, hba_nle]
        linarith
      · have hpar2 : a % 2 ≠ b % 2 := by omega
        have hs := sign_add_ne a b hpar2
        simp [hab, hpar, hab_le, hba_nle]
        linarith
    · have hba_le : b ≤ a := le_of_lt h
      have hab_nle : ¬ (a ≤ b) := by omega
      by_cases hpar : a % 2 = b % 2
      · have hs := sign_add_same b a hpar.symm
        simp [hab, hpar, hba_le, hab_nle, Ne.symm hab]
        linarith
      · have hpar2 : b % 2 ≠ a % 2 := by omega
        have hs := sign_add_ne b a hpar2
        simp [hab, hpar, hba_le, hab_nle]
        linarith

private lemma R_eq_coeff2 (N : ℕ) (_hN : N ≠ 0) :
    Rcoeff N = ∑ d ∈ N.divisors, (-1:ℝ)^(d+1) := by
  have hCoeff : (∑ d ∈ N.divisors, (-1:ℝ)^(d+1))
      = ∑ x ∈ N.divisorsAntidiagonal, (-1:ℝ)^(x.1+1) := by
    have h2 := Nat.sum_divisorsAntidiagonal (M := ℝ) (f := fun a b => (-1:ℝ)^(a+1)) (n := N)
    simpa using h2.symm
  rw [hCoeff]
  simp only [Rcoeff]
  have hsub : ∑ x ∈ N.divisorsAntidiagonal, Rdiff2 x = 0 := by
    apply Finset.sum_involution (fun a ha => (a.2, a.1))
    · intro a ha
      exact Rdiff_pair2 a.1 a.2
    · rintro ⟨a1, a2⟩ ha hne
      intro hcon
      apply hne
      have h1 : (a2, a1) = (a1, a2) := hcon
      have h2 : a2 = a1 := congrArg Prod.fst h1
      have h3 : a1 = a2 := congrArg Prod.snd h1
      rw [h3] at hne
      simp only [Rdiff2, wR] at hne
      simp at hne
    · intro a ha
      have hmem := Nat.mem_divisorsAntidiagonal.mp ha
      rw [Nat.mem_divisorsAntidiagonal]
      constructor
      · rw [mul_comm]; exact hmem.1
      · exact hmem.2
    · intro a ha
      simp
  have hsplit := Finset.sum_sub_distrib (s := N.divisorsAntidiagonal)
    (f := fun x : ℕ × ℕ => wR x)
    (g := fun x : ℕ × ℕ => (-1:ℝ)^(x.1+1))
  have hRdiff_eq : ∀ x : ℕ × ℕ, Rdiff2 x = wR x - (-1:ℝ)^(x.1+1) := fun x => rfl
  simp only [hRdiff_eq] at hsub
  rw [hsplit] at hsub
  linarith

private lemma right_single_eq2 {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' k : ℕ+, singleR t k
      = ∑' N : ℕ+, Rcoeff (N:ℕ) * t^((N:ℕ)) := by
  have hsum := dblR_summable ht
  have e1 : (∑' k : ℕ+, singleR t k)
      = ∑' k : ℕ+, ∑' j : ℕ+, dblR t (k, j) := by
    refine tsum_congr fun k => ?_
    rw [per_k_R ht k]
  rw [e1, ← hsum.tsum_prod]
  exact right_tsum_eq ht

private lemma t_main_eq2 {t : ℝ} (ht : ‖t‖ < 1) :
    (∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))))
      = ∑' k : ℕ+, singleR t k := by
  rw [left_single_eq ht, right_single_eq2 ht]
  refine tsum_congr fun N => ?_
  have hN : (N:ℕ) ≠ 0 := ne_of_gt N.2
  rw [R_eq_coeff2 (N:ℕ) hN]

/-- **Ramanujan's transformation of the alternating series of 1/(x^k - 1).** For every real number
$x$ with $|x| > 1$, we have $x^k - 1 \ne 0$ and $x^{k^2}(x^{2k} - 1) \ne 0$ for every integer
$k \ge 1$, the series $\sum_{k \ge 1} (-1)^{k+1}/(x^k - 1)$ and
$\sum_{k \ge 1} (-1)^{k+1}(x^{2k} + 1)/(x^{k^2}(x^{2k} - 1))$ are summable, and
$\sum_{k=1}^{\infty} (-1)^{k+1}/(x^k - 1) =
\sum_{k=1}^{\infty} (-1)^{k+1}(x^{2k} + 1)/(x^{k^2}(x^{2k} - 1))$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
Proves `Wanted` entry `ramanujan_part1_ch6_entry13_ramanujanfactorial`.
-/
theorem ramanujan_part1_ch6_entry13_ramanujanfactorial (x : ℝ) (hx : 1 < |x|) :
    let leftTerm := fun j : ℕ =>
      (-1 : ℝ) ^ (j + 2) / (x ^ (j + 1) - 1)
    let rightTerm := fun j : ℕ =>
      ((-1 : ℝ) ^ (j + 2) * (x ^ (2 * (j + 1)) + 1)) /
        (x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1))
    (∀ j : ℕ, x ^ (j + 1) - 1 ≠ 0) ∧
      (∀ j : ℕ,
        x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1) ≠ 0) ∧
      Summable leftTerm ∧ Summable rightTerm ∧
      ∑' j, leftTerm j = ∑' j, rightTerm j := by
  intro leftTerm rightTerm
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    linarith
  have q_gt : (1:ℝ) < |x| := hx
  have q_pos : (0:ℝ) < |x| := by linarith [abs_nonneg x]
  have q1 : (1:ℝ) ≤ |x| := by linarith
  set t : ℝ := x⁻¹ with ht_def
  have ht0 : t ≠ 0 := inv_ne_zero hx0
  have hx_norm : (1:ℝ) < ‖x‖ := by rw [Real.norm_eq_abs]; exact hx
  have ht_norm : ‖t‖ < 1 := by
    rw [ht_def, norm_inv]
    exact inv_lt_one_of_one_lt₀ hx_norm
  have hleft_ne : ∀ j : ℕ, x ^ (j + 1) - 1 ≠ 0 := by
    intro j
    have hq : (1:ℝ) < |x| ^ (j + 1) := one_lt_pow₀ q_gt (by omega)
    have hnorm : |x ^ (j + 1)| = |x| ^ (j + 1) := abs_pow x (j+1)
    intro h
    have h1 : x ^ (j + 1) = 1 := by linarith
    rw [h1] at hnorm
    simp at hnorm
    linarith
  have hright_ne : ∀ j : ℕ,
      x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1) ≠ 0 := by
    intro j
    apply mul_ne_zero
    · exact pow_ne_zero _ hx0
    · have hq : (1:ℝ) < |x| ^ (2*(j+1)) := one_lt_pow₀ q_gt (by omega)
      intro h
      have h1 : x ^ (2*(j+1)) = 1 := by linarith
      have hnorm : |x ^ (2*(j+1))| = |x| ^ (2*(j+1)) := abs_pow x _
      rw [h1] at hnorm
      simp at hnorm
      linarith
  have hleft_summ : Summable leftTerm := by
    show Summable (fun j : ℕ => (-1 : ℝ) ^ (j + 2) / (x ^ (j + 1) - 1))
    have q_sub_pos : (0:ℝ) < |x| - 1 := by linarith
    have hpow_ge : ∀ j : ℕ, (1:ℝ) ≤ |x| ^ j := fun j => one_le_pow₀ q1
    have hgeo : Summable (fun j : ℕ => (1 / (|x| - 1)) * ((1:ℝ)/|x|) ^ j) := by
      apply Summable.mul_left
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/|x|)]
      exact (div_lt_one q_pos).mpr q_gt
    apply Summable.of_norm_bounded hgeo
    intro j
    have hden_pos : (0:ℝ) < |x| ^ (j+1) - 1 := by
      have := one_lt_pow₀ q_gt (show j + 1 ≠ 0 by omega)
      linarith
    have hden2_pos : (0:ℝ) < (|x| - 1) * |x| ^ j := mul_pos q_sub_pos (pow_pos q_pos j)
    have hle : (|x| - 1) * |x| ^ j ≤ |x| ^ (j+1) - 1 := by
      have hj : (1:ℝ) ≤ |x| ^ j := hpow_ge j
      have hsplit : |x| ^ (j+1) = |x| ^ j * |x| := pow_succ |x| j
      nlinarith
    have h1 : ‖(-1 : ℝ) ^ (j + 2) / (x ^ (j + 1) - 1)‖ = 1 / |x ^ (j+1) - 1| := by
      rw [norm_div, norm_pow]
      simp [Real.norm_eq_abs]
    rw [h1]
    have hab : |x| ^ (j+1) - 1 ≤ |x ^ (j+1) - 1| := by
      have h := abs_sub_abs_le_abs_sub (x ^ (j+1)) (1:ℝ)
      rw [abs_one, abs_pow] at h
      exact h
    have h2 : (1:ℝ) / |x ^ (j+1) - 1| ≤ 1 / (|x| ^ (j+1) - 1) :=
      one_div_le_one_div_of_le hden_pos hab
    have h5 : (1:ℝ) / ((|x| - 1) * |x| ^ j) = (1 / (|x| - 1)) * ((1:ℝ)/|x|) ^ j := by
      rw [div_pow, one_pow]
      field_simp
    have h4 : (1:ℝ) / (|x| ^ (j+1) - 1) ≤ 1 / ((|x| - 1) * |x| ^ j) :=
      one_div_le_one_div_of_le hden2_pos hle
    rw [← h5]
    linarith
  have hright_summ : Summable rightTerm := by
    show Summable (fun j : ℕ =>
      ((-1 : ℝ) ^ (j + 2) * (x ^ (2 * (j + 1)) + 1)) /
        (x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1)))
    have q2_gt : (1:ℝ) < |x| ^ 2 := one_lt_pow₀ q_gt (by norm_num)
    have q2sub_pos : (0:ℝ) < |x|^2 - 1 := by linarith
    have hgeo : Summable (fun j : ℕ => ((|x|^2 + 1) / (|x|^2 - 1)) * ((1:ℝ)/|x|) ^ j) := by
      apply Summable.mul_left
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/|x|)]
      exact (div_lt_one q_pos).mpr q_gt
    apply Summable.of_norm_bounded hgeo
    intro j
    have hpow2k_gt : (1:ℝ) < |x|^(2*(j+1)) := one_lt_pow₀ q_gt (by omega)
    have hden1_pos : (0:ℝ) < |x|^(2*(j+1)) - 1 := by linarith
    have hdenx_pos : (0:ℝ) < |x|^((j+1)^2) := pow_pos q_pos _
    have hBA : |x|^2 ≤ |x|^(2*(j+1)) := pow_le_pow_right₀ q1 (by omega)
    have hratio : (|x|^(2*(j+1)) + 1) / (|x|^(2*(j+1)) - 1)
        ≤ (|x|^2 + 1) / (|x|^2 - 1) := by
      rw [le_div_iff₀ q2sub_pos, div_mul_eq_mul_div, div_le_iff₀ hden1_pos]
      nlinarith [hBA, hpow2k_gt, q2_gt]
    have hnum : |x ^ (2*(j+1)) + 1| ≤ |x|^(2*(j+1)) + 1 := by
      calc |x ^ (2*(j+1)) + 1| ≤ |x ^ (2*(j+1))| + |1| := abs_add_le _ _
      _ = |x|^(2*(j+1)) + 1 := by rw [abs_one, abs_pow]
    have hden1 : |x|^(2*(j+1)) - 1 ≤ |x ^ (2*(j+1)) - 1| := by
      have h := abs_sub_abs_le_abs_sub (x ^ (2*(j+1))) (1:ℝ)
      rw [abs_one, abs_pow] at h
      exact h
    have hden_abs_pos : (0:ℝ) < |x ^ (2*(j+1)) - 1| := lt_of_lt_of_le hden1_pos hden1
    have h1 : ‖(-1 : ℝ) ^ (j + 2)‖ = 1 := by simp
    have hnorm_eq : ‖(-1 : ℝ) ^ (j + 2) * (x ^ (2 * (j + 1)) + 1) /
          (x ^ ((j + 1) ^ 2) * (x ^ (2 * (j + 1)) - 1))‖
        = |x ^ (2*(j+1)) + 1| / (|x|^((j+1)^2) * |x ^ (2*(j+1)) - 1|) := by
      rw [norm_div, norm_mul, h1, one_mul, norm_mul, norm_pow,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [hnorm_eq]
    have hbase0 : (0:ℝ) ≤ (1:ℝ)/|x| := by positivity
    have hbase1 : (1:ℝ)/|x| ≤ 1 := le_of_lt ((div_lt_one q_pos).mpr q_gt)
    have hj_le : j ≤ (j+1)^2 := by nlinarith
    have hpow_le : ((1:ℝ)/|x|)^((j+1)^2) ≤ ((1:ℝ)/|x|)^j :=
      pow_le_pow_of_le_one hbase0 hbase1 hj_le
    have hpow_eq : (1:ℝ) / |x|^((j+1)^2) = ((1:ℝ)/|x|)^((j+1)^2) := by
      rw [div_pow, one_pow]
    have hNUM_nonneg : (0:ℝ) ≤ |x|^(2*(j+1)) + 1 := by positivity
    have hle1 : |x ^ (2*(j+1)) + 1| / |x ^ (2*(j+1)) - 1|
        ≤ (|x|^(2*(j+1)) + 1) / (|x|^(2*(j+1)) - 1) :=
      calc |x ^ (2*(j+1)) + 1| / |x ^ (2*(j+1)) - 1|
          ≤ (|x|^(2*(j+1)) + 1) / |x ^ (2*(j+1)) - 1| :=
            div_le_div_of_nonneg_right hnum (le_of_lt hden_abs_pos)
        _ ≤ (|x|^(2*(j+1)) + 1) / (|x|^(2*(j+1)) - 1) :=
            div_le_div_of_nonneg_left hNUM_nonneg hden1_pos hden1
    have hfrac : |x ^ (2*(j+1)) + 1| / (|x|^((j+1)^2) * |x ^ (2*(j+1)) - 1|)
        = (|x ^ (2*(j+1)) + 1| / |x ^ (2*(j+1)) - 1|) * (1 / |x|^((j+1)^2)) := by
      field_simp
    rw [hfrac, hpow_eq]
    calc (|x ^ (2*(j+1)) + 1| / |x ^ (2*(j+1)) - 1|) * ((1:ℝ)/|x|)^((j+1)^2)
        ≤ ((|x|^(2*(j+1)) + 1) / (|x|^(2*(j+1)) - 1)) * ((1:ℝ)/|x|)^((j+1)^2) := by
          apply mul_le_mul_of_nonneg_right hle1 (pow_nonneg hbase0 _)
      _ ≤ ((|x|^2 + 1) / (|x|^2 - 1)) * ((1:ℝ)/|x|)^((j+1)^2) := by
          apply mul_le_mul_of_nonneg_right hratio (pow_nonneg hbase0 _)
      _ ≤ ((|x|^2 + 1) / (|x|^2 - 1)) * ((1:ℝ)/|x|)^j := by
          apply mul_le_mul_of_nonneg_left hpow_le (le_of_lt (div_pos (by positivity) q2sub_pos))
  -- t-powers nonzero and one-sub facts
  have ht_pow_ne_one : ∀ n : ℕ, n ≠ 0 → t ^ n ≠ 1 := by
    intro n hn h
    have h1 : ‖t ^ n‖ = 1 := by rw [h, norm_one]
    rw [norm_pow] at h1
    have hlt : ‖t‖ ^ n < 1 := pow_lt_one₀ (norm_nonneg _) ht_norm hn
    linarith
  have hx_pow_ne : ∀ n : ℕ, x ^ n ≠ 0 := fun n => pow_ne_zero n hx0
  have ht_pow_ne : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht0
  have hleft_eq : ∀ j : ℕ, leftTerm j
      = (-1:ℝ)^(j+2) * (t^(j+1) / (1 - t^(j+1))) := by
    intro j
    show (-1:ℝ)^(j+2) / (x^(j+1) - 1)
      = (-1:ℝ)^(j+2) * (t^(j+1) / (1 - t^(j+1)))
    have htp : t^(j+1) = (x^(j+1))⁻¹ := by rw [ht_def, inv_pow]
    rw [htp]
    have hxj : x^(j+1) ≠ 0 := hx_pow_ne _
    have h1 : (1:ℝ) - (x^(j+1))⁻¹ ≠ 0 := by
      intro h
      have h2 : (x^(j+1))⁻¹ = 1 := by linarith
      have h3 : x^(j+1) = 1 := by
        field_simp at h2
        linarith [h2]
      exact hleft_ne j (by linarith)
    field_simp
  have hright_eq : ∀ j : ℕ, rightTerm j
      = (-1:ℝ)^(j+2) * (t^((j+1)^2) * (1 + t^(2*(j+1))) / (1 - t^(2*(j+1)))) := by
    intro j
    show ((-1:ℝ)^(j+2) * (x^(2*(j+1)) + 1)) / (x^((j+1)^2) * (x^(2*(j+1)) - 1))
      = (-1:ℝ)^(j+2) * (t^((j+1)^2) * (1 + t^(2*(j+1))) / (1 - t^(2*(j+1))))
    have htp1 : t^((j+1)^2) = (x^((j+1)^2))⁻¹ := by rw [ht_def, inv_pow]
    have htp2 : t^(2*(j+1)) = (x^(2*(j+1)))⁻¹ := by rw [ht_def, inv_pow]
    rw [htp1, htp2]
    have hx1 : x^((j+1)^2) ≠ 0 := hx_pow_ne _
    have hx2 : x^(2*(j+1)) ≠ 0 := hx_pow_ne _
    have h1 : (1:ℝ) - (x^(2*(j+1)))⁻¹ ≠ 0 := by
      intro h
      have h2 : (x^(2*(j+1)))⁻¹ = 1 := by linarith
      have hxeq : x^(2*(j+1)) = 1 := by
        field_simp at h2
        linarith [h2]
      have hden := hright_ne j
      have hne : x^(2*(j+1)) - 1 ≠ 0 := by
        intro hz
        apply hden
        simp [hz]
      exact hne (by linarith)
    field_simp
  have hLre : (∑' j : ℕ, leftTerm j)
      = ∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))) := by
    have e1 : (∑' j : ℕ, leftTerm j)
        = ∑' j : ℕ, ((-1:ℝ)^(j+1+1) * (t^(j+1) / (1 - t^(j+1)))) :=
      tsum_congr hleft_eq
    have e2 : (∑' j : ℕ, ((-1:ℝ)^(j+1+1) * (t^(j+1) / (1 - t^(j+1)))))
        = ∑' k : ℕ+, ((-1:ℝ)^((k:ℕ)+1) * (t^((k:ℕ)) / (1 - t^((k:ℕ))))) := by
      have hlem := tsum_pnat_eq_tsum_succ (M := ℝ)
        (f := fun n : ℕ => (-1:ℝ)^(n+1) * (t^n / (1 - t^n)))
      rw [← hlem]
    rw [e1, e2]
    rfl
  have hRre : (∑' j : ℕ, rightTerm j) = ∑' k : ℕ+, singleR t k := by
    have e1 : (∑' j : ℕ, rightTerm j)
        = ∑' j : ℕ, ((-1:ℝ)^(j+1+1) * (t^((j+1)^2) * (1 + t^(2*(j+1))) / (1 - t^(2*(j+1))))) :=
      tsum_congr hright_eq
    have e2 : (∑' j : ℕ, ((-1:ℝ)^(j+1+1) * (t^((j+1)^2) * (1 + t^(2*(j+1))) / (1 - t^(2*(j+1))))))
        = ∑' k : ℕ+, ((-1:ℝ)^((k:ℕ)+1) * (t^((k:ℕ)^2) * (1 + t^(2*(k:ℕ))) / (1 - t^(2*(k:ℕ))))) := by
      have hlem := tsum_pnat_eq_tsum_succ (M := ℝ)
        (f := fun n : ℕ => (-1:ℝ)^(n+1) * (t^(n^2) * (1 + t^(2*n)) / (1 - t^(2*n))))
      rw [← hlem]
    rw [e1, e2]
    rfl
  have hTeq := t_main_eq2 ht_norm
  have heq : (∑' j : ℕ, leftTerm j) = ∑' j : ℕ, rightTerm j := by
    rw [hLre, hRre]
    exact hTeq
  exact ⟨hleft_ne, hright_ne, hleft_summ, hright_summ, heq⟩

end

end Entry13Ramanujanfactorial

end MathlibExt.Analysis.Ramanujan.Part1Ch6
