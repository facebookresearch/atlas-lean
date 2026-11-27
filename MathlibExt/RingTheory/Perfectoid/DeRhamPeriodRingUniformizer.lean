/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/DeRhamPrintTDict.lean` and
`ZInQKernel/Contrib/OneProof/BdRInvariants.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingGalois
import Mathlib.NumberTheory.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The uniformizer `[ε] - 1` of `B_dR^+` and the cyclotomic character

Choose a compatible system `1, ζ_p, ζ_{p²}, …` of `p`-power roots of unity in `ℚ̄_p`
(`PadicComplexInt.zetaPow`) and let `ε = (1, ζ_p, ζ_{p²}, …)` be the corresponding element of the
tilt `𝓞_ℂ_[p]♭` (`PadicComplexInt.epsilon`), so that `ε♯ = 1` and `ε ≠ 1`. We show:

* `[ε] - 1` is a uniformizer of the discrete valuation ring `B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p`
  (`PadicComplexInt.irreducible_algebraMap_teichmuller_epsilon_sub_one`). Indeed
  `[ε] - 1 = ω · ([ε^{1/p}] - 1)` with `ω = Σ_{i < p} [ε^{1/p}]^i`, where `[ε^{1/p}] - 1` is a unit
  of `B_dR^+` since `θ([ε^{1/p}] - 1) = ζ_p - 1 ≠ 0`, and `ω`, like `ξ`, generates the kernel of
  `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]` (L. Berger, *Représentations p-adiques et équations
  différentielles*, Invent. Math. 148 (2002), §1.1), so `ω` generates the maximal ideal `(ξ)` of
  `B_dR^+`. Since `log [ε] ≡ [ε] - 1` modulo `([ε] - 1)²`, this is equivalent to Fontaine's
  statement that the period `t = log [ε]` is a uniformizer of `B_dR^+` (J.-M. Fontaine, *Le corps
  des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.4 p. 72).
* For `σ ∈ Gal(ℚ̄_p/ℚ_p)`, `σ([ε] - 1) = ([ε] - 1) · w` with `θ(w) = χ(σ)`, the `p`-adic
  cyclotomic character of `σ`
  (`PadicComplexInt.exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one`): modulo
  `p^m`, `σ(ε) = ε^{a} ρ^{p^m}` with `a ≡ χ(σ)` and `ρ♯ = 1`.
-/

@[expose] public noncomputable section

open Ideal WittVector MathlibExt.AlgebraicGeometry.HodgeTateComparison

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p

/-- There is a primitive `p`-th root of unity in `ℚ̄_p`. -/
theorem exists_isPrimitiveRoot_padicAlgCl : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ p := by
  have : NeZero (p : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (PadicAlgCl p))
    (Polynomial.degree_cyclotomic_pos p (PadicAlgCl p) hp.out.pos).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/-- A compatible system `1, ζ_p, ζ_{p²}, …` of `p`-power roots of unity in `ℚ̄_p`: `zetaPow p 1`
is a primitive `p`-th root of unity and `zetaPow p (n + 1) ^ p = zetaPow p n`. -/
def zetaPow : ℕ → PadicAlgCl p
  | 0 => 1
  | 1 => (exists_isPrimitiveRoot_padicAlgCl p).choose
  | n + 2 => (IsAlgClosed.exists_pow_nat_eq (zetaPow (n + 1)) hp.out.pos).choose

/-- `zetaPow p 0 = 1`. -/
@[simp]
theorem zetaPow_zero : zetaPow p 0 = 1 :=
  rfl

/-- `zetaPow p 1` is a primitive `p`-th root of unity. -/
theorem isPrimitiveRoot_zetaPow_one : IsPrimitiveRoot (zetaPow p 1) p :=
  (exists_isPrimitiveRoot_padicAlgCl p).choose_spec

/-- `zetaPow p (n + 1)` is a `p`-th root of `zetaPow p n`. -/
theorem zetaPow_succ_pow (n : ℕ) : zetaPow p (n + 1) ^ p = zetaPow p n := by
  rcases n with _ | n
  · exact (isPrimitiveRoot_zetaPow_one p).pow_eq_one
  · exact (IsAlgClosed.exists_pow_nat_eq (zetaPow p (n + 1)) hp.out.pos).choose_spec

/-- `zetaPow p n` is a `p ^ n`-th root of unity. -/
theorem zetaPow_pow (n : ℕ) : zetaPow p n ^ p ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, zetaPow_succ_pow, ih]

/-- The roots of unity `zetaPow p n` have norm `1` in `ℂ_[p]`. -/
theorem norm_zetaPow (n : ℕ) : ‖((zetaPow p n : PadicAlgCl p) : ℂ_[p])‖ = 1 := by
  have h1 : ‖((zetaPow p n : PadicAlgCl p) : ℂ_[p])‖ ^ p ^ n = 1 := by
    rw [← norm_pow, PadicComplex.coe_eq, ← map_pow, zetaPow_pow, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).mp h1

/-- The element `ε = (1, ζ_p, ζ_{p²}, …)` of the tilt of `𝓞_ℂ_[p]`: its `n`-th component is the
class modulo `p` of `zetaPow p n`. -/
def epsilon : PreTilt 𝓞_ℂ_[p] p :=
  ⟨fun n => Ideal.Quotient.mk _
      ⟨((zetaPow p n : PadicAlgCl p) : ℂ_[p]), (mem_iff_norm_le_one p _).mpr (norm_zetaPow p n).le⟩,
    fun n => by
      rw [← map_pow]
      congr 1
      apply Subtype.ext
      change ((zetaPow p (n + 1) : PadicAlgCl p) : ℂ_[p]) ^ p =
        ((zetaPow p n : PadicAlgCl p) : ℂ_[p])
      rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow, zetaPow_succ_pow]⟩

/-! ### Elements of the tilt from compatible sequences -/

/-- The element `(z₀, z₁, …)` of the tilt of `𝓞_ℂ_[p]` defined by a sequence with
`z (n + 1) ^ p = z n`. -/
private def mkSeq (z : ℕ → 𝓞_ℂ_[p]) (hz : ∀ n, z (n + 1) ^ p = z n) : PreTilt 𝓞_ℂ_[p] p :=
  ⟨fun n => Ideal.Quotient.mk _ (z n), fun n => by rw [← map_pow, hz]⟩

private theorem coeff_mkSeq (z : ℕ → 𝓞_ℂ_[p]) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) :
    PreTilt.coeff n (mkSeq p z hz) = Ideal.Quotient.mk _ (z n) :=
  rfl

private theorem pow_seq (z : ℕ → 𝓞_ℂ_[p]) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) :
    z n ^ p ^ n = z 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hz, ih]

/-- If the components of `x` in the tilt of `𝓞_ℂ_[p]` are the classes of `z n`, where
`z (n + 1) ^ p = z n`, then `x♯ = z 0`. -/
theorem untilt_eq_of_coeff (z : ℕ → 𝓞_ℂ_[p]) (hz : ∀ n, z (n + 1) ^ p = z n)
    (x : PreTilt 𝓞_ℂ_[p] p) (hx : ∀ n, PreTilt.coeff n x = Ideal.Quotient.mk _ (z n)) :
    x.untilt = z 0 := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : 𝓞_ℂ_[p])})]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  have h1 : x.untiltRoot n - z n ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, PreTilt.mk_untiltRoot, hx]
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [PreTilt.untiltRoot_pow, pow_seq p z hz] at h2
  exact (pow_dvd_pow _ n.le_succ).trans h2

private theorem untilt_mkSeq (z : ℕ → 𝓞_ℂ_[p]) (hz : ∀ n, z (n + 1) ^ p = z n) :
    (mkSeq p z hz).untilt = z 0 :=
  untilt_eq_of_coeff p z hz _ (coeff_mkSeq p z hz)

/-- The roots of unity `zetaPow p n`, as elements of `𝓞_ℂ_[p]`. -/
def zetaPowInt (n : ℕ) : 𝓞_ℂ_[p] :=
  ⟨((zetaPow p n : PadicAlgCl p) : ℂ_[p]), (mem_iff_norm_le_one p _).mpr (norm_zetaPow p n).le⟩

/-- `zetaPowInt p (n + 1)` is a `p`-th root of `zetaPowInt p n`. -/
theorem zetaPowInt_succ_pow (n : ℕ) : zetaPowInt p (n + 1) ^ p = zetaPowInt p n := by
  apply Subtype.ext
  change ((zetaPow p (n + 1) : PadicAlgCl p) : ℂ_[p]) ^ p = ((zetaPow p n : PadicAlgCl p) : ℂ_[p])
  rw [PadicComplex.coe_eq, PadicComplex.coe_eq, ← map_pow, zetaPow_succ_pow]

/-- `zetaPowInt p 0 = 1`. -/
theorem zetaPowInt_zero : zetaPowInt p 0 = 1 := by
  apply Subtype.ext
  change ((zetaPow p 0 : PadicAlgCl p) : ℂ_[p]) = 1
  rw [zetaPow_zero, PadicComplex.coe_eq, map_one]

/-- `zetaPowInt p 1`, a primitive `p`-th root of unity, is not `1`. -/
theorem zetaPowInt_one_ne_one : zetaPowInt p 1 ≠ 1 := fun h => by
  have h1 : ((zetaPow p 1 : PadicAlgCl p) : ℂ_[p]) = 1 := congrArg Subtype.val h
  rw [PadicComplex.coe_eq, ← map_one (algebraMap (PadicAlgCl p) ℂ_[p])] at h1
  exact (isPrimitiveRoot_zetaPow_one p).ne_one hp.out.one_lt
    ((algebraMap (PadicAlgCl p) ℂ_[p]).injective h1)

private theorem epsilon_eq_mkSeq : epsilon p = mkSeq p (zetaPowInt p) (zetaPowInt_succ_pow p) :=
  rfl

/-- `ε♯ = 1`. -/
@[simp]
theorem untilt_epsilon : (epsilon p).untilt = 1 := by
  rw [epsilon_eq_mkSeq, untilt_mkSeq, zetaPowInt_zero]

/-- `ε^{1/p} = (ζ_p, ζ_{p²}, …)`. -/
private def eps1 : PreTilt 𝓞_ℂ_[p] p :=
  mkSeq p (fun n => zetaPowInt p (n + 1)) (fun n => zetaPowInt_succ_pow p (n + 1))

private theorem untilt_eps1 : (eps1 p).untilt = zetaPowInt p 1 :=
  untilt_mkSeq p _ _

private theorem eps1_pow : eps1 p ^ p = epsilon p := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (eps1 p ^ p) = PreTilt.coeff n (epsilon p)
  rw [map_pow, eps1, epsilon_eq_mkSeq, coeff_mkSeq, coeff_mkSeq, ← map_pow, zetaPowInt_succ_pow]

private theorem eps1_sub_one_ne_zero : eps1 p - 1 ≠ 0 := by
  intro h
  have h2 := congrArg PreTilt.untilt (sub_eq_zero.mp h)
  rw [untilt_eps1, map_one] at h2
  exact zetaPowInt_one_ne_one p h2

/-- `ε ≠ 1`. -/
theorem epsilon_ne_one : epsilon p ≠ 1 := by
  intro h
  apply eps1_sub_one_ne_zero p
  rw [← pow_eq_zero_iff hp.out.ne_zero, sub_pow_char, one_pow, eps1_pow, h, sub_self]

/-! ### Divisibility in the tilt and `‖ζ_{p²} - 1‖ ^ (p (p - 1)) ≥ ‖p‖` -/

/-- If `‖c♯‖ ≤ ‖a♯‖` and `a♯ ≠ 0`, then `a` divides `c` in the tilt of `𝓞_ℂ_[p]`. -/
private theorem dvd_of_norm_le (a c : PreTilt 𝓞_ℂ_[p] p)
    (ha : ((a.untilt : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0)
    (hle : ‖((c.untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤ ‖((a.untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖) : a ∣ c := by
  have han : ∀ n, ‖((a.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ p ^ n =
      ‖((a.untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : 𝓞_ℂ_[p] => ‖(z : ℂ_[p])‖) (PreTilt.untiltRoot_pow a n)
    simpa [norm_pow] using h
  have hcn : ∀ n, ‖((c.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ p ^ n =
      ‖((c.untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : 𝓞_ℂ_[p] => ‖(z : ℂ_[p])‖) (PreTilt.untiltRoot_pow c n)
    simpa [norm_pow] using h
  have hne : ∀ n, ((a.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := fun n h0 => by
    have := han n
    rw [h0, norm_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at this
    exact ha (norm_eq_zero.mp this.symm)
  have hle' : ∀ n, ‖((c.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((a.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p])‖ :=
    fun n => by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
        (pow_ne_zero n hp.out.ne_zero)).mp ?_
      rw [hcn, han]
      exact hle
  let e : ℕ → 𝓞_ℂ_[p] := fun n => ⟨((c.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p]) /
      ((a.untiltRoot n : 𝓞_ℂ_[p]) : ℂ_[p]),
    (mem_iff_norm_le_one p _).mpr (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle' n) (norm_nonneg _))⟩
  have he : ∀ n, e (n + 1) ^ p = e n := fun n => by
    apply Subtype.ext
    simp only [e, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, PreTilt.untiltRoot_succ_pow,
      PreTilt.untiltRoot_succ_pow]
  have hce : ∀ n, c.untiltRoot n = a.untiltRoot n * e n := fun n => by
    apply Subtype.ext
    simp only [e, MulMemClass.coe_mul]
    field_simp [hne n]
  refine ⟨mkSeq p e he, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n (a * mkSeq p e he)
  rw [map_mul, coeff_mkSeq, ← PreTilt.mk_untiltRoot, ← PreTilt.mk_untiltRoot, ← map_mul, hce]

private theorem norm_one_sub_pow_le (ζ : 𝓞_ℂ_[p]) (k : ℕ) :
    ‖(1 : ℂ_[p]) - (ζ : ℂ_[p]) ^ k‖ ≤ ‖(1 : ℂ_[p]) - (ζ : ℂ_[p])‖ := by
  have h : (1 : 𝓞_ℂ_[p]) - ζ ^ k = (1 - ζ) * ∑ i ∈ Finset.range k, ζ ^ i :=
    (mul_neg_geom_sum ζ k).symm
  have h' := congrArg (fun z : 𝓞_ℂ_[p] => ‖(z : ℂ_[p])‖) h
  simp only [MulMemClass.coe_mul] at h'
  push_cast at h'
  rw [h', norm_mul]
  have hs := norm_le_one p (∑ i ∈ Finset.range k, ζ ^ i)
  push_cast at hs
  calc ‖(1 : ℂ_[p]) - ζ‖ * ‖∑ i ∈ Finset.range k, (ζ : ℂ_[p]) ^ i‖ ≤ ‖(1 : ℂ_[p]) - ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := mul_one _

private theorem isPrimitiveRoot_zetaPowInt_two :
    IsPrimitiveRoot ((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p]) (p ^ 2) := by
  have h1 : ((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p]) ^ p ^ 1 ≠ 1 := by
    intro h
    apply zetaPowInt_one_ne_one p
    apply Subtype.ext
    rw [pow_one] at h
    rw [← zetaPowInt_succ_pow p 1]
    push_cast
    exact h
  have h2 : ((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p]) ^ p ^ (1 + 1) = 1 := by
    have h3 := pow_seq p (zetaPowInt p) (zetaPowInt_succ_pow p) 2
    rw [zetaPowInt_zero] at h3
    have h4 := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) h3
    simpa using h4
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

/-- `‖p‖ ≤ ‖1 - ζ_{p²}‖ ^ (p (p - 1))`, from `Φ_{p²}(1) = p`. -/
private theorem norm_p_le :
    ‖(p : ℂ_[p])‖ ≤ ‖(1 : ℂ_[p]) - ((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ (p * (p - 1)) := by
  have hprim := isPrimitiveRoot_zetaPowInt_two p
  have hev : Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (1 + 1)) ℂ_[p]) = p :=
    Polynomial.eval_one_cyclotomic_prime_pow 1
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  rw [← hev, norm_prod]
  have hcard : (primitiveRoots (p ^ 2) ℂ_[p]).card = p * (p - 1) := by
    rw [hprim.card_primitiveRoots, Nat.totient_prime_pow hp.out (by norm_num)]
    simp
  rw [← hcard, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun μ hμ => ?_
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have : NeZero (p ^ 2) := ⟨hp2.ne'⟩
  have hμ' : μ ^ p ^ 2 = 1 := ((mem_primitiveRoots hp2).mp hμ).pow_eq_one
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμ'
  exact norm_one_sub_pow_le p (zetaPowInt p 2) i

/-! ### Fontaine's generator `ω = Σ_{i < p} [ε^{1/p}]^i` of the kernel of `θ` -/

private theorem geom_sum_eq_sub_one_pow (e : PreTilt 𝓞_ℂ_[p] p) (he : e - 1 ≠ 0) :
    ∑ i ∈ Finset.range p, e ^ i = (e - 1) ^ (p - 1) := by
  have h1 : (∑ i ∈ Finset.range p, e ^ i) * (e - 1) = (e - 1) ^ (p - 1) * (e - 1) := by
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow]
  exact mul_right_cancel₀ he h1

private theorem sum_zetaPowInt_one_eq_zero : ∑ i ∈ Finset.range p, zetaPowInt p 1 ^ i = 0 := by
  have h : (∑ i ∈ Finset.range p, zetaPowInt p 1 ^ i) * (zetaPowInt p 1 - 1) = 0 := by
    rw [geom_sum_mul, zetaPowInt_succ_pow p 0, zetaPowInt_zero, sub_self]
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (zetaPowInt_one_ne_one p))

/-- `‖((ε^{1/p} - 1) ^ (p - 1))♯‖ ≥ ‖p‖`. -/
private theorem norm_untilt_pow_ge :
    ‖(p : ℂ_[p])‖ ≤ ‖((((eps1 p - 1) ^ (p - 1)).untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖ := by
  set y := eps1 p - 1
  set r := ‖((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1‖
  have hr : ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := by
    have := norm_p_le p
    rwa [norm_sub_rev] at this
  have hp1 := PadicComplex.norm_p_lt_one p
  have hp0 := PadicComplex.norm_p_pos p
  have hrp : ‖(p : ℂ_[p])‖ < r := by
    by_contra hcon
    push Not at hcon
    have h2 : 1 < p * (p - 1) := by
      have := hp.out.two_le
      have h3 : 1 ≤ p - 1 := by omega
      nlinarith
    have := pow_lt_self_of_lt_one₀ hp0 hp1 h2
    have h4 : r ^ (p * (p - 1)) ≤ ‖(p : ℂ_[p])‖ ^ (p * (p - 1)) :=
      pow_le_pow_left₀ (norm_nonneg _) hcon _
    linarith
  -- `y.untiltRoot 1 ≡ ζ_{p²} - 1 (mod p)`
  have hmem : y.untiltRoot 1 - (zetaPowInt p 2 - 1) ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, PreTilt.mk_untiltRoot, map_sub, map_sub, map_one, eps1, coeff_mkSeq,
      map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hdiff : ‖((y.untiltRoot 1 - (zetaPowInt p 2 - 1) : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    rw [← hc]
    push_cast
    rw [norm_mul]
    have := norm_le_one p c
    nlinarith [norm_nonneg ((c : 𝓞_ℂ_[p]) : ℂ_[p]), norm_nonneg (p : ℂ_[p])]
  have hroot : r ≤ ‖((y.untiltRoot 1 : 𝓞_ℂ_[p]) : ℂ_[p])‖ := by
    have h1 : ((zetaPowInt p 2 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1 =
        ((y.untiltRoot 1 : 𝓞_ℂ_[p]) : ℂ_[p]) -
          ((y.untiltRoot 1 - (zetaPowInt p 2 - 1) : 𝓞_ℂ_[p]) : ℂ_[p]) := by
      push_cast; ring
    have h2 := IsUltrametricDist.norm_add_le_max ((y.untiltRoot 1 : 𝓞_ℂ_[p]) : ℂ_[p])
      (-((y.untiltRoot 1 - (zetaPowInt p 2 - 1) : 𝓞_ℂ_[p]) : ℂ_[p]))
    rw [norm_neg, ← sub_eq_add_neg, ← h1] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hy : ‖((y.untilt : 𝓞_ℂ_[p]) : ℂ_[p])‖ = ‖((y.untiltRoot 1 : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ p := by
    rw [← PreTilt.untiltRoot_pow y 1, pow_one]; push_cast; rw [norm_pow]
  rw [map_pow]
  push_cast
  rw [norm_pow, hy, ← pow_mul]
  calc ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := hr
    _ ≤ _ := pow_le_pow_left₀ (le_trans (norm_nonneg _) hrp.le) hroot _

/-- `(ε^{1/p} - 1) ^ (p - 1)` divides `p♭` in the tilt. -/
private theorem eps1_sub_one_pow_dvd_pFlat : (eps1 p - 1) ^ (p - 1) ∣ pFlat p := by
  apply dvd_of_norm_le
  · intro h0
    have := norm_untilt_pow_ge p
    rw [h0, norm_zero] at this
    linarith [PadicComplex.norm_p_pos p]
  · rw [untilt_pFlat]
    exact norm_untilt_pow_ge p

/-- Fontaine's element `ω = Σ_{i < p} [ε^{1/p}]^i` of `W(𝓞_ℂ_[p]♭)`. -/
private def omegaEps : 𝔸 :=
  ∑ i ∈ Finset.range p, teichmuller p (eps1 p) ^ i

private theorem fontaineTheta_omegaEps : fontaineTheta 𝓞_ℂ_[p] p (omegaEps p) = 0 := by
  rw [omegaEps, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller, untilt_eps1]
  exact sum_zetaPowInt_one_eq_zero p

/-- The kernel of `θ : W(𝓞_ℂ_[p]♭) → 𝓞_ℂ_[p]` is generated by `ω`. -/
private theorem ker_fontaineTheta_eq_span_omegaEps :
    RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {omegaEps p} := by
  apply RingHom.ker_eq_span_singleton_of_isAdicComplete p (fontaineTheta 𝓞_ℂ_[p] p)
    (fun b hb => (mul_eq_zero.mp hb).resolve_left (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    (omegaEps p) (fontaineTheta_omegaEps p)
  intro x hx
  have hx' : x ∈ span {xi p} := by
    rw [← ker_fontaineTheta_eq_span_xi]
    exact hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨d, hd⟩ := eps1_sub_one_pow_dvd_pFlat p
  have hmem : teichmuller p ((eps1 p - 1) ^ (p - 1)) - omegaEps p ∈ span {(p : 𝔸)} := by
    have hc : ∀ e : PreTilt 𝓞_ℂ_[p] p, constantCoeff (teichmuller p e) = e := fun e => by simp
    rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, omegaEps, map_sum, hc]
    simp only [map_pow, hc]
    rw [geom_sum_eq_sub_one_pow p (eps1 p) (eps1_sub_one_ne_zero p), sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨-(y * teichmuller p d), y - y * w * teichmuller p d, ?_⟩
  rw [xi, hd, map_mul]
  linear_combination (y * teichmuller p d) * hw

/-! ### `[ε] - 1` is a uniformizer of `B_dR^+` -/

private theorem teichmuller_epsilon_sub_one_eq :
    teichmuller p (epsilon p) - 1 = omegaEps p * (teichmuller p (eps1 p) - 1) := by
  rw [← eps1_pow p, map_pow, omegaEps, geom_sum_mul]

private theorem isUnit_algebraMap_teichmuller_eps1_sub_one :
    IsUnit (algebraMap 𝔸 𝔹⁺ (teichmuller p (eps1 p) - 1)) := by
  apply isUnit_of_fontaineThetaBDeRhamPlus_ne_zero
  rw [fontaineThetaBDeRhamPlus_algebraMap_wittVector, map_sub, fontaineTheta_teichmuller,
    untilt_eps1, map_one]
  exact_mod_cast sub_ne_zero.mpr (zetaPowInt_one_ne_one p)

/-- **`[ε] - 1` is a uniformizer of `B_dR^+`.** -/
theorem irreducible_algebraMap_teichmuller_epsilon_sub_one :
    Irreducible (algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1)) := by
  have h := congrArg (Ideal.map (algebraMap 𝔸 𝔹⁺))
    ((ker_fontaineTheta_eq_span_xi p).symm.trans (ker_fontaineTheta_eq_span_omegaEps p))
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, maximalIdeal_bDeRhamPlus, h,
    teichmuller_epsilon_sub_one_eq, map_mul,
    Ideal.span_singleton_mul_right_unit (isUnit_algebraMap_teichmuller_eps1_sub_one p)]

/-! ### The Galois action on `ε` -/

/-- The reduction modulo `p ^ m` of the cyclotomic character of `σ`, as a natural number `a`: so
`σ ζ = ζ ^ a` for every `p ^ m`-th root of unity `ζ`. -/
private def aexp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) : ℕ :=
  (PadicInt.toZModPow m
    ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val

private theorem completionGalois_zetaPow (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) :
    completionGalois p σ ((zetaPow p m : PadicAlgCl p) : ℂ_[p]) =
      ((zetaPow p m : PadicAlgCl p) : ℂ_[p]) ^ aexp p σ m := by
  rw [PadicComplex.coe_eq, completionGalois_coe, ← map_pow]
  exact congrArg _ (cyclotomicCharacter.spec p σ.toRingEquiv (zetaPow p m) (zetaPow_pow p m))

private theorem coe_zetaPow_ne_zero (n : ℕ) : ((zetaPow p n : PadicAlgCl p) : ℂ_[p]) ≠ 0 := by
  intro h
  have := norm_zetaPow p n
  rw [h, norm_zero] at this
  exact zero_ne_one this

private theorem zetaPow_pow_add (n m : ℕ) : zetaPow p (n + m) ^ p ^ m = zetaPow p n := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, pow_succ', pow_mul, zetaPow_succ_pow, ih]

private theorem coe_zetaPow_pow (k N : ℕ) :
    ((zetaPow p k : PadicAlgCl p) : ℂ_[p]) ^ N = ((zetaPow p k ^ N : PadicAlgCl p) : ℂ_[p]) := by
  rw [PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]

/-- The components `σ(ζ_{p^{n+m}}) ζ_{p^{n+m}}^{-a}` of `ρ = (σ(ε) ε^{-a})^{1/p^m}`, in `ℂ_[p]`. -/
private def rhoC (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m n : ℕ) : ℂ_[p] :=
  completionGalois p σ ((zetaPow p (n + m) : PadicAlgCl p) : ℂ_[p]) *
    ((zetaPow p (n + m) : PadicAlgCl p) : ℂ_[p])⁻¹ ^ aexp p σ m

private theorem norm_rhoC (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m n : ℕ) :
    ‖rhoC p σ m n‖ = 1 := by
  rw [rhoC, norm_mul, norm_pow, norm_inv, PadicComplex.norm_completionGalois, norm_zetaPow]
  simp

/-- The components of `ρ`, in `𝓞_ℂ_[p]`. -/
private def rhoO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m n : ℕ) : 𝓞_ℂ_[p] :=
  ⟨rhoC p σ m n, (mem_iff_norm_le_one p _).mpr (norm_rhoC p σ m n).le⟩

private theorem rhoC_pow (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m n N k : ℕ)
    (hk : zetaPow p (n + m) ^ N = zetaPow p k) :
    rhoC p σ m n ^ N = completionGalois p σ ((zetaPow p k : PadicAlgCl p) : ℂ_[p]) *
      ((zetaPow p k : PadicAlgCl p) : ℂ_[p])⁻¹ ^ aexp p σ m := by
  rw [rhoC, mul_pow, ← pow_mul, mul_comm (aexp p σ m) N, pow_mul, inv_pow _ N, ← map_pow,
    coe_zetaPow_pow, hk]

private theorem rhoO_succ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m n : ℕ) :
    rhoO p σ m (n + 1) ^ p = rhoO p σ m n := by
  apply Subtype.ext
  change rhoC p σ m (n + 1) ^ p = rhoC p σ m n
  rw [rhoC_pow p σ m (n + 1) p (n + m)
    (by rw [Nat.add_right_comm]; exact zetaPow_succ_pow p (n + m))]
  rfl

/-- `ρ = (σ(ε) ε^{-a})^{1/p^m}`, an element of the tilt with `ρ♯ = 1`. -/
private def rho (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) : PreTilt 𝓞_ℂ_[p] p :=
  mkSeq p (rhoO p σ m) (rhoO_succ p σ m)

private theorem untilt_rho (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) :
    (rho p σ m).untilt = 1 := by
  rw [rho, untilt_mkSeq]
  apply Subtype.ext
  change rhoC p σ m 0 = 1
  rw [rhoC, zero_add, completionGalois_zetaPow, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero _ (coe_zetaPow_ne_zero p m))]

/-- **`σ(ε) = ε^a ρ^{p^m}`** in the tilt. -/
private theorem preTiltMap_epsilon (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) :
    PreTilt.map p (integralGalois p σ).toRingHom (epsilon p) =
      epsilon p ^ aexp p σ m * rho p σ m ^ p ^ m := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (PreTilt.map p (integralGalois p σ).toRingHom (epsilon p)) =
    PreTilt.coeff n (epsilon p ^ aexp p σ m * rho p σ m ^ p ^ m)
  rw [PreTilt.coeff_map, map_mul, map_pow, map_pow, epsilon_eq_mkSeq, rho, coeff_mkSeq,
    coeff_mkSeq, ModP.map_mk, ← map_pow, ← map_pow, ← map_mul]
  congr 1
  apply Subtype.ext
  change completionGalois p σ ((zetaPow p n : PadicAlgCl p) : ℂ_[p]) =
    ((zetaPow p n : PadicAlgCl p) : ℂ_[p]) ^ aexp p σ m * rhoC p σ m n ^ p ^ m
  rw [rhoC_pow p σ m n (p ^ m) n (zetaPow_pow_add p n m), inv_pow, mul_left_comm,
    mul_inv_cancel₀ (pow_ne_zero _ (coe_zetaPow_ne_zero p n)), mul_one]

/-! ### The Galois action on `[ε] - 1` -/

/-- For `ρ` in the tilt with `ρ♯ = 1`, `[ρ] - 1 = ([ε] - 1) r` in `B_dR^+` with
`‖θ(r)‖ ≤ ‖ζ_p - 1‖⁻¹`, a bound independent of `ρ`. -/
private theorem exists_algebraMap_teichmuller_sub_one_eq (ρ : PreTilt 𝓞_ℂ_[p] p)
    (hρ : ρ.untilt = 1) :
    ∃ r : 𝔹⁺, algebraMap 𝔸 𝔹⁺ (teichmuller p ρ - 1) =
        algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1) * r ∧
      ‖fontaineThetaBDeRhamPlus p r‖ ≤ ‖((zetaPowInt p 1 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1‖⁻¹ := by
  have hk : teichmuller p ρ - 1 ∈ RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, map_sub, fontaineTheta_teichmuller, hρ, map_one, sub_self]
  rw [ker_fontaineTheta_eq_span_omegaEps] at hk
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.mp hk
  obtain ⟨u, hu⟩ := isUnit_algebraMap_teichmuller_eps1_sub_one p
  refine ⟨algebraMap 𝔸 𝔹⁺ r' * ↑u⁻¹, ?_, ?_⟩
  · rw [← hr', teichmuller_epsilon_sub_one_eq, map_mul, map_mul, ← hu]
    linear_combination -(algebraMap 𝔸 𝔹⁺ r' * algebraMap 𝔸 𝔹⁺ (omegaEps p)) * u.mul_inv
  · rw [map_mul, norm_mul, map_units_inv, norm_inv, hu,
      fontaineThetaBDeRhamPlus_algebraMap_wittVector,
      fontaineThetaBDeRhamPlus_algebraMap_wittVector, map_sub, fontaineTheta_teichmuller,
      untilt_eps1, map_one]
    push_cast
    exact mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (norm_le_one p _)

private theorem fontaineThetaBDeRhamPlus_geom_sum (x : 𝔹⁺)
    (hx : fontaineThetaBDeRhamPlus p x = 1) (n : ℕ) :
    fontaineThetaBDeRhamPlus p (∑ i ∈ Finset.range n, x ^ i) = n := by
  rw [map_sum]
  simp only [map_pow, hx, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- For every `m`, `σ([ε] - 1) = ([ε] - 1) w` with `‖θ(w) - a‖ ≤ ‖ζ_p - 1‖⁻¹ ‖p‖ ^ m`, where `a`
is the cyclotomic character of `σ` modulo `p ^ m`. -/
private theorem exists_galoisBDeRhamPlus_approx (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (m : ℕ) :
    ∃ w : 𝔹⁺, galoisBDeRhamPlus p σ (algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1)) =
        algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1) * w ∧
      ‖fontaineThetaBDeRhamPlus p w - (aexp p σ m : ℂ_[p])‖ ≤
        ‖((zetaPowInt p 1 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1‖⁻¹ * ‖(p : ℂ_[p])‖ ^ m := by
  obtain ⟨r, hr, hrb⟩ :=
    exists_algebraMap_teichmuller_sub_one_eq p (rho p σ m) (untilt_rho p σ m)
  set T := algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1) with hT
  set a := aexp p σ m
  set N := p ^ m
  set E := algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p)) with hE_def
  set R := algebraMap 𝔸 𝔹⁺ (teichmuller p (rho p σ m)) with hR_def
  have hE : E - 1 = T := by rw [hT, map_sub, map_one]
  have hR : R - 1 = T * r := by rw [← hr, map_sub, map_one]
  have hθE : fontaineThetaBDeRhamPlus p E = 1 := by
    rw [hE_def, fontaineThetaBDeRhamPlus_algebraMap_wittVector, fontaineTheta_teichmuller,
      untilt_epsilon]
    rfl
  have hθR : fontaineThetaBDeRhamPlus p R = 1 := by
    rw [hR_def, fontaineThetaBDeRhamPlus_algebraMap_wittVector, fontaineTheta_teichmuller,
      untilt_rho]
    rfl
  have hσT : galoisBDeRhamPlus p σ T = E ^ a * R ^ N - 1 := by
    rw [hT, galoisBDeRhamPlus_algebraMap_wittVector, map_sub, map_one, map_teichmuller,
      preTiltMap_epsilon p σ m, map_mul, map_pow, map_pow, map_sub, map_one, map_mul, map_pow,
      map_pow]
  refine ⟨(∑ i ∈ Finset.range a, E ^ i) * R ^ N + r * ∑ i ∈ Finset.range N, R ^ i, ?_, ?_⟩
  · rw [hσT]
    have h1 : E ^ a - 1 = (∑ i ∈ Finset.range a, E ^ i) * T := by rw [← hE, geom_sum_mul]
    have h2 : R ^ N - 1 = (∑ i ∈ Finset.range N, R ^ i) * (T * r) := by
      rw [← hR, geom_sum_mul]
    linear_combination R ^ N * h1 + h2
  · rw [map_add, map_mul, map_mul, map_pow, hθR, one_pow, mul_one,
      fontaineThetaBDeRhamPlus_geom_sum p E hθE, fontaineThetaBDeRhamPlus_geom_sum p R hθR,
      add_sub_cancel_left, norm_mul]
    have : ((N : ℕ) : ℂ_[p]) = (p : ℂ_[p]) ^ m := by simp [N]
    rw [this, norm_pow]
    exact mul_le_mul_of_nonneg_right hrb (pow_nonneg (norm_nonneg _) m)

/-- `‖a - χ(σ)‖ ≤ ‖p‖ ^ m`, where `a` is the cyclotomic character `χ(σ)` modulo `p ^ m`. -/
private theorem norm_aexp_sub_le (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : ℕ) :
    ‖(aexp p σ m : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ)‖ ≤
      ‖(p : ℂ_[p])‖ ^ m := by
  set χ : ℤ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])
  have hk : ((aexp p σ m : ℕ) : ℤ_[p]) - χ ∈ RingHom.ker (PadicInt.toZModPow (p := p) m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, aexp, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow] at hk
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hk
  let ι : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have h : (aexp p σ m : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) =
      ι y * (p : ℂ_[p]) ^ m := by
    change (aexp p σ m : ℂ_[p]) - ι χ = _
    rw [← map_natCast ι, ← map_sub, ← hy, map_mul, map_pow, map_natCast]
  rw [h, norm_mul, norm_pow]
  refine mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) ?_
  change ‖algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] y)‖ ≤ 1
  rw [norm_algebraMap']
  exact PadicInt.norm_le_one y

private theorem eq_zero_of_norm_le_pow {D : ℂ_[p]} {K : ℝ}
    (h : ∀ m : ℕ, ‖D‖ ≤ K * ‖(p : ℂ_[p])‖ ^ m) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have hK : 0 < K := by
    have := h 0
    rw [pow_zero, mul_one] at this
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hpos hK) (PadicComplex.norm_p_lt_one p)
  rw [lt_div_iff₀ hK] at hm
  linarith [h m, mul_comm K (‖(p : ℂ_[p])‖ ^ m)]

/-- **The Galois action on `[ε] - 1`**: for `σ ∈ Gal(ℚ̄_p/ℚ_p)`, `σ([ε] - 1) = ([ε] - 1) · w` for
some `w ∈ B_dR^+` with `θ(w) = χ(σ)`, the image in `ℂ_[p]` of the `p`-adic cyclotomic character of
`σ` (`cyclotomicScalar p σ`). -/
theorem exists_galoisBDeRhamPlus_algebraMap_teichmuller_epsilon_sub_one
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ w : 𝔹⁺, galoisBDeRhamPlus p σ (algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1)) =
        algebraMap 𝔸 𝔹⁺ (teichmuller p (epsilon p) - 1) * w ∧
      fontaineThetaBDeRhamPlus p w = algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ) := by
  obtain ⟨w, hw, -⟩ := exists_galoisBDeRhamPlus_approx p σ 0
  refine ⟨w, hw, ?_⟩
  set C := ‖((zetaPowInt p 1 : 𝓞_ℂ_[p]) : ℂ_[p]) - 1‖⁻¹
  rw [← sub_eq_zero]
  refine eq_zero_of_norm_le_pow p (K := C + 1) fun m => ?_
  obtain ⟨w', hw', hb⟩ := exists_galoisBDeRhamPlus_approx p σ m
  have hww : w' = w := mul_left_cancel₀
    (irreducible_algebraMap_teichmuller_epsilon_sub_one p).ne_zero (hw'.symm.trans hw)
  rw [hww] at hb
  calc ‖fontaineThetaBDeRhamPlus p w - algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ)‖
      = ‖(fontaineThetaBDeRhamPlus p w - (aexp p σ m : ℂ_[p])) +
          ((aexp p σ m : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖fontaineThetaBDeRhamPlus p w - (aexp p σ m : ℂ_[p])‖ +
          ‖(aexp p σ m : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (cyclotomicScalar p σ)‖ :=
        norm_add_le _ _
    _ ≤ C * ‖(p : ℂ_[p])‖ ^ m + ‖(p : ℂ_[p])‖ ^ m := add_le_add hb (norm_aexp_sub_le p σ m)
    _ = (C + 1) * ‖(p : ℂ_[p])‖ ^ m := by ring

end PadicComplexInt
