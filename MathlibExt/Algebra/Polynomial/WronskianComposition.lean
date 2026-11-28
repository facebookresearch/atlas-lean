/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero.lean`
and
`P2M/Sol/S_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero.lean`
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

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Wronskian

@[expose] public section

namespace Polynomial
namespace SepComp

variable {k : Type*} [Field k]

private noncomputable def hom (m : ℕ) (u v s : k[X]) : k[X] :=
  ∑ i ∈ Finset.range (m + 1), C (s.coeff i) * u ^ i * v ^ (m - i)

private theorem eval_hom {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x x' : k}
    (hx : x' * v.eval x = u.eval x) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval x' := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hs), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← hx, mul_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  ring

private theorem eval_hom_div {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x : k}
    (hv : v.eval x ≠ 0) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval (u.eval x / v.eval x) :=
  eval_hom hs (div_mul_cancel₀ _ hv)

private theorem eval_hom_of_root {m : ℕ} {u v : k[X]} (s : k[X]) {x : k} (hx : v.eval x = 0) :
    (hom m u v s).eval x = s.coeff m * (u.eval x) ^ m := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C, hx]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i hi him
    rw [Finset.mem_range] at hi
    rw [zero_pow (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) him)), mul_zero]
  · intro h; exact absurd (Finset.self_mem_range_succ m) h

private theorem natDegree_hom_le (m : ℕ) (u v s : k[X]) :
    (hom m u v s).natDegree ≤ m * max u.natDegree v.natDegree := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  calc (C (s.coeff i) * u ^ i * v ^ (m - i)).natDegree
      ≤ (C (s.coeff i) * u ^ i).natDegree + (v ^ (m - i)).natDegree := natDegree_mul_le
    _ ≤ i * u.natDegree + (m - i) * v.natDegree :=
        add_le_add ((natDegree_C_mul_le _ _).trans natDegree_pow_le) natDegree_pow_le
    _ ≤ i * max u.natDegree v.natDegree + (m - i) * max u.natDegree v.natDegree :=
        add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _))
          (Nat.mul_le_mul_left _ (le_max_right _ _))
    _ = m * max u.natDegree v.natDegree := by
        rw [← add_mul, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]

private theorem ne_zero_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.mp huv)
    simp [this] at h
  · rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp huv)
    simp [this] at h

private theorem ne_C_mul_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) (c : k) : u ≠ C c * v := by
  intro huc
  have hvu : v ∣ u := ⟨C c, by rw [huc, mul_comm]⟩
  have hunit : IsUnit v := huv.isUnit_of_dvd' hvu (dvd_refl v)
  have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  have hu0 : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [huc]; exact (natDegree_C_mul_le _ _).trans_eq hv0
  omega

private theorem eval_ne_zero_of_isCoprime {u v : k[X]} (huv : IsCoprime u v) {x : k}
    (hv : v.eval x = 0) :
    u.eval x ≠ 0 := by
  intro hu
  obtain ⟨a, b, hab⟩ := huv
  have := congr_arg (eval x) hab
  simp [hu, hv] at this

private theorem eq_of_eval_eq_off_finite [Infinite k] {f g : k[X]} {S : Set k} (hS : S.Finite)
    (h : ∀ x, x ∉ S → f.eval x = g.eval x) : f = g := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Sᶜ)
  · intro x hx; exact h x hx
  · exact hS.infinite_compl

section Fibre

variable [DecidableEq k]

private noncomputable def fib (f g : k[X]) (c : k) : Finset k := (f - C c * g).roots.toFinset

private theorem mem_fib {f g : k[X]} {c x : k} (h : f - C c * g ≠ 0) :
    x ∈ fib f g c ↔ f.eval x = c * g.eval x := by
  rw [fib, Multiset.mem_toFinset, mem_roots h, IsRoot.def, eval_sub, eval_mul, eval_C, sub_eq_zero]

private theorem eval_eq_of_mem_fib {f g : k[X]} {c x : k} (hx : x ∈ fib f g c) :
    f.eval x = c * g.eval x := by
  by_cases h : f - C c * g = 0
  · simp [fib, h] at hx
  · exact (mem_fib h).mp hx

private theorem card_fib_le (f g : k[X]) (c : k) : (fib f g c).card ≤ (f - C c * g).natDegree :=
  (Multiset.toFinset_card_le _).trans (card_roots' _)

private theorem natDegree_sub_C_mul_le (f g : k[X]) (c : k) :
    (f - C c * g).natDegree ≤ max f.natDegree g.natDegree :=
  (natDegree_sub_le _ _).trans (max_le_max le_rfl (natDegree_C_mul_le _ _))

private theorem natDegree_sub_C_mul_eq {f g : k[X]} (hg : g ≠ 0) {c : k} (hc : c ≠ 0)
    (hc' : c ≠ f.leadingCoeff / g.leadingCoeff) :
    (f - C c * g).natDegree = max f.natDegree g.natDegree := by
  have hlead : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
  have hcg : (C c * g).natDegree = g.natDegree := natDegree_C_mul hc
  rcases lt_trichotomy f.natDegree g.natDegree with hlt | heq | hgt
  · rw [max_eq_right hlt.le, natDegree_sub_eq_right_of_natDegree_lt (by rwa [hcg]), hcg]
  · apply le_antisymm (natDegree_sub_C_mul_le f g c)
    rw [heq, max_self]
    apply le_natDegree_of_ne_zero
    rw [coeff_sub, coeff_C_mul, ← heq, coeff_natDegree, heq, coeff_natDegree]
    intro h0
    apply hc'
    rw [eq_div_iff hlead]
    exact (sub_eq_zero.mp h0).symm
  · rw [max_eq_left hgt.le, natDegree_sub_eq_left_of_natDegree_lt (by rwa [hcg])]

variable [IsAlgClosed k]

private theorem exists_card_fib_eq {f g : k[X]} (hfg : IsCoprime f g)
    (hpos : 0 < max f.natDegree g.natDegree)
    (hw : wronskian f g ≠ 0) :
    ∃ S : Finset k, ∀ c, c ∉ S → (fib f g c).card = max f.natDegree g.natDegree := by
  obtain ⟨hf0, hg0⟩ := ne_zero_of_isCoprime_of_pos hfg hpos
  refine ⟨insert 0 (insert (f.leadingCoeff / g.leadingCoeff)
    ((wronskian f g).roots.toFinset.image fun a => f.eval a / g.eval a)), fun c hc => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_image, Multiset.mem_toFinset, not_or, not_exists,
    not_and] at hc
  obtain ⟨hc0, hc1, hc2⟩ := hc
  have hdeg : (f - C c * g).natDegree = max f.natDegree g.natDegree :=
    natDegree_sub_C_mul_eq hg0 hc0 hc1
  have hsep : (f - C c * g).Separable := by
    rw [separable_def, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) (K := k)]
    intro a
    by_contra hcon
    simp only [not_or, not_not, coe_aeval_eq_eval, derivative_sub, derivative_mul, derivative_C,
      zero_mul, zero_add, eval_sub, eval_mul, eval_C, sub_eq_zero] at hcon
    obtain ⟨e1, e2⟩ := hcon
    have hwa : (wronskian f g).eval a = 0 := by
      simp only [wronskian, eval_sub, eval_mul, e1, e2]; ring
    by_cases hga : g.eval a = 0
    · exact eval_ne_zero_of_isCoprime hfg hga (by rw [e1, hga, mul_zero])
    · exact hc2 a ((mem_roots hw).mpr hwa) (by rw [e1, mul_div_cancel_right₀ _ hga])
  rw [fib, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
    ← (IsAlgClosed.splits (f - C c * g)).natDegree_eq_card_roots, hdeg]

private theorem card_fib_expand_le (p : ℕ) [Fact p.Prime] [CharP k p] (f g : k[X]) (c : k) :
    (fib (expand k p f) (expand k p g) c).card ≤ (f - C c * g).natDegree := by
  have he : expand k p f - C c * expand k p g = expand k p (f - C c * g) := by
    rw [map_sub, map_mul, expand_C]
  by_cases h0 : f - C c * g = 0
  · rw [fib, he, h0, map_zero, roots_zero]; simp
  have hne : expand k p (f - C c * g) ≠ 0 := by
    rwa [Ne, ← map_zero (expand k p), (expand_injective (Fact.out : p.Prime).pos).eq_iff]
  calc (fib (expand k p f) (expand k p g) c).card
      ≤ (f - C c * g).roots.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun x => x ^ p) ?_ ?_
        · intro x hx
          rw [Finset.mem_coe, fib, he, Multiset.mem_toFinset, mem_roots hne, IsRoot.def,
            expand_eval] at hx
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots h0]
          exact hx
        · intro x _ y _ hxy
          exact frobenius_inj k p hxy
    _ ≤ (f - C c * g).natDegree := (Multiset.toFinset_card_le _).trans (card_roots' _)

end Fibre

section Main

variable [DecidableEq k] [IsAlgClosed k]

variable {u v s t U V : k[X]} (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree)
  (hw : wronskian u v ≠ 0) (hst : IsCoprime s t) (hs : 0 < max s.natDegree t.natDegree)
  (hw' : wronskian s t ≠ 0)
  (hU : ∀ x : k, v.eval x ≠ 0 →
    U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x))
  (hV : ∀ x : k, v.eval x ≠ 0 →
    V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x))

include huv hu hU in
private theorem U_eq : U = hom (max s.natDegree t.natDegree) u v s := by
  refine eq_of_eval_eq_off_finite (finite_setOf_isRoot (ne_zero_of_isCoprime_of_pos huv hu).2)
    fun x hx => ?_
  simp only [Set.mem_setOf_eq, IsRoot.def] at hx
  rw [hU x hx, eval_hom_div (le_max_left _ _) hx]

include huv hu hV in
private theorem V_eq : V = hom (max s.natDegree t.natDegree) u v t := by
  refine eq_of_eval_eq_off_finite (finite_setOf_isRoot (ne_zero_of_isCoprime_of_pos huv hu).2)
    fun x hx => ?_
  simp only [Set.mem_setOf_eq, IsRoot.def] at hx
  rw [hV x hx, eval_hom_div (le_max_right _ _) hx]

include huv hu hst hs hU hV in

private theorem isCoprime_UV : IsCoprime U V := by
  obtain ⟨hs0, ht0⟩ := ne_zero_of_isCoprime_of_pos hst hs
  rw [U_eq huv hu hU, V_eq huv hu hV,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) (K := k)]
  intro x
  simp only [coe_aeval_eq_eval]
  by_cases hvx : v.eval x = 0
  · have hux : u.eval x ≠ 0 := eval_ne_zero_of_isCoprime huv hvx
    rw [eval_hom_of_root s hvx, eval_hom_of_root t hvx]

    rcases le_total t.natDegree s.natDegree with hle | hle
    · left
      rw [show max s.natDegree t.natDegree = s.natDegree from max_eq_left hle, coeff_natDegree]
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr hs0) (pow_ne_zero _ hux)
    · right
      rw [show max s.natDegree t.natDegree = t.natDegree from max_eq_right hle, coeff_natDegree]
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr ht0) (pow_ne_zero _ hux)
  · rw [eval_hom_div (le_max_left _ _) hvx, eval_hom_div (le_max_right _ _) hvx]
    have := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := k) (K := k) s t).mp
      hst (u.eval x / v.eval x)
    simp only [coe_aeval_eq_eval] at this
    exact this.imp (fun h => mul_ne_zero (pow_ne_zero _ hvx) h)
      (fun h => mul_ne_zero (pow_ne_zero _ hvx) h)

include huv hu hw hst hs hU hV in

private theorem U_ne_C_mul_V (c : k) : U ≠ C c * V := by
  intro hUV
  obtain ⟨S, hS⟩ := exists_card_fib_eq huv hu hw
  apply ne_C_mul_of_isCoprime_of_pos hst hs c
  refine eq_of_eval_eq_off_finite (S := (S : Set k)) S.finite_toSet fun w hw0 => ?_
  have hcard := hS w hw0
  have hne : (fib u v w).Nonempty := by
    rw [← Finset.card_pos, hcard]; exact hu
  obtain ⟨x, hx⟩ := hne
  have hux : u.eval x = w * v.eval x := eval_eq_of_mem_fib hx
  have hvx : v.eval x ≠ 0 := fun h0 => eval_ne_zero_of_isCoprime huv h0 (by rw [hux, h0, mul_zero])
  have hw' : u.eval x / v.eval x = w := by rw [hux, mul_div_cancel_right₀ _ hvx]
  have e1 := hU x hvx
  have e2 := hV x hvx
  rw [hw'] at e1 e2
  have : U.eval x = c * V.eval x := by rw [hUV, eval_mul, eval_C]
  rw [e1, e2] at this
  rw [eval_mul, eval_C]
  have hvm : v.eval x ^ max s.natDegree t.natDegree ≠ 0 := pow_ne_zero _ hvx
  apply mul_left_cancel₀ hvm
  rw [this]; ring

include huv hu hw hst hs hw' hU hV in
private theorem exists_large_fibre :
    ∃ c : k, max s.natDegree t.natDegree * max u.natDegree v.natDegree ≤ (fib U V c).card := by
  obtain ⟨Suv, hSuv⟩ := exists_card_fib_eq huv hu hw
  obtain ⟨Sst, hSst⟩ := exists_card_fib_eq hst hs hw'
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (Sst ∪ Suv.image fun w => s.eval w / t.eval w)
  simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hc
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨c, ?_⟩
  have hUVne : U - C c * V ≠ 0 := sub_ne_zero.mpr (U_ne_C_mul_V huv hu hw hst hs hU hV c)
  have hsub : (fib s t c).biUnion (fun w => fib u v w) ⊆ fib U V c := by
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨w, hw1, hx⟩ := hx
    have hsw : s.eval w = c * t.eval w := eval_eq_of_mem_fib hw1
    have hux : u.eval x = w * v.eval x := eval_eq_of_mem_fib hx
    have hvx : v.eval x ≠ 0 := fun h0 =>
      eval_ne_zero_of_isCoprime huv h0 (by rw [hux, h0, mul_zero])
    have hw2 : u.eval x / v.eval x = w := by rw [hux, mul_div_cancel_right₀ _ hvx]
    rw [mem_fib hUVne, hU x hvx, hV x hvx, hw2, hsw]
    ring
  have hdisj : ((fib s t c : Finset k) : Set k).PairwiseDisjoint fun w => fib u v w := by
    intro w₁ _ w₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    have e₁ : u.eval x = w₁ * v.eval x := eval_eq_of_mem_fib hx₁
    have e₂ : u.eval x = w₂ * v.eval x := eval_eq_of_mem_fib hx₂
    have hvx : v.eval x ≠ 0 := fun h0 =>
      eval_ne_zero_of_isCoprime huv h0 (by rw [e₁, h0, mul_zero])
    exact mul_right_cancel₀ hvx (e₁.symm.trans e₂)
  calc max s.natDegree t.natDegree * max u.natDegree v.natDegree
      = ∑ w ∈ fib s t c, (fib u v w).card := by
        rw [Finset.sum_const_nat (m := max u.natDegree v.natDegree) fun w hw1 => ?_, hSst c hc1]
        apply hSuv
        intro hmem
        have hsw : s.eval w = c * t.eval w := eval_eq_of_mem_fib hw1
        have htw : t.eval w ≠ 0 := fun h0 =>
          eval_ne_zero_of_isCoprime hst h0 (by rw [hsw, h0, mul_zero])
        exact hc2 w hmem (by rw [hsw, mul_div_cancel_right₀ _ htw])
    _ = ((fib s t c).biUnion fun w => fib u v w).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (fib U V c).card := Finset.card_le_card hsub

include huv hu hw hst hs hw' hU hV in
private theorem main : IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ wronskian U V ≠ 0 := by
  have hcop : IsCoprime U V := isCoprime_UV huv hu hst hs hU hV
  obtain ⟨c₀, hc₀⟩ := exists_large_fibre huv hu hw hst hs hw' hU hV
  have hmd : 0 < max s.natDegree t.natDegree * max u.natDegree v.natDegree := Nat.mul_pos hs hu

  have hdegUV : max U.natDegree V.natDegree ≤
      max s.natDegree t.natDegree * max u.natDegree v.natDegree := by
    rw [U_eq huv hu hU, V_eq huv hu hV]
    exact max_le (natDegree_hom_le _ _ _ _) (natDegree_hom_le _ _ _ _)
  refine ⟨hcop, ?_, ?_⟩
  ·
    by_contra h0
    push Not at h0
    have h1 : (fib U V c₀).card ≤ 0 := by
      refine (card_fib_le U V c₀).trans ((natDegree_sub_C_mul_le U V c₀).trans h0)
    omega
  · intro hW
    obtain ⟨hdU, hdV⟩ := hcop.wronskian_eq_zero_iff.mp hW

    obtain ⟨q, hq⟩ := ExpChar.exists k
    rcases hq with _ | ⟨hprime, _⟩
    ·
      have hU0 : U.natDegree = 0 := derivative_eq_zero.mp hdU
      have hV0 : V.natDegree = 0 := derivative_eq_zero.mp hdV
      have h1 : (fib U V c₀).card ≤ 0 := by
        refine (card_fib_le U V c₀).trans ((natDegree_sub_C_mul_le U V c₀).trans ?_)
        rw [hU0, hV0, max_self]
      omega
    ·
      haveI := Fact.mk hprime
      have hq0 : q ≠ 0 := hprime.ne_zero
      have eU : U = expand k q (contract q U) := (expand_contract q hdU hq0).symm
      have eV : V = expand k q (contract q V) := (expand_contract q hdV hq0).symm
      have h1 : (fib U V c₀).card ≤ max (contract q U).natDegree (contract q V).natDegree := by
        conv_lhs => rw [eU, eV]
        exact (card_fib_expand_le q _ _ c₀).trans (natDegree_sub_C_mul_le _ _ _)
      have h2 : max (contract q U).natDegree (contract q V).natDegree * q =
          max U.natDegree V.natDegree := by
        conv_rhs => rw [eU, eV]
        rw [natDegree_expand, natDegree_expand, Nat.mul_max_mul_right]
      have h3 : max (contract q U).natDegree (contract q V).natDegree * q ≤
          max s.natDegree t.natDegree * max u.natDegree v.natDegree := h2 ▸ hdegUV
      have hq2 : 2 ≤ q := hprime.two_le
      nlinarith

end Main

end SepComp

/-- Composition preserves coprimality and a nonzero Wronskian.

Let `u / v` and `s / t` be rational functions over an algebraically closed
field, given by coprime numerator and denominator pairs of positive maximal
degree and nonzero Wronskian. If `U` and `V` are the cleared numerator and
denominator of the composition, described off the zeros of `v` by the
evaluation identities `hU` and `hV`, then `U` and `V` are again coprime, of
positive maximal degree, and have nonzero Wronskian. -/
public theorem isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
    {k : Type*} [Field k] [IsAlgClosed k] {u v s t U V : Polynomial k}
    (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree)
    (hw : Polynomial.wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : Polynomial.wronskian s t ≠ 0)
    (hU : ∀ x : k, v.eval x ≠ 0 →
      U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x))
    (hV : ∀ x : k, v.eval x ≠ 0 →
      V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x)) :
    IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ Polynomial.wronskian U V ≠ 0 := by
  classical
  exact Polynomial.SepComp.main huv hu hw hst hs hw' hU hV

end Polynomial
