/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial.lean`
and
`P2M/Sol/S_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial.lean`
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

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open Polynomial

noncomputable section

namespace PolynomialExistsMonicResultantAux


section Nev

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra ℚ R] [Algebra ℚ R']

private def Nev {m : ℕ} (N : MvPolynomial (Fin m) ℚ) (G : R[X]) : R :=
  MvPolynomial.aeval (fun i : Fin m => G.coeff (i : ℕ)) N

private theorem Nev_rat {m : ℕ} (N : MvPolynomial (Fin m) ℚ) (G : ℚ[X]) :
    Nev N G = MvPolynomial.eval (fun i : Fin m => G.coeff (i : ℕ)) N := rfl

private theorem Nev_map_int {m : ℕ} (N : MvPolynomial (Fin m) ℚ) (G : ℤ[X]) :
    Nev N (G.map (Int.castRingHom ℚ)) = MvPolynomial.eval (fun i : Fin m => ((G.coeff (i : ℕ) : ℤ)
      : ℚ)) N := by
  rw [Nev_rat]
  congr 2
  funext i
  rw [coeff_map]
  rfl

@[simp] private theorem Nev_one {m : ℕ} (G : R[X]) : Nev (1 : MvPolynomial (Fin m) ℚ) G = 1 := by
  simp [Nev]

private theorem map_Nev {m : ℕ} (N : MvPolynomial (Fin m) ℚ) (G : R[X]) (j : R →ₐ[ℚ] R') :
    j (Nev N G) = Nev N (G.map (j : R →+* R')) := by
  unfold Nev
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  simp [Polynomial.coeff_map]

end Nev

section PolyP

private def Pof (N₁ : MvPolynomial (Fin 1) ℚ) : ℚ[X] :=
  MvPolynomial.aeval (fun _ : Fin 1 => -(X : ℚ[X])) N₁

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem coeff_vec_X_sub_C (c : R) :
    (fun i : Fin 1 => (X - C c).coeff (i : ℕ)) = fun _ => -c := by
  funext i
  fin_cases i
  simp [coeff_X]

private theorem eval_map_Pof (N₁ : MvPolynomial (Fin 1) ℚ) (c : R) :
    ((Pof N₁).map (algebraMap ℚ R)).eval c = Nev N₁ (X - C c) := by
  unfold Pof Nev
  rw [coeff_vec_X_sub_C]
  have key : ((evalRingHom c).comp (mapRingHom (algebraMap ℚ R))).comp
      (MvPolynomial.aeval fun _ : Fin 1 => -(X : ℚ[X])).toRingHom =
      (MvPolynomial.aeval (R := ℚ) (fun _ : Fin 1 => -c)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.aeval_C,
        Polynomial.algebraMap_eq, coe_mapRingHom, Polynomial.map_C, coe_evalRingHom, eval_C]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.aeval_X,
        coe_mapRingHom, Polynomial.map_neg, Polynomial.map_X, coe_evalRingHom, eval_neg, eval_X]
  exact congrArg (fun f : MvPolynomial (Fin 1) ℚ →+* R => f N₁) key

private theorem Pof_eq_sum (N₁ : MvPolynomial (Fin 1) ℚ) :
    Pof N₁ = ∑ d ∈ N₁.support, C (N₁.coeff d) * (-X) ^ (d 0) := by
  unfold Pof
  conv_lhs => rw [MvPolynomial.as_sum N₁]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_one]
  simp

variable {n : ℕ}

private theorem deg_one {N₁ : MvPolynomial (Fin 1) ℚ} (hN : N₁.totalDegree ≤ n)
    {d : Fin 1 →₀ ℕ} (hd : d ∈ N₁.support) : d 0 ≤ n := by
  have h := MvPolynomial.le_totalDegree hd
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_one] at h
  exact h.trans hN

private theorem eq_single_of_apply (d : Fin 1 →₀ ℕ) : d = Finsupp.single 0 (d 0) := by
  refine Finsupp.ext fun i => ?_
  fin_cases i
  simp

private theorem natDegree_Pof_le (N₁ : MvPolynomial (Fin 1) ℚ) (hN : N₁.totalDegree ≤ n) :
    (Pof N₁).natDegree ≤ n := by
  rw [Pof_eq_sum]
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  have hdeg := deg_one hN hd
  calc d 0 * (-X : ℚ[X]).natDegree ≤ d 0 * 1 :=
        Nat.mul_le_mul_left _ (by rw [natDegree_neg, natDegree_X])
    _ ≤ n := by omega

private theorem coeff_Pof_n (N₁ : MvPolynomial (Fin 1) ℚ) (hn : Even n) :
    (Pof N₁).coeff n = N₁.coeff (Finsupp.single 0 n) := by
  classical
  rw [Pof_eq_sum, finsetSum_coeff]
  have hterm : ∀ d ∈ N₁.support, (C (N₁.coeff d) * (-X : ℚ[X]) ^ (d 0)).coeff n =
      if d = Finsupp.single 0 n then N₁.coeff d else 0 := by
    intro d _
    rw [neg_pow, ← mul_assoc, show C (N₁.coeff d) * (-1 : ℚ[X]) ^ (d 0) =
      C (N₁.coeff d * (-1) ^ (d 0)) by simp, coeff_C_mul, coeff_X_pow]
    by_cases h : d = Finsupp.single 0 n
    · subst h
      simp [hn.neg_one_pow]
    · have h0 : n ≠ d 0 := by
        intro h0
        apply h
        rw [eq_single_of_apply d, ← h0]
      rw [ite_eq_right h0, ite_eq_right h, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]

private theorem monic_Pof (N₁ : MvPolynomial (Fin 1) ℚ) (hN : N₁.totalDegree ≤ n) (hn : Even n)
    (h1 : N₁.coeff (Finsupp.single 0 n) = 1) : (Pof N₁).Monic ∧ (Pof N₁).natDegree = n := by
  have hle := natDegree_Pof_le N₁ hN
  have hc : (Pof N₁).coeff n = 1 := by rw [coeff_Pof_n N₁ hn, h1]
  have hdeg : (Pof N₁).natDegree = n :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, hdeg, hc], hdeg⟩

end PolyP

section Universal

variable (b : ℕ)

private def U : (MvPolynomial (Fin (b + 1)) ℚ)[X] := X + C (MvPolynomial.X 0)

private def W : (MvPolynomial (Fin (b + 1)) ℚ)[X] :=
  X ^ b + ∑ j : Fin b, C (MvPolynomial.X j.succ) * X ^ (j : ℕ)

private def Psi (N₁ : MvPolynomial (Fin 1) ℚ) (Nb : MvPolynomial (Fin b) ℚ)
    (Nb1 : MvPolynomial (Fin (b + 1)) ℚ) : MvPolynomial (Fin (b + 1)) ℚ :=
  Nev Nb1 (U b * W b) - Nev N₁ (U b) * Nev Nb (W b)

variable {b}
variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem map_U (j : MvPolynomial (Fin (b + 1)) ℚ →+* R) :
    (U b).map j = X + C (j (MvPolynomial.X 0)) := by
  simp [U]

private theorem map_W (j : MvPolynomial (Fin (b + 1)) ℚ →+* R) :
    (W b).map j = X ^ b + ∑ i : Fin b, C (j (MvPolynomial.X i.succ)) * X ^ (i : ℕ) := by
  simp [W, Polynomial.map_sum]

private theorem monic_genericW {S : Type*} [CommRing S] [Nontrivial S] (c : Fin b → S) :
    (X ^ b + ∑ i : Fin b, C (c i) * X ^ (i : ℕ)).Monic ∧
      (X ^ b + ∑ i : Fin b, C (c i) * X ^ (i : ℕ)).natDegree = b := by
  have hmon : (X ^ b + ∑ i : Fin b, C (c i) * X ^ (i : ℕ)).Monic :=
    monic_X_pow_add (degree_sum_fin_lt c)
  refine ⟨hmon, ?_⟩
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

private theorem coeff_zero_genericW {S : Type*} [CommRing S] (c : Fin b → S) :
    (X ^ b + ∑ i : Fin b, C (c i) * X ^ (i : ℕ)).coeff 0 = 1 ∨
      ∃ i, (X ^ b + ∑ i : Fin b, C (c i) * X ^ (i : ℕ)).coeff 0 = c i := by
  cases b with
  | zero => left; simp
  | succ b =>
    right
    refine ⟨0, ?_⟩
    rw [coeff_add, coeff_X_pow, ite_eq_right (Nat.succ_ne_zero b).symm, zero_add, finsetSum_coeff]
    rw [Finset.sum_eq_single (0 : Fin (b + 1))]
    · simp
    · intro i _ hi
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right, mul_zero]
      intro h
      exact hi (Fin.ext h.symm)
    · intro h; exact (h (Finset.mem_univ _)).elim

private theorem genericW_eq_of_monic {S : Type*} [CommRing S] (H : S[X]) (hH : H.Monic) (hb :
  H.natDegree = b) :
    (X ^ b + ∑ i : Fin b, C (H.coeff i) * X ^ (i : ℕ)) = H := by
  conv_rhs => rw [hH.as_sum, hb]
  rw [Finset.sum_range (fun i => C (H.coeff i) * X ^ i)]

private theorem map_Psi (N₁ : MvPolynomial (Fin 1) ℚ) (Nb : MvPolynomial (Fin b) ℚ)
    (Nb1 : MvPolynomial (Fin (b + 1)) ℚ) (j : MvPolynomial (Fin (b + 1)) ℚ →ₐ[ℚ] R) :
    j (Psi b N₁ Nb Nb1) =
      Nev Nb1 ((U b).map (j : _ →+* R) * (W b).map (j : _ →+* R)) -
        Nev N₁ ((U b).map (j : _ →+* R)) * Nev Nb ((W b).map (j : _ →+* R)) := by
  rw [Psi, map_sub, map_mul, map_Nev, map_Nev, map_Nev, Polynomial.map_mul]

end Universal

section Main

private theorem infinite_S (K : Type*) [Field K] : {c : ℤ | ((c : ℤ) : K) ≠ 0}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  by_cases h : (((a + 1 : ℤ)) : K) ≠ 0
  · exact ⟨a + 1, h, by omega⟩
  · refine ⟨a + 2, ?_, by omega⟩
    rw [not_not] at h
    show ((a + 2 : ℤ) : K) ≠ 0
    have : ((a + 2 : ℤ) : K) = ((a + 1 : ℤ) : K) + 1 := by push_cast; ring
    rw [this, h, zero_add]
    exact one_ne_zero

private theorem infinite_SQ (K : Type*) [Field K] :
    ((fun c : ℤ => (c : ℚ)) '' {c : ℤ | ((c : ℤ) : K) ≠ 0}).Infinite :=
  (infinite_S K).image Int.cast_injective.injOn

variable {K : Type*} [Field K] (D : Polynomial ℤ → ℚ) (n : ℕ) (hn : Even n) (h1 : D 1 = 1)
  (hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
    ((H.coeff 0 : ℤ) : K) ≠ 0 → D (G * H) = D G * D H)
  (hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧
    N.coeff (Finsupp.single 0 n) = 1 ∧
    ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = D G)

private def Nf : (m : ℕ) → MvPolynomial (Fin m) ℚ
  | 0 => 1
  | m + 1 => (hpoly m).choose

private theorem Nf_succ_spec (m : ℕ) :
    (Nf D n hpoly (m + 1)).totalDegree ≤ n ∧
      (Nf D n hpoly (m + 1)).coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = m + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (m + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) (Nf D n hpoly (m +
          1)) = D G :=
  (hpoly m).choose_spec

include h1 in
private theorem Nev_Nf_eq (m : ℕ) (G : ℤ[X]) (hG : G.Monic) (hdeg : G.natDegree = m)
    (hG0 : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    Nev (Nf D n hpoly m) (G.map (Int.castRingHom ℚ)) = D G := by
  cases m with
  | zero =>
    have hG1 : G = 1 := eq_one_of_monic_natDegree_zero hG hdeg
    subst hG1
    rw [h1]
    exact Nev_one _
  | succ m =>
    rw [Nev_map_int]
    exact (Nf_succ_spec D n hpoly m).2.2 G hG hdeg hG0

include h1 hmul in
private theorem Psi_eq_zero (b : ℕ) :
    Psi b (Nf D n hpoly 1) (Nf D n hpoly b) (Nf D n hpoly (b + 1)) = 0 := by
  refine MvPolynomial.funext_set (fun _ => (fun c : ℤ => (c : ℚ)) '' {c : ℤ | ((c : ℤ) : K) ≠ 0})
    (fun _ => infinite_SQ K) (fun x hx => ?_)
  rw [map_zero]
  have hx' : ∀ i, ∃ c : ℤ, ((c : ℤ) : K) ≠ 0 ∧ (c : ℚ) = x i := fun i => by
    obtain ⟨c, hc, hcx⟩ := hx i (Set.mem_univ i)
    exact ⟨c, hc, hcx⟩
  choose c hcK hcx using hx'
  set jA : MvPolynomial (Fin (b + 1)) ℚ →ₐ[ℚ] ℚ := MvPolynomial.aeval x with hjA
  have hjx : ∀ i, jA (MvPolynomial.X i) = (c i : ℚ) := fun i => by
    rw [hjA, MvPolynomial.aeval_X, hcx]
  set G₁ : ℤ[X] := X + C (c 0) with hG₁
  set G₂ : ℤ[X] := X ^ b + ∑ i : Fin b, C (c i.succ) * X ^ (i : ℕ) with hG₂
  have hU : (U b).map (jA : _ →+* ℚ) = G₁.map (Int.castRingHom ℚ) := by
    rw [map_U, hG₁, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
    simp [hjx]
  have hW : (W b).map (jA : _ →+* ℚ) = G₂.map (Int.castRingHom ℚ) := by
    rw [map_W, hG₂, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp [hjx, Polynomial.map_mul]
  have hmon₁ : G₁.Monic := monic_X_add_C (c 0)
  have hdeg₁ : G₁.natDegree = 1 := natDegree_X_add_C _
  have hc₁ : ((G₁.coeff 0 : ℤ) : K) ≠ 0 := by rw [hG₁]; simpa using hcK 0
  have hmon₂ := monic_genericW (fun i : Fin b => c i.succ)
  have hc₂ : ((G₂.coeff 0 : ℤ) : K) ≠ 0 := by
    rcases coeff_zero_genericW (fun i : Fin b => c i.succ) with h | ⟨i, hi⟩
    · rw [hG₂, h, Int.cast_one]; exact one_ne_zero
    · rw [hG₂, hi]; exact hcK _
  have hdeg₁₂ : (G₁ * G₂).natDegree = b + 1 := by
    rw [hmon₁.natDegree_mul hmon₂.1, hdeg₁, hmon₂.2, add_comm]
  have hc₁₂ : (((G₁ * G₂).coeff 0 : ℤ) : K) ≠ 0 := by
    rw [mul_coeff_zero, Int.cast_mul]
    exact mul_ne_zero hc₁ hc₂
  have heval : MvPolynomial.eval x (Psi b (Nf D n hpoly 1) (Nf D n hpoly b) (Nf D n hpoly (b + 1)))
    =
      jA (Psi b (Nf D n hpoly 1) (Nf D n hpoly b) (Nf D n hpoly (b + 1))) := rfl
  rw [heval, map_Psi, hU, hW, ← Polynomial.map_mul,
    Nev_Nf_eq D n h1 hpoly _ _ (hmon₁.mul hmon₂.1) hdeg₁₂ hc₁₂,
    Nev_Nf_eq D n h1 hpoly _ _ hmon₁ hdeg₁ hc₁,
    Nev_Nf_eq D n h1 hpoly _ _ hmon₂.1 hmon₂.2 hc₂,
    hmul G₁ G₂ hmon₁ hmon₂.1 hc₁ hc₂, sub_self]

include h1 hmul in
private theorem Nev_linear_mul (b : ℕ) (γ : ℂ) (H : ℂ[X]) (hH : H.Monic) (hb : H.natDegree = b) :
    Nev (Nf D n hpoly (b + 1)) ((X - C γ) * H) =
      Nev (Nf D n hpoly 1) (X - C γ) * Nev (Nf D n hpoly b) H := by
  set x : Fin (b + 1) → ℂ := Fin.cons (-γ) fun i : Fin b => H.coeff i with hx
  set j : MvPolynomial (Fin (b + 1)) ℚ →ₐ[ℚ] ℂ := MvPolynomial.aeval x
  have h0 := congrArg j (Psi_eq_zero D n h1 hmul hpoly b)
  rw [map_zero, map_Psi, map_U, map_W] at h0
  have hjU : (X + C ((j : MvPolynomial (Fin (b + 1)) ℚ →+* ℂ) (MvPolynomial.X 0)) : ℂ[X]) = X - C γ
    := by
    simp [j, hx, sub_eq_add_neg]
  have hjW : (X ^ b + ∑ i : Fin b, C ((j : MvPolynomial (Fin (b + 1)) ℚ →+* ℂ) (MvPolynomial.X
    i.succ)) *
      X ^ (i : ℕ) : ℂ[X]) = H := by
    have : ∀ i : Fin b, (j : MvPolynomial (Fin (b + 1)) ℚ →+* ℂ) (MvPolynomial.X i.succ) = H.coeff
      i := by
      intro i; simp [j, hx]
    simp_rw [this]
    exact genericW_eq_of_monic H hH hb
  rw [hjU, hjW] at h0
  exact sub_eq_zero.mp h0

private def P : ℚ[X] := Pof (Nf D n hpoly 1)

include hn in
private theorem monic_P : (P D n hpoly).Monic ∧ (P D n hpoly).natDegree = n :=
  monic_Pof _ (Nf_succ_spec D n hpoly 0).1 hn (Nf_succ_spec D n hpoly 0).2.1

include h1 hmul in

private theorem Nev_eq_prod_roots : ∀ (b : ℕ) (H : ℂ[X]), H.Monic → H.natDegree = b →
    Nev (Nf D n hpoly b) H = (H.roots.map ((P D n hpoly).map (algebraMap ℚ ℂ)).eval).prod := by
  intro b
  induction b with
  | zero =>
    intro H hH hb
    have hH1 : H = 1 := eq_one_of_monic_natDegree_zero hH hb
    subst hH1
    rw [roots_one]
    show _ = (Multiset.map _ 0).prod
    rw [Multiset.map_zero, Multiset.prod_zero]
    exact Nev_one _
  | succ b ih =>
    intro H hH hb
    have hdeg : H.degree ≠ 0 := by
      rw [degree_eq_natDegree hH.ne_zero, hb]
      exact_mod_cast Nat.succ_ne_zero b
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_root H hdeg
    set H₁ := H /ₘ (X - C γ) with hH₁
    have hmul' : (X - C γ) * H₁ = H := mul_divByMonic_eq_iff_isRoot.mpr hγ
    have hH₁mon : H₁.Monic := (monic_X_sub_C γ).of_mul_monic_left (by rw [hmul']; exact hH)
    have hH₁deg : H₁.natDegree = b := by
      rw [hH₁, natDegree_divByMonic _ (monic_X_sub_C γ), hb, natDegree_X_sub_C]
      rfl
    rw [← hmul', Nev_linear_mul D n h1 hmul hpoly b γ H₁ hH₁mon hH₁deg, ih H₁ hH₁mon hH₁deg,
      P, ← eval_map_Pof, roots_mul (by rw [hmul']; exact hH.ne_zero), roots_X_sub_C]
    rw [Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons]

include h1 hmul hn in
private theorem eq_resultant (G : ℤ[X]) (hG : G.Monic) (hG0 : ((G.coeff 0 : ℤ) : K) ≠ 0) :
    D G = (G.map (Int.castRingHom ℚ)).resultant (P D n hpoly) := by
  set ι := algebraMap ℚ ℂ with hι
  have hP := monic_P D n hn hpoly
  have hGq : (G.map (Int.castRingHom ℚ)).Monic := hG.map _
  apply (algebraMap ℚ ℂ).injective
  rw [← hι]
  have h1' := Nev_Nf_eq D n h1 hpoly G.natDegree G hG rfl hG0
  have hnat : ι (Nev (Nf D n hpoly G.natDegree) (G.map (Int.castRingHom ℚ))) =
      Nev (Nf D n hpoly G.natDegree) ((G.map (Int.castRingHom ℚ)).map ι) :=
    map_Nev _ _ (Algebra.ofId ℚ ℂ)
  rw [← h1', hnat, Nev_eq_prod_roots D n h1 hmul hpoly G.natDegree ((G.map (Int.castRingHom ℚ)).map
    ι)
    (hGq.map ι) (by rw [hGq.natDegree_map, hG.natDegree_map])]
  have hres := resultant_eq_prod_eval ((G.map (Int.castRingHom ℚ)).map ι) ((P D n hpoly).map ι)
    ((P D n hpoly).map ι).natDegree le_rfl (IsAlgClosed.splits _)
  rw [(hGq.map ι).leadingCoeff, one_pow, one_mul, hGq.natDegree_map, hP.1.natDegree_map,
    resultant_map_map] at hres
  exact hres.symm

end Main
end PolynomialExistsMonicResultantAux

namespace Polynomial

/-- A multiplicative function on monic integer polynomials, given on each
degree by a bounded-degree multivariate polynomial over `ℚ` with leading
coefficient `1`, is given by taking the resultant with a fixed monic
rational polynomial of that degree bound. -/
public theorem exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
    (K : Type*) [Field K] (D : Polynomial ℤ → ℚ) (n : ℕ) (hn : Even n) (h1 : D 1 = 1)
    (hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      ((H.coeff 0 : ℤ) : K) ≠ 0 → D (G * H) = D G * D H)
    (hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧
      N.coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = D G) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = n ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        D G = (G.map (Int.castRingHom ℚ)).resultant P :=
  ⟨PolynomialExistsMonicResultantAux.P D n hpoly,
    (PolynomialExistsMonicResultantAux.monic_P D n hn hpoly).1,
    (PolynomialExistsMonicResultantAux.monic_P D n hn hpoly).2,
    fun G hG hG0 =>
      PolynomialExistsMonicResultantAux.eq_resultant D n hn h1 hmul hpoly G hG hG0⟩

end Polynomial
