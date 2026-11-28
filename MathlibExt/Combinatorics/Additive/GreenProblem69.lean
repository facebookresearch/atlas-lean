/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Green's problem on sums of cubes in ternary vector spaces

We use Yang Yu's support-bound theorem ([arXiv:2510.01300v2](https://arxiv.org/abs/2510.01300v2),
Theorems 5 and 7 and Lemma 6) in the algebra in which each variable squares to zero.
This gives a nonzero squarefree coefficient for a product formed from four labelled bases.
The Combinatorial Nullstellensatz turns that coefficient into a binary choice of columns;
the other 96 cubes in Green's statement contribute zero.
-/

open scoped BigOperators
open MvPolynomial

namespace Green69

noncomputable section

variable {K ι : Type*} [Field K]

private def sqIdeal (K ι : Type*) [Field K] : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range fun i : ι ↦ (X i : MvPolynomial ι K) ^ 2)

private abbrev Q (K ι : Type*) [Field K] := MvPolynomial ι K ⧸ sqIdeal K ι

private abbrev q : MvPolynomial ι K →ₐ[K] Q K ι := Ideal.Quotient.mkₐ K _

private abbrev xvar (x : ι) : Q K ι := q (X x)

private theorem xvar_sq (x : ι) : (xvar x : Q K ι) ^ 2 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨x, rfl⟩)

private def liftQ {R : Type*} [CommRing R] [Algebra K R] (v : ι → R)
    (hv : ∀ x, v x ^ 2 = 0) : Q K ι →ₐ[K] R :=
  Ideal.Quotient.liftₐ _ (aeval v) (fun p hp ↦ by
    apply (show sqIdeal K ι ≤ RingHom.ker (aeval v).toRingHom from
      Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; simpa using hv j)) hp)

@[simp] private theorem liftQ_X {R : Type*} [CommRing R] [Algebra K R]
    (v : ι → R) (hv : ∀ x, v x ^ 2 = 0) (j : ι) :
    liftQ (K := K) v hv (xvar j) = v j := aeval_X _ _

@[simp] private theorem q_C (c : K) : q (C (σ := ι) c) = algebraMap K (Q K ι) c :=
  q.commutes c

private theorem extQ {R : Type*} [CommRing R] [Algebra K R]
    {f g : Q K ι →ₐ[K] R} (h : ∀ j, f (xvar j) = g (xvar j)) : f = g := by
  have he : f.comp q = g.comp q := MvPolynomial.algHom_ext h
  ext p
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  exact DFunLike.congr_fun he p

private def aug : Q K ι →ₐ[K] K := liftQ (fun _ ↦ 0) (by simp)

private def split [DecidableEq ι] (x : ι) : Q K ι →ₐ[K] TrivSqZeroExt (Q K ι) (Q K ι) :=
  liftQ (K := K) (fun j ↦ if j = x then TrivSqZeroExt.inr (1 : Q K ι)
    else TrivSqZeroExt.inl (xvar j : Q K ι)) (by
    intro j
    split_ifs
    · rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    · rw [pow_two, TrivSqZeroExt.inl_mul_inl, ← pow_two, xvar_sq, TrivSqZeroExt.inl_zero])

private def E [DecidableEq ι] (x : ι) : Q K ι →ₐ[K] Q K ι :=
  (TrivSqZeroExt.fstHom K _ _).comp (split x)

private def D [DecidableEq ι] (x : ι) : Q K ι →ₗ[K] Q K ι :=
  ((TrivSqZeroExt.sndHom (Q K ι) (Q K ι)).restrictScalars K).comp (split x).toLinearMap

@[simp] private theorem E_X [DecidableEq ι] (x j : ι) :
    E x (xvar j : Q K ι) = if j = x then 0 else xvar j := by
  change (split x (xvar j)).fst = _
  simp only [split, liftQ_X]
  split_ifs <;> rfl

@[simp] private theorem D_X [DecidableEq ι] (x j : ι) :
    D x (xvar j : Q K ι) = if j = x then 1 else 0 := by
  change (split x (xvar j)).snd = _
  simp only [split, liftQ_X]
  split_ifs <;> rfl

private theorem D_mul [DecidableEq ι] (x : ι) (f g : Q K ι) :
    D x (f * g) = E x f * D x g + D x f * E x g := by
  change (split x (f * g)).snd = _
  rw [map_mul]
  rfl

@[simp] private theorem D_C [DecidableEq ι] (x : ι) (c : K) :
    D x (algebraMap K (Q K ι) c) = 0 := by
  change (split x (algebraMap K (Q K ι) c)).snd = _
  rw [AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl]

private def erasePoly [DecidableEq ι] (x : ι) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval (fun j ↦ if j = x then 0 else X j)

private theorem erasePoly_X [DecidableEq ι] (x j : ι) :
    erasePoly x (X j : MvPolynomial ι K) = if j = x then 0 else X j := aeval_X _ _

private theorem E_q [DecidableEq ι] (x : ι) (p : MvPolynomial ι K) :
    E x (q p) = q (erasePoly x p) := by
  have h : (E x : Q K ι →ₐ[K] Q K ι).comp q = q.comp (erasePoly x) := by
    apply MvPolynomial.algHom_ext
    intro j
    change E x (xvar j) = q (erasePoly x (X j))
    rw [erasePoly_X, E_X]
    split_ifs <;> simp only [map_zero]
  exact DFunLike.congr_fun h p

private theorem D_q [DecidableEq ι] (x : ι) (p : MvPolynomial ι K) :
    D x (q p) = q (erasePoly x (pderiv x p)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [q_C, D_C, pderiv_C, map_zero]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p j hp =>
    simp only [map_mul, D_mul, D_X, pderiv_mul, erasePoly_X, map_add, hp, E_q]
    by_cases h : j = x
    · subst j
      simp only [ite_true, pderiv_X_self, map_one, map_zero, mul_zero, add_zero,
        zero_add, mul_one]
    · simp only [ite_eq_right h, pderiv_X_of_ne h, map_zero, mul_zero, zero_add, add_zero]

private theorem decomp [DecidableEq ι] (x : ι) (f : Q K ι) :
    f = E x f + D x f * xvar x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  change q p = E x (q p) + D x (q p) * xvar x
  induction p using MvPolynomial.induction_on with
  | C c => simp only [q_C, AlgHom.commutes, D_C, zero_mul, add_zero]
  | add p r hp hr =>
    simp only [map_add, add_mul]
    exact (congrArg₂ (· + ·) hp hr).trans (by abel)
  | mul_X p j hp =>
    simp only [map_mul, D_mul, E_X, D_X]
    by_cases h : j = x
    · subst j
      simp only [ite_true, mul_zero, mul_one, add_zero, zero_add]
      calc
        q p * xvar x = (E x (q p) + D x (q p) * xvar x) * xvar x :=
          congrArg (· * xvar x) hp
        _ = E x (q p) * xvar x := by simp only [add_mul, mul_assoc, ← pow_two, xvar_sq,
          mul_zero, add_zero]
    · simp only [ite_eq_right h, mul_zero, zero_add]
      calc
        q p * xvar j = (E x (q p) + D x (q p) * xvar x) * xvar j :=
          congrArg (· * xvar j) hp
        _ = _ := by ring

private theorem E_idem [DecidableEq ι] (x : ι) (f : Q K ι) : E x (E x f) = E x f := by
  have h : (E x).comp (E x) = (E x : Q K ι →ₐ[K] Q K ι) := by
    apply extQ
    intro j
    change E x (E x (xvar j)) = E x (xvar j)
    by_cases he : j = x <;> simp only [E_X, he, ite_true, ite_false, map_zero, eq_self]
  exact DFunLike.congr_fun h f

private theorem D_E [DecidableEq ι] (x : ι) (f : Q K ι) : D x (E x f) = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  change D x (E x (q p)) = 0
  induction p using MvPolynomial.induction_on with
  | C c => simp only [q_C, AlgHom.commutes, D_C]
  | add p r hp hr => simp only [map_add, hp, hr, add_zero]
  | mul_X p j hp =>
    by_cases h : j = x <;>
      simp only [map_mul, E_X, h, ite_true, ite_false, mul_zero, map_zero,
        D_mul, D_X, hp, zero_mul, add_zero]

private theorem E_D [DecidableEq ι] (x : ι) (f : Q K ι) : E x (D x f) = D x f := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  change E x (D x (q p)) = D x (q p)
  induction p using MvPolynomial.induction_on with
  | C c => simp only [q_C, D_C, map_zero]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p j hp =>
    by_cases h : j = x <;>
      simp only [map_mul, D_mul, D_X, E_X, h, ite_true, ite_false, mul_zero,
        mul_one, zero_add, add_zero, E_idem, hp]

private def Deg (d : ℤ) (f : Q K ι) : Prop :=
  ∃ p : MvPolynomial ι K, (p = 0 ∨ (p.totalDegree : ℤ) ≤ d) ∧ q p = f

private theorem Deg.zero (d : ℤ) : Deg d (0 : Q K ι) := ⟨0, Or.inl rfl, map_zero q⟩

private theorem Deg.mono {d e : ℤ} {f : Q K ι} (h : Deg d f) (hle : d ≤ e) : Deg e f := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p, hp.imp_right (·.trans hle), rfl⟩

private theorem Deg.add {d : ℤ} {f g : Q K ι} (hf : Deg d f) (hg : Deg d g) : Deg d (f + g) := by
  obtain ⟨p, hp | hp, rfl⟩ := hf
  · simpa [hp] using hg
  obtain ⟨r, hr | hr, rfl⟩ := hg
  · simpa [hr] using (show Deg d (q p) from ⟨p, Or.inr hp, rfl⟩)
  refine ⟨p + r, Or.inr ?_, map_add q _ _⟩
  have := totalDegree_add p r
  omega

private theorem Deg.neg {d : ℤ} {f : Q K ι} (hf : Deg d f) : Deg d (-f) := by
  obtain ⟨p, hp | hp, rfl⟩ := hf
  · simp [hp, Deg.zero]
  exact ⟨-p, Or.inr (by simpa using hp), map_neg q _⟩

private theorem Deg.sub {d : ℤ} {f g : Q K ι} (hf : Deg d f) (hg : Deg d g) : Deg d (f - g) :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

private theorem Deg.mul {d e : ℤ} {f g : Q K ι} (hf : Deg d f) (hg : Deg e g) :
    Deg (d + e) (f * g) := by
  obtain ⟨p, hp | hp, rfl⟩ := hf
  · simp [hp, Deg.zero]
  obtain ⟨r, hr | hr, rfl⟩ := hg
  · simp [hr, Deg.zero]
  refine ⟨p * r, Or.inr ?_, map_mul q _ _⟩
  have := totalDegree_mul p r
  omega

private theorem Deg.sum {J : Type*} {d : ℤ} (s : Finset J) {f : J → Q K ι}
    (h : ∀ j ∈ s, Deg d (f j)) : Deg d (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Deg.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private theorem Deg.C (c : K) : Deg 0 (algebraMap K (Q K ι) c) :=
  ⟨MvPolynomial.C c, Or.inr (by simp), q_C c⟩

private theorem Deg.const {f : Q K ι} (h : Deg 0 f) : ∃ c : K, f = algebraMap K _ c := by
  obtain ⟨p, hp | hp, rfl⟩ := h
  · exact ⟨0, by simp [hp]⟩
  have hd : p.totalDegree = 0 := by omega
  exact ⟨p.coeff 0, (congrArg q (totalDegree_eq_zero_iff_eq_C.mp hd)).trans (q_C _)⟩

private theorem Deg.eq_zero {d : ℤ} {f : Q K ι} (hd : d < 0) (h : Deg d f) : f = 0 := by
  obtain ⟨p, hp | hp, rfl⟩ := h
  · simp [hp]
  · omega

private theorem Deg.X (x : ι) : Deg 1 (xvar x : Q K ι) := ⟨MvPolynomial.X x, Or.inr (by simp), rfl⟩


private theorem erasePoly_degree [DecidableEq ι] (x : ι) (p : MvPolynomial ι K) :
    (erasePoly x p).totalDegree ≤ p.totalDegree := by
  classical
  have h : erasePoly x p = ∑ m ∈ p.support,
      if (m.support : Set ι) ⊆ {x}ᶜ then monomial m (p.coeff m) else 0 := by
    rw [← aeval_ite_mem_eq]
    apply congrArg (fun F : MvPolynomial ι K →ₐ[K] MvPolynomial ι K ↦ F p)
    apply MvPolynomial.algHom_ext
    intro j
    rw [erasePoly_X, aeval_X]
    by_cases hj : j = x <;> simp [hj]
  rw [h]
  apply totalDegree_finsetSum_le
  intro m hm
  split_ifs
  · exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
  · simp

private theorem pderiv_degree (x : ι) (p : MvPolynomial ι K)
    (hp : pderiv x p ≠ 0) : (pderiv x p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup (s := (pderiv x p).support)
    (f := fun m ↦ m.degree) (by simpa [Finset.nonempty_iff_ne_empty] using hp)
  have hcoeff : (pderiv x p).coeff m ≠ 0 := mem_support_iff.mp hm
  rw [coeff_pderiv] at hcoeff
  have h := le_totalDegree (mem_support_iff.mpr (left_ne_zero_of_mul hcoeff))
  change (m + Finsupp.single x 1).degree ≤ p.totalDegree at h
  rw [map_add, Finsupp.degree_single] at h
  change (pderiv x p).totalDegree = m.degree at he
  omega

private theorem Deg.erase [DecidableEq ι] {d : ℤ} {f : Q K ι} (h : Deg d f) (x : ι) :
    Deg d (E x f) := by
  obtain ⟨p, hp | hp, rfl⟩ := h
  · simp [hp, Deg.zero]
  exact ⟨erasePoly x p, Or.inr ((Int.ofNat_le.mpr (erasePoly_degree x p)).trans hp),
    (E_q x p).symm⟩

private theorem Deg.coefficient [DecidableEq ι] {d : ℤ} {f : Q K ι} (h : Deg d f) (x : ι) :
    Deg (d - 1) (D x f) := by
  obtain ⟨p, hp | hp, rfl⟩ := h
  · simp [hp, Deg.zero]
  rw [D_q]
  by_cases hz : pderiv x p = 0
  · simp [hz, Deg.zero]
  refine ⟨erasePoly x (pderiv x p), Or.inr ?_, rfl⟩
  have := erasePoly_degree x (pderiv x p)
  have := pderiv_degree x p hz
  omega

section Forms

variable [Fintype ι] [DecidableEq ι]

private def formPoly : (ι → K) →ₗ[K] MvPolynomial ι K where
  toFun u := ∑ j, C (u j) * X j
  map_add' u v := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_assoc,
      Finset.mul_sum, smul_eq_C_mul]

private abbrev form : (ι → K) →ₗ[K] Q K ι := q.toLinearMap.comp formPoly

omit [DecidableEq ι] in
private theorem form_apply (u : ι → K) :
    form u = ∑ j, algebraMap K (Q K ι) (u j) * xvar j := by
  change q (∑ j, C (u j) * X j) = _
  simp only [map_sum, map_mul, q_C]

private def eraseVec (x : ι) : (ι → K) →ₗ[K] (ι → K) where
  toFun u j := if j = x then 0 else u j
  map_add' u v := by ext j; by_cases h : j = x <;> simp [h]
  map_smul' c u := by ext j; by_cases h : j = x <;> simp [h]

omit [Fintype ι] in
@[simp] private theorem eraseVec_apply (x : ι) (u : ι → K) (j : ι) :
    eraseVec x u j = if j = x then 0 else u j := rfl

private theorem E_form (x : ι) (u : ι → K) : E x (form u) = form (eraseVec x u) := by
  simp only [form_apply, map_sum, map_mul, AlgHom.commutes, E_X, eraseVec_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [mul_zero, map_zero, zero_mul]

private theorem D_form (x : ι) (u : ι → K) : D x (form u) = algebraMap K (Q K ι) (u x) := by
  simp only [form_apply, map_sum, D_mul, AlgHom.commutes, D_C, zero_mul, add_zero, D_X]
  rw [Finset.sum_eq_single x]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

omit [DecidableEq ι] in
private theorem Deg.form (u : ι → K) : Deg 1 (form u) := by
  rw [form_apply]
  apply Deg.sum
  intro j _
  exact (Deg.C (u j)).mul (Deg.X j)

omit [DecidableEq ι] in
private theorem formPoly_degree (u : ι → K) : (formPoly u).totalDegree ≤ 1 := by
  change (∑ j, C (u j) * X j).totalDegree ≤ 1
  apply totalDegree_finsetSum_le
  intro j _
  simpa only [totalDegree_C, totalDegree_X, zero_add] using
    totalDegree_mul (C (u j)) (X j)

omit [DecidableEq ι] in
private theorem coeff_formPoly (u : ι → K) (j : ι) :
    (formPoly u).coeff (Finsupp.single j 1) = u j := by
  classical
  change (∑ i, C (u i) * X i).coeff (Finsupp.single j 1) = _
  simp only [coeff_sum, C_mul_X_eq_monomial, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have h : Finsupp.single i (1 : ℕ) ≠ Finsupp.single j 1 := by
      intro he
      have := congrFun (congrArg DFunLike.coe he) j
      simp [hij.symm] at this
    exact ite_eq_right h
  · simp

end Forms

section Characteristic

variable [CharP K 3]

private theorem three_q : (3 : Q K ι) = 0 := by
  have h : (3 : K) = 0 := CharP.cast_eq_zero K 3
  exact (map_ofNat (algebraMap K (Q K ι)) 3).symm.trans (by rw [h, map_zero])

private theorem two_q : (2 : Q K ι) = -1 := by linear_combination (three_q (K := K) (ι := ι))

private theorem cube_add (a b : Q K ι) : (a + b) ^ 3 = a ^ 3 + b ^ 3 := by
  linear_combination (a ^ 2 * b + a * b ^ 2) * (three_q (K := K) (ι := ι))

private theorem form_cube [Fintype ι] (u : ι → K) : form u ^ 3 = 0 := by
  classical
  rw [form_apply]
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hs =>
    rw [Finset.sum_insert hj, cube_add, hs, add_zero, mul_pow,
      show (xvar j : Q K ι) ^ 3 = xvar j ^ 2 * xvar j by rfl,
      xvar_sq, zero_mul, mul_zero]


end Characteristic

section Support

open Submodule

variable [Fintype ι] [DecidableEq ι]

private abbrev Vec (K ι : Type*) := ι → K

private def vsupp (u : Vec K ι) : Finset ι := by classical exact Finset.univ.filter (u · ≠ 0)

omit [DecidableEq ι] in
@[simp] private theorem mem_vsupp {u : Vec K ι} {x : ι} : x ∈ vsupp u ↔ u x ≠ 0 := by
  classical
  simp [vsupp]

private def supp (U : Submodule K (Vec K ι)) : Finset ι := by
  classical exact Finset.univ.filter (fun x ↦ ∃ u ∈ U, u x ≠ 0)

omit [DecidableEq ι] in
@[simp] private theorem mem_supp {U : Submodule K (Vec K ι)} {x : ι} :
    x ∈ supp U ↔ ∃ u ∈ U, u x ≠ 0 := by
  classical
  simp [supp]

private def Covers (c : ℤ) (U : Submodule K (Vec K ι)) : Prop :=
  ∀ W ≤ U, 0 < Module.finrank K W → 4 * (Module.finrank K W : ℤ) + c ≤ (supp W).card

omit [DecidableEq ι] in
private theorem Covers.mono {c d : ℤ} {U V : Submodule K (Vec K ι)}
    (h : Covers c U) (hVU : V ≤ U) (hdc : d ≤ c) : Covers d V := by
  intro W hWV hp
  have := h W (hWV.trans hVU) hp
  omega

omit [DecidableEq ι] in
private theorem supp_span_singleton (u : Vec K ι) : supp (K ∙ u) = vsupp u := by
  ext x
  rw [mem_supp, mem_vsupp]
  constructor
  · rintro ⟨v, hv, hne⟩ he
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact hne (by simp [he])
  · intro h
    exact ⟨u, Submodule.subset_span (Set.mem_singleton _), h⟩

omit [DecidableEq ι] in
private theorem Covers.vec {c : ℤ} {U : Submodule K (Vec K ι)} (h : Covers c U)
    {u : Vec K ι} (hu : u ∈ U) (hne : u ≠ 0) : 4 + c ≤ (vsupp u).card := by
  have hr := finrank_span_singleton (K := K) hne
  simpa only [hr, supp_span_singleton, Nat.cast_one, mul_one] using
    h (K ∙ u) ((span_le.mpr (Set.singleton_subset_iff.mpr hu))) (hr.symm ▸ Nat.one_pos)

private theorem vsupp_erase (x : ι) (u : Vec K ι) : vsupp (eraseVec x u) = (vsupp u).erase x := by
  ext j
  by_cases hj : j = x <;> simp [hj]

private theorem supp_map_erase (x : ι) (U : Submodule K (Vec K ι)) :
    supp (U.map (eraseVec x)) = (supp U).erase x := by
  ext j
  by_cases hj : j = x
  · subst j
    simp only [mem_supp, Submodule.mem_map, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      iff_false]
    rintro ⟨_, ⟨u, _, rfl⟩, hne⟩
    exact hne (by simp)
  · simp only [Finset.mem_erase, ne_eq, hj, not_false_eq_true, true_and, mem_supp,
      Submodule.mem_map]
    exact ⟨fun ⟨_, ⟨u, hu, rfl⟩, hne⟩ ↦ ⟨u, hu, by simpa only [eraseVec_apply, ite_eq_right hj]
      using hne⟩, fun ⟨u, hu, hne⟩ ↦ ⟨eraseVec x u, ⟨u, hu, rfl⟩,
      by simpa only [eraseVec_apply, ite_eq_right hj] using hne⟩⟩

private theorem eraseVec_ker_inj {c : ℤ} {U : Submodule K (Vec K ι)} (h : Covers c U)
    (hc : -2 ≤ c) (x : ι) : Function.Injective ((eraseVec x).comp U.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro u hu
  by_contra hn
  have hnu : (u : Vec K ι) ≠ 0 := fun h0 ↦ hn (Subtype.ext h0)
  have hs := h.vec u.property hnu
  have hsub : vsupp (u : Vec K ι) ⊆ {x} := by
    intro j hj
    by_contra hne
    have he : eraseVec x (u : Vec K ι) = 0 := hu
    have := congrFun he j
    have hjx : j ≠ x := by simpa using hne
    exact (mem_vsupp.mp hj) (by simpa only [eraseVec_apply, ite_eq_right hjx, Pi.zero_apply]
      using this)
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

omit [Fintype ι] [DecidableEq ι] in
private theorem finrank_map_restrict (f : Vec K ι →ₗ[K] Vec K ι)
    {U : Submodule K (Vec K ι)} (hinj : Function.Injective (f.comp U.subtype)) :
    Module.finrank K (U.map f) = Module.finrank K U := by
  have h : LinearMap.range (f.comp U.subtype) = U.map f := by
    rw [LinearMap.range_comp, U.range_subtype]
  rw [← h]
  exact LinearMap.finrank_range_of_inj hinj

private theorem Covers.erase {c : ℤ} {U : Submodule K (Vec K ι)} (h : Covers c U)
    (hc : -2 ≤ c) (x : ι) : Covers (c - 1) (U.map (eraseVec x)) := by
  intro W hW hp
  let V := U ⊓ W.comap (eraseVec x)
  have hV : V ≤ U := inf_le_left
  have he : V.map (eraseVec x) = W := by
    dsimp only [V]
    rw [← Submodule.map_inf_eq_map_inf_comap, inf_of_le_right hW]
  have hi : Function.Injective ((eraseVec x).comp V.subtype) := by
    intro a b hab
    have hh : (⟨a, hV a.property⟩ : U) = ⟨b, hV b.property⟩ := eraseVec_ker_inj h hc x hab
    exact Subtype.ext (congrArg (fun a : U ↦ (a : Vec K ι)) hh)
  have hr := finrank_map_restrict (eraseVec x) hi
  have hpos : 0 < Module.finrank K V := by rwa [← he, hr] at hp
  have hs := h V hV hpos
  have hd := Finset.card_erase_add_one (s := supp V) (a := x)
  rw [← he, supp_map_erase, hr]
  by_cases hx : x ∈ supp V
  · have := hd hx
    omega
  · rw [Finset.erase_eq_of_notMem hx]
    omega

private def supportedOn (s : Finset ι) : Submodule K (Vec K ι) where
  carrier := { u | ∀ j ∉ s, u j = 0 }
  zero_mem' := by simp
  add_mem' {u v} hu hv := fun j hj ↦ by simp [hu j hj, hv j hj]
  smul_mem' c u hu := fun j hj ↦ by simp [hu j hj]

omit [DecidableEq ι] in
private theorem supp_le_iff {U : Submodule K (Vec K ι)} {s : Finset ι} :
    supp U ⊆ s ↔ U ≤ supportedOn s := by
  classical
  constructor
  · intro h u hu j hj
    by_contra hne
    exact hj (h (mem_supp.mpr ⟨u, hu, hne⟩))
  · intro h j hj
    by_contra hn
    obtain ⟨u, hu, hne⟩ := mem_supp.mp hj
    exact hne (h hu j hn)

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_avoiding [Finite ι] [Infinite K] {J : Type*} [Finite J]
    (w : J → Vec K ι) (hw : ∀ j, w j ≠ 0) :
    ∃ l : Vec K ι →ₗ[K] K, ∀ j, l (w j) ≠ 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype J := Fintype.ofFinite J
  let P := ∏ j, formPoly (w j)
  have hnz : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _ hz
    apply hw j
    funext i
    simpa [coeff_formPoly] using congrArg (fun p : MvPolynomial ι K ↦
      p.coeff (Finsupp.single i 1)) hz
  obtain ⟨a, ha⟩ : ∃ a : Vec K ι, eval a P ≠ 0 := by
    by_contra! h
    exact hnz (MvPolynomial.funext (fun a ↦ (h a).trans (map_zero (eval a)).symm))
  let l : Vec K ι →ₗ[K] K := ∑ i, a i • LinearMap.proj i
  refine ⟨l, fun j hj ↦ ha ?_⟩
  rw [show eval a P = ∏ j, l (w j) by
    simp only [P, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    change eval a (∑ i, C (w j i) * X i) = _
    simp only [map_sum, map_mul, eval_C, eval_X, l, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hj

omit [Fintype ι] [DecidableEq ι] in
private theorem finrank_inf_ker [Finite ι] (U : Submodule K (Vec K ι)) {l : Vec K ι →ₗ[K] K}
    (h : ∃ u ∈ U, l u ≠ 0) :
    Module.finrank K ↥(U ⊓ LinearMap.ker l) + 1 = Module.finrank K U := by
  let lU := l.comp U.subtype
  have hnonzero : lU ≠ 0 := by
    obtain ⟨u, hu, hn⟩ := h
    exact fun he ↦ hn (DFunLike.congr_fun he ⟨u, hu⟩)
  have hr : LinearMap.range lU = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun z ↦ by
      obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hnonzero
      exact ⟨(z / lU v) • v, by rw [map_smul]; exact div_mul_cancel₀ z hv⟩
  have hd := lU.finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self, add_comm] at hd
  have he : (LinearMap.ker lU).map U.subtype = U ⊓ LinearMap.ker l := by
    ext u
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, lU, LinearMap.comp_apply,
      Submodule.subtype_apply]
    exact ⟨fun ⟨v, hv, he⟩ ↦ he ▸ ⟨v.property, hv⟩, fun ⟨hU, hker⟩ ↦ ⟨⟨u, hU⟩, hker, rfl⟩⟩
  rwa [← he, Submodule.finrank_map_subtype_eq]

-- A single hyperplane misses one chosen nonzero vector in each nonzero coordinate section.
omit [DecidableEq ι] in
private theorem genericHyperplane [Infinite K] {c : ℤ} {U : Submodule K (Vec K ι)}
    (h : Covers c U) (hu : 0 < Module.finrank K U) :
    ∃ V ≤ U, Module.finrank K V + 1 = Module.finrank K U ∧ Covers (c + 4) V := by
  classical
  let sectionOn (s : Finset ι) := U ⊓ supportedOn (K := K) s
  let J := {s : Finset ι // sectionOn s ≠ ⊥}
  have hw (s : J) : ∃ u ∈ sectionOn s.val, (u : Vec K ι) ≠ 0 :=
    (sectionOn s.val).ne_bot_iff.mp s.property
  choose w hmem hne using hw
  obtain ⟨l, hl⟩ := exists_avoiding w hne
  let V := U ⊓ LinearMap.ker l
  have hsection : sectionOn Finset.univ = U := by
    simp only [sectionOn, inf_eq_left]
    exact supp_le_iff.mp (Finset.subset_univ _)
  let j : J := ⟨Finset.univ, by rw [hsection]; exact fun he ↦ by rw [he, finrank_bot] at hu; omega⟩
  have hr := finrank_inf_ker U ⟨w j, (hmem j).1, hl j⟩
  refine ⟨V, inf_le_left, hr, ?_⟩
  intro W hW hp
  let S := sectionOn (supp W)
  have hWS : W ≤ S := le_inf (hW.trans inf_le_left) (supp_le_iff.mp (by rfl))
  have hS : S ≠ ⊥ := by
    intro he
    have := finrank_mono hWS
    rw [he, finrank_bot] at this
    omega
  let js : J := ⟨supp W, hS⟩
  have hlt : W < S := lt_of_le_of_ne hWS (fun he ↦
    hl js (show l (w js) = 0 from (hW (he ▸ hmem js)).2))
  have hd := finrank_lt_finrank_of_lt hlt
  have hs := h S inf_le_left (by omega)
  have hb : (supp S).card ≤ (supp W).card := Finset.card_le_card (supp_le_iff.mpr inf_le_right)
  omega

end Support

section Generators

open Submodule

variable [Fintype ι] [DecidableEq ι] [CharP K 3]

omit [CharP K 3] [Fintype ι] [DecidableEq ι] in
private theorem q_smul (a : K) (f : Q K ι) : a • f = algebraMap K (Q K ι) a * f := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective f
  change q (a • p) = algebraMap K (Q K ι) a * q p
  rw [smul_eq_C_mul, map_mul, q_C]

omit [Fintype ι] [DecidableEq ι] [CharP K 3] in
private theorem deg_smul {d : ℤ} {f : Q K ι} (hf : Deg d f) (c : K) : Deg d (c • f) := by
  rw [q_smul]
  simpa only [zero_add] using (Deg.C (ι := ι) c).mul hf

private def Gen (d : ℤ) (U : Submodule K (Vec K ι)) : Submodule K (Q K ι) :=
  Submodule.span K {t | ∃ a : Q K ι, Deg (d - 1) a ∧ ∃ u ∈ U, t = a * form u}

omit [CharP K 3] [DecidableEq ι] in
private theorem gen_single {d : ℤ} {U : Submodule K (Vec K ι)} {a : Q K ι}
    (ha : Deg (d - 1) a) {u : Vec K ι} (hu : u ∈ U) : a * form u ∈ Gen d U :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

omit [CharP K 3] [DecidableEq ι] in
private theorem gen_mono {d : ℤ} {U W : Submodule K (Vec K ι)} (h : U ≤ W) : Gen d U ≤ Gen d W :=
  Submodule.span_le.mpr (by rintro _ ⟨a, ha, u, hu, rfl⟩; exact gen_single ha (h hu))

omit [CharP K 3] [DecidableEq ι] in
private theorem gen_eq_zero {d : ℤ} {U : Submodule K (Vec K ι)} (hd : d < 1)
    {f : Q K ι} (hf : f ∈ Gen d U) : f = 0 := by
  apply (Submodule.mem_bot K).mp
  apply (show Gen d U ≤ ⊥ from Submodule.span_le.mpr ?_) hf
  rintro _ ⟨a, ha, u, _, rfl⟩
  simp [ha.eq_zero (by omega)]

omit [CharP K 3] in
private theorem gen_erase (x : ι) {d : ℤ} {U : Submodule K (Vec K ι)} {f : Q K ι}
    (hf : f ∈ Gen d U) : E x f ∈ Gen d (U.map (eraseVec x)) := by
  induction hf using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, u, hu, rfl⟩ := ht
    rw [map_mul, E_form]
    exact gen_single (ha.erase x) (Submodule.mem_map_of_mem hu)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

omit [DecidableEq ι] [CharP K 3] in
private theorem gen_split {d : ℤ} {W : Submodule K (Vec K ι)} {u : Vec K ι} {f : Q K ι}
    (hf : f ∈ Gen d (W ⊔ K ∙ u)) :
    ∃ a : Q K ι, Deg (d - 1) a ∧ ∃ g ∈ Gen d W, f = a * form u + g := by
  induction hf using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, v, hv, rfl⟩ := ht
    obtain ⟨w, hw, t, ht, he⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rw [← he]
    refine ⟨c • a, deg_smul ha c, a * form w, gen_single ha hw, ?_⟩
    rw [map_add, map_smul, q_smul c (form u), q_smul c a]
    ring
  | zero => exact ⟨0, Deg.zero _, 0, Submodule.zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, g, hg, rfl⟩ := ha
    obtain ⟨e, he, t, ht, rfl⟩ := hb
    exact ⟨c + e, hc.add he, g + t, Submodule.add_mem _ hg ht, by ring⟩
  | smul c a _ ha =>
    obtain ⟨e, he, g, hg, rfl⟩ := ha
    exact ⟨c • e, deg_smul he c, c • g, Submodule.smul_mem _ _ hg,
      by simp only [q_smul]; ring⟩

omit [CharP K 3] [DecidableEq ι] in
private theorem gen_mul_ann {d : ℤ} {U : Submodule K (Vec K ι)} {f t : Q K ι}
    (hf : f ∈ Gen d U) (ht : ∀ u ∈ U, form u * t = 0) : f * t = 0 := by
  induction hf using Submodule.span_induction with
  | mem a ha => obtain ⟨g, _, u, hu, rfl⟩ := ha; rw [mul_assoc, ht u hu, mul_zero]
  | zero => exact zero_mul _
  | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_mul_assoc, ha, smul_zero]

private abbrev topProd {J : Type*} [Fintype J] (b : J → Vec K ι) : Q K ι :=
  ∏ j, form (b j) ^ 2

omit [DecidableEq ι] in
private theorem powBinomial {J : Type*} [Fintype J] (b : J → Vec K ι)
    {p : MvPolynomial J K} (hp : p.IsHomogeneous (2 * Fintype.card J)) :
    ∃ c : K, (aeval (fun j ↦ form (b j))) p = algebraMap K (Q K ι) c * topProd b := by
  classical
  let m : J →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ ↦ 2)
  refine ⟨p.coeff m, ?_⟩
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, aeval_monomial]
  rw [Finset.sum_eq_single m]
  · congr 1
    rw [Finsupp.prod_fintype _ _ (fun j ↦ pow_zero (form (b j)))]
    rfl
  · intro v hv hvm
    have hbig : ∃ j, 3 ≤ v j := by
      by_contra! h
      have hd := hp.degree_eq_sum_deg_support hv
      rw [← Finsupp.degree_apply, Finsupp.degree_eq_sum] at hd
      have he : ∑ j, v j = ∑ _j : J, (2 : ℕ) := by
        simpa [Finset.sum_const, Nat.mul_comm] using hd.symm
      apply hvm
      ext j
      exact (Finset.sum_eq_sum_iff_of_le (fun j _ ↦ show v j ≤ 2 by have := h j; omega)).mp he j
        (Finset.mem_univ _)
    obtain ⟨j, hj⟩ := hbig
    rw [Finsupp.prod_fintype _ _ (fun j ↦ pow_zero (form (b j))),
      Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
    rw [show v j = v j - 3 + 3 from (Nat.sub_add_cancel hj).symm, pow_add,
      form_cube, mul_zero]
  · intro hm
    rw [notMem_support_iff.mp hm, map_zero, zero_mul]

omit [DecidableEq ι] in
private theorem top_transfer {J L : Type*} [Fintype J] [Fintype L]
    (b : J → Vec K ι) (c : L → Vec K ι) (he : Fintype.card J = Fintype.card L)
    (hc : ∀ l, c l ∈ Submodule.span K (Set.range b)) :
    ∃ k : K, topProd c = algebraMap K (Q K ι) k * topProd b := by
  classical
  have hl (l : L) : ∃ a : J → K, c l = ∑ j, a j • b j := by
    obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (hc l)
    exact ⟨d, hd.symm.trans (Finsupp.sum_fintype d (fun i a ↦ a • b i)
      (fun _ ↦ zero_smul K _))⟩
  choose a ha using hl
  let p (l : L) : MvPolynomial J K := ∑ j, C (a l j) * X j
  have hp (l : L) : (p l).IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    exact isHomogeneous_C_mul_X _ _
  have hprod : (∏ l, p l ^ 2).IsHomogeneous (2 * Fintype.card J) := by
    rw [he]
    simpa [Nat.mul_comm] using (MvPolynomial.IsHomogeneous.prod Finset.univ (fun l ↦ p l ^ 2)
      (fun _ ↦ 2) (fun l _ ↦ by simpa using (hp l).pow 2))
  obtain ⟨k, hk⟩ := powBinomial b hprod
  refine ⟨k, ?_⟩
  rw [← hk]
  simp only [map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  rw [ha l]
  simp only [p, map_sum, map_mul, aeval_X, aeval_C, map_smul]
  exact Finset.sum_congr rfl fun j _ ↦ q_smul _ _

omit [DecidableEq ι] in
private theorem top_ann {J : Type*} [Fintype J] (b : J → Vec K ι)
    {u : Vec K ι} (hu : u ∈ Submodule.span K (Set.range b)) : form u * topProd b = 0 := by
  classical
  induction hu using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    unfold topProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), ← mul_assoc,
      ← pow_succ', form_cube, zero_mul]
  | zero => rw [map_zero, zero_mul]
  | add a b _ _ ha hb => rw [map_add, add_mul, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, smul_mul_assoc, ha, smul_zero]

end Generators

section Splitting

open Submodule

variable [Fintype ι] [DecidableEq ι]

private abbrev coord (x : ι) : Vec K ι →ₗ[K] K := LinearMap.proj x

private abbrev clean (x : ι) (U : Submodule K (Vec K ι)) := U ⊓ LinearMap.ker (coord x)

omit [Fintype ι] [DecidableEq ι] in
private theorem clean_val {x : ι} {U : Submodule K (Vec K ι)} {u : Vec K ι}
    (hu : u ∈ clean x U) : u x = 0 := hu.2

omit [Fintype ι] in
private theorem eraseVec_eq_self {x : ι} {u : Vec K ι} (h : u x = 0) : eraseVec x u = u := by
  funext j
  by_cases hj : j = x <;> simp [hj, h]

omit [Fintype ι] in
private theorem clean_map (x : ι) (U : Submodule K (Vec K ι)) :
    (clean x U).map (eraseVec x) = clean x U := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    rwa [eraseVec_eq_self (clean_val hu)]
  · intro hv
    exact Submodule.mem_map.mpr ⟨v, hv, eraseVec_eq_self (clean_val hv)⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem pivot {U : Submodule K (Vec K ι)} (h : 0 < Module.finrank K U) :
    ∃ x : ι, ∃ p ∈ U, p x = 1 := by
  classical
  have hn : U ≠ ⊥ := by rintro rfl; simp at h
  obtain ⟨p, hp, hp0⟩ := U.ne_bot_iff.mp hn
  obtain ⟨x, hx⟩ : ∃ x, p x ≠ 0 := by
    by_contra! hzero
    exact hp0 (funext hzero)
  refine ⟨x, (p x)⁻¹ • p, U.smul_mem _ hp, ?_⟩
  simp [hx]

omit [Fintype ι] [DecidableEq ι] in
private theorem clean_split {U : Submodule K (Vec K ι)} {x : ι} {p : Vec K ι}
    (hp : p ∈ U) (hx : p x = 1) : clean x U ⊔ K ∙ p = U := by
  apply le_antisymm (sup_le inf_le_left (span_le.mpr (Set.singleton_subset_iff.mpr hp)))
  intro v hv
  apply Submodule.mem_sup.mpr
  refine ⟨v - v x • p, ⟨U.sub_mem hv (U.smul_mem _ hp), ?_⟩, v x • p,
    mem_span_singleton.mpr ⟨v x, rfl⟩, sub_add_cancel _ _⟩
  change (v - v x • p) x = 0
  simp [hx]

omit [Fintype ι] [DecidableEq ι] in
private theorem clean_rank [Finite ι] {U : Submodule K (Vec K ι)} {x : ι} {p : Vec K ι}
    (hp : p ∈ U) (hx : p x = 1) : Module.finrank K (clean x U) + 1 = Module.finrank K U :=
  finrank_inf_ker U ⟨p, hp, by simp [coord, hx]⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem clean_extend [Finite ι] {U V : Submodule K (Vec K ι)} {x : ι} {p : Vec K ι}
    (hVU : V ≤ U) (hr : Module.finrank K V + 1 = Module.finrank K U) (hp : p ∈ V) (hx : p x = 1) :
    ∃ v ∈ clean x U, v ∉ clean x V ∧ clean x V ⊔ K ∙ v = clean x U := by
  have hn : ¬U ≤ V := by
    intro hUV
    have := finrank_mono hUV
    omega
  obtain ⟨u, hu, hnu⟩ : ∃ u, u ∈ U ∧ u ∉ V := by
    by_contra! h
    exact hn h
  let v := u - u x • p
  have hv : v ∈ clean x U := ⟨U.sub_mem hu (U.smul_mem _ (hVU hp)), by
    change v x = 0
    simp [v, hx]⟩
  have hvn : v ∉ clean x V := by
    intro h
    exact hnu (show u ∈ V from (sub_add_cancel u (u x • p)) ▸ V.add_mem h.1 (V.smul_mem _ hp))
  refine ⟨v, hv, hvn, ?_⟩
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le (inf_le_inf_right _ hVU) (span_le.mpr (Set.singleton_subset_iff.mpr hv))
  · rw [Submodule.finrank_sup_span_singleton hvn]
    have h1 := clean_rank hp hx
    have h2 := clean_rank (hVU hp) hx
    omega

private abbrev delta (x : ι) : Vec K ι := Pi.single x 1

private theorem form_delta (x : ι) : form (delta (K := K) x) = xvar x := by
  rw [form_apply, Finset.sum_eq_single x]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

omit [Fintype ι] in
private theorem vec_expand (x : ι) (u : Vec K ι) : u = eraseVec x u + u x • delta x := by
  ext j
  by_cases hj : j = x <;> simp [hj]

private theorem form_expand {x : ι} {u : Vec K ι} (h : u x = 1) :
    form u = form (eraseVec x u) + xvar x := by
  nth_rw 1 [vec_expand x u]
  rw [map_add, h, one_smul, form_delta]

omit [Fintype ι] [DecidableEq ι] in
private theorem aug_inj : Function.Injective (algebraMap K (Q K ι)) :=
  Function.LeftInverse.injective (f := algebraMap K (Q K ι)) (g := aug) fun c ↦ aug.commutes c

omit [DecidableEq ι] in
private theorem form_inj : Function.Injective (form (K := K) (ι := ι)) := by
  classical
  intro u v h
  funext x
  apply aug_inj (ι := ι)
  simpa only [D_form] using congrArg (D x) h

omit [DecidableEq ι] in
private theorem gen_one {U : Submodule K (Vec K ι)} {f : Q K ι} (hf : f ∈ Gen 1 U) :
    f ∈ U.map form := by
  induction hf using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, u, hu, rfl⟩ := ht
    rw [sub_self] at ha
    obtain ⟨c, rfl⟩ := ha.const
    exact Submodule.mem_map.mpr ⟨c • u, U.smul_mem c hu, by rw [map_smul, q_smul]⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c _ _ ha => exact Submodule.smul_mem _ c ha

private theorem clean_gen_deriv (x : ι) {d : ℤ} {U : Submodule K (Vec K ι)} {g : Q K ι}
    (hg : g ∈ Gen d (clean x U)) : D x g ∈ Gen (d - 1) (clean x U) := by
  induction hg using Submodule.span_induction with
  | mem _ ht =>
    obtain ⟨a, ha, u, hu, rfl⟩ := ht
    rw [D_mul, D_form, clean_val hu, map_zero, mul_zero, zero_add, E_form,
      eraseVec_eq_self (clean_val hu)]
    exact gen_single (ha.coefficient x) hu
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

private theorem clean_gen_erase (x : ι) {d : ℤ} {U : Submodule K (Vec K ι)} {g : Q K ι}
    (hg : g ∈ Gen d (clean x U)) : E x g ∈ Gen d (clean x U) := by
  simpa only [clean_map] using gen_erase x hg

private abbrev basisVec (U : Submodule K (Vec K ι)) : Fin (Module.finrank K U) → Vec K ι :=
  fun j ↦ (Module.finBasis K U j : Vec K ι)

omit [DecidableEq ι] in
private theorem basisVec_span (U : Submodule K (Vec K ι)) :
    Submodule.span K (Set.range (basisVec U)) = U := by
  have h := congrArg (Submodule.map U.subtype) (Module.finBasis K U).span_eq
  rwa [Submodule.map_span, Submodule.map_top, U.range_subtype, ← Set.range_comp] at h

private abbrev top (U : Submodule K (Vec K ι)) := topProd (basisVec U)

private theorem clean_top_E (x : ι) (U : Submodule K (Vec K ι)) :
    E x (top (clean x U)) = top (clean x U) := by
  simp only [top, topProd, map_prod, map_pow, E_form]
  apply Finset.prod_congr rfl
  intro j _
  rw [eraseVec_eq_self (clean_val (Module.finBasis K (clean x U) j).property)]

private theorem clean_top_D (x : ι) (U : Submodule K (Vec K ι)) :
    D x (top (clean x U)) = 0 := by
  rw [← clean_top_E x U, D_E]

variable [CharP K 3]

omit [DecidableEq ι] in
private theorem top_split {U W : Submodule K (Vec K ι)} {p : Vec K ι}
    (he : W ⊔ K ∙ p = U) (hr : Module.finrank K W + 1 = Module.finrank K U) :
    (∃ a : K, top U = algebraMap K (Q K ι) a * (form p ^ 2 * top W)) ∧
    (∃ a : K, form p ^ 2 * top W = algebraMap K (Q K ι) a * top U) := by
  classical
  let b : Option (Fin (Module.finrank K W)) → Vec K ι := fun j ↦ j.elim p (basisVec W)
  have hb : Submodule.span K (Set.range b) = U := by
    have hspan : Submodule.span K (Set.range (basisVec W) ∪ {p}) = U := by
      rw [Submodule.span_union, basisVec_span, he]
    rw [← hspan]
    congr 1
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      cases j with
      | none => exact Or.inr rfl
      | some j => exact Or.inl ⟨j, rfl⟩
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨some j, rfl⟩
      · exact ⟨none, rfl⟩
  have hcard : Fintype.card (Option (Fin (Module.finrank K W))) =
      Fintype.card (Fin (Module.finrank K U)) := by simpa using hr
  have hprod : topProd b = form p ^ 2 * top W := by simp [top, topProd, b]
  refine ⟨?_, ?_⟩
  · rw [← hprod]
    exact top_transfer b (basisVec U) hcard (fun j ↦ hb ▸ (Module.finBasis K U j).property)
  · rw [← hprod]
    apply top_transfer (basisVec U) b hcard.symm
    rw [basisVec_span]
    exact fun j ↦ hb ▸ Submodule.subset_span (Set.mem_range_self j)

omit [DecidableEq ι] in
private theorem top_ann_mem {U : Submodule K (Vec K ι)} {p : Vec K ι} (h : p ∈ U) :
    form p * top U = 0 := top_ann (basisVec U) (by rwa [basisVec_span])

omit [DecidableEq ι] in
private theorem top_mul_gen {d : ℤ} {U : Submodule K (Vec K ι)} {f : Q K ι}
    (hf : f ∈ Gen d U) : f * top U = 0 := gen_mul_ann hf (fun _ ↦ top_ann_mem)

private theorem erase_top_split {U : Submodule K (Vec K ι)} {x : ι} {p : Vec K ι}
    (hc : Covers (-2) U) (hp : p ∈ U) (hx : p x = 1) :
    (∃ a : K, top (U.map (eraseVec x)) = algebraMap K (Q K ι) a *
      (form (eraseVec x p) ^ 2 * top (clean x U))) := by
  apply (top_split (U := U.map (eraseVec x)) (W := clean x U) (p := eraseVec x p) ?_ ?_).1
  · calc
      _ = (clean x U ⊔ K ∙ p).map (eraseVec x) := by
        rw [Submodule.map_sup, clean_map, Submodule.map_span, Set.image_singleton]
      _ = _ := by rw [clean_split hp hx]
  · rw [finrank_map_restrict _ (eraseVec_ker_inj hc (le_refl _) x)]
    exact clean_rank hp hx

omit [Fintype ι] [DecidableEq ι] [CharP K 3] in
private theorem sq_remainder (x : ι) (u : Q K ι) :
    u ^ 2 = (u + xvar x) * (u - xvar x) := by
  linear_combination xvar_sq (K := K) x

omit [CharP K 3] in
private theorem rem (x : ι) (f : Q K ι) (u : Vec K ι) :
    f = D x f * (form (eraseVec x u) + xvar x) + (E x f - D x f * form (eraseVec x u)) := by
  linear_combination decomp x f

omit [CharP K 3] in
private theorem rem_deg (x : ι) {d : ℤ} {f : Q K ι} (hf : Deg d f) (u : Vec K ι) :
    Deg d (E x f - D x f * form (eraseVec x u)) :=
  (hf.erase x).sub (((hf.coefficient x).mul (Deg.form _)).mono (by omega))

omit [CharP K 3] in
private theorem rem_E (x : ι) (f : Q K ι) (u : Vec K ι) :
    E x (E x f - D x f * form (eraseVec x u)) = E x f - D x f * form (eraseVec x u) := by
  rw [map_sub, map_mul, E_idem, E_D, E_form, eraseVec_eq_self (by simp)]

omit [Fintype ι] [CharP K 3] in
private theorem D_fixed (x : ι) {f : Q K ι} (h : E x f = f) : D x f = 0 := by
  nth_rw 1 [← h]
  exact D_E x f

end Splitting

section RankOne

open Submodule

variable [Fintype ι] [DecidableEq ι] [CharP K 3]

private def OneA (k : ℕ) : Prop := ∀ (u : Vec K ι), 2 * k + 2 ≤ (vsupp u).card →
  ∀ f : Q K ι, Deg k f → f * form u ^ 2 = 0 → ∃ g : Q K ι, Deg ((k : ℤ) - 1) g ∧ f = g * form u

private def OneB (k : ℕ) : Prop := ∀ (u : Vec K ι), 2 * k + 1 ≤ (vsupp u).card →
  ∀ f : Q K ι, Deg k f → f * form u = 0 → ∃ g : Q K ι, Deg ((k : ℤ) - 2) g ∧ f = g * form u ^ 2

omit [CharP K 3] in
private theorem normalVector (u : Vec K ι) (h : 0 < (vsupp u).card) :
    ∃ (x : ι) (v : Vec K ι) (a : K), v x = 1 ∧ 0 < (vsupp u).card ∧
      (vsupp (eraseVec x v)).card + 1 = (vsupp u).card ∧ a ≠ 0 ∧
      u = a • v := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  let a := u x
  have ha : a ≠ 0 := mem_vsupp.mp hx
  let v := a⁻¹ • u
  have hs : vsupp v = vsupp u := by
    ext j
    simp [v, ha]
  refine ⟨x, v, a, ?_, h, ?_, ha, ?_⟩
  · change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha
  · rw [vsupp_erase, hs]
    exact Finset.card_erase_add_one hx
  · dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

omit [Fintype ι] [DecidableEq ι] [CharP K 3] in
private theorem mul_scalar_zero {a : K} (ha : a ≠ 0) {t : Q K ι}
    (h : algebraMap K (Q K ι) a * t = 0) : t = 0 := by
  have hi : algebraMap K (Q K ι) a⁻¹ * algebraMap K (Q K ι) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  linear_combination (algebraMap K (Q K ι) a⁻¹) * h - t * hi

omit [DecidableEq ι] in
private theorem OneA_from_B (k : ℕ) (ih : OneB (K := K) (ι := ι) k) :
    OneA (K := K) (ι := ι) k := by
  classical
  intro u hcard f hf hker
  obtain ⟨x, v, a, hx, _, hcount, ha, huv⟩ := normalVector u (by omega)
  let w := form (eraseVec x v)
  let e := E x f - D x f * w
  have hform : form v = w + xvar x := form_expand hx
  have he : E x (form v) = w := E_form x v
  have hd : D x (form v) = 1 := by simp only [D_form, hx, map_one]
  have h : f * form v ^ 2 = 0 := by
    apply mul_scalar_zero (pow_ne_zero 2 ha)
    rw [huv, map_smul, q_smul, mul_pow, ← map_pow] at hker
    simpa only [mul_left_comm] using hker
  have hzero : e * w = 0 := by
    have hh := congrArg (D x) h
    simp only [pow_two, D_mul, map_mul, map_zero, he, hd, mul_one, one_mul] at hh
    dsimp only [e]
    linear_combination -hh + E x f * w * (two_q (K := K) (ι := ι))
  obtain ⟨g, hg, hg_eq⟩ := ih (eraseVec x v) (by omega) e (rem_deg x hf v) hzero
  let m := D x f + g * (w - xvar x)
  have hm : Deg ((k : ℤ) - 1) m := (hf.coefficient x).add
    ((hg.mul ((Deg.form _).sub (Deg.X x))).mono (by omega))
  have hf_eq : f = m * form v := by
    rw [hform, rem x f v]
    change _ + e = m * _
    rw [hg_eq, sq_remainder x w]
    dsimp only [m]
    ring
  refine ⟨a⁻¹ • m, deg_smul hm _, ?_⟩
  rw [huv, map_smul, q_smul a, q_smul a⁻¹, hf_eq]
  have ha' : algebraMap K (Q K ι) a⁻¹ * algebraMap K (Q K ι) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  linear_combination -(m * form v) * ha'

omit [DecidableEq ι] in
private theorem OneB_from_A (k : ℕ)
    (ih : ∀ j < k, OneA (K := K) (ι := ι) j) : OneB (K := K) (ι := ι) k := by
  classical
  intro u hcard f hf hker
  obtain ⟨x, v, a, hx, _, hcount, ha, huv⟩ := normalVector u (by omega)
  let w := form (eraseVec x v)
  have hform : form v = w + xvar x := form_expand hx
  have he : E x (form v) = w := E_form x v
  have hd : D x (form v) = 1 := by simp only [D_form, hx, map_one]
  have h : f * form v = 0 := by
    apply mul_scalar_zero ha
    rw [huv, map_smul, q_smul] at hker
    simpa only [mul_left_comm] using hker
  have hD : E x f + D x f * w = 0 := by
    simpa only [D_mul, he, hd, mul_one, map_zero] using congrArg (D x) h
  have hE : E x f * w = 0 := by simpa only [map_mul, he, map_zero] using congrArg (E x) h
  have hker' : D x f * w ^ 2 = 0 := by linear_combination w * hD - hE
  have hd' : ∃ g : Q K ι, Deg ((k : ℤ) - 2) g ∧ D x f = g * w := by
    cases k with
    | zero =>
      have hzero := (hf.coefficient x).eq_zero (by norm_num)
      exact ⟨0, Deg.zero _, by rw [hzero, zero_mul]⟩
    | succ k =>
      have hf' : Deg (k : ℤ) (D x f) := (hf.coefficient x).mono (by omega)
      obtain ⟨g, hg, hge⟩ := ih k (by omega) (eraseVec x v) (by omega) (D x f) hf' hker'
      exact ⟨g, hg.mono (by omega), hge⟩
  obtain ⟨g, hg, hge⟩ := hd'
  have hfg : f = -g * form v ^ 2 := by
    have hdec := decomp x f
    rw [hge] at hD hdec
    rw [hform]
    linear_combination hdec + hD + g * xvar_sq (K := K) x +
      g * w * xvar x * (three_q (K := K) (ι := ι))
  refine ⟨(a⁻¹ ^ 2) • (-g), deg_smul hg.neg _, ?_⟩
  rw [huv, map_smul, q_smul a, mul_pow, q_smul (a⁻¹ ^ 2), hfg]
  have ha' : algebraMap K (Q K ι) (a⁻¹ ^ 2) * (algebraMap K (Q K ι) a) ^ 2 = 1 := by
    rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]
  linear_combination (g * form v ^ 2) * ha'

omit [DecidableEq ι] in
private theorem one_pair (k : ℕ) : OneB (K := K) (ι := ι) k ∧ OneA (K := K) (ι := ι) k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have h := OneB_from_A (K := K) (ι := ι) k (fun j hj ↦ (ih j hj).2)
    exact ⟨h, OneA_from_B k h⟩

end RankOne

section RankInduction

open Submodule

variable [Fintype ι] [DecidableEq ι] [CharP K 3] [Infinite K]

private def CaseA (r k : ℕ) : Prop := ∀ U : Submodule K (Vec K ι), Module.finrank K U = r →
  Covers (2 * (k : ℤ) - 2) U → ∀ f : Q K ι, Deg k f → f * top U = 0 → f ∈ Gen k U

private def CaseB (r k : ℕ) : Prop := ∀ U : Submodule K (Vec K ι), Module.finrank K U = r →
  Covers (2 * (k : ℤ) - 3) U → ∀ f : Q K ι, Deg (2 * (r : ℤ) - 2 + k) f →
  (∀ u ∈ U, f * form u = 0) → ∃ g : Q K ι, Deg ((k : ℤ) - 2) g ∧ f = g * top U

omit [DecidableEq ι] [Infinite K] in
private theorem rankOne_cases (k : ℕ) :
    CaseB (K := K) (ι := ι) 1 k ∧ CaseA (K := K) (ι := ι) 1 k := by
  have hreduce (U : Submodule K (Vec K ι)) (hr : Module.finrank K U = 1) :
      ∃ u ∈ U, u ≠ 0 ∧ K ∙ u = U ∧
        (∃ a : K, top U = algebraMap K (Q K ι) a * form u ^ 2) ∧
        (∃ b : K, form u ^ 2 = algebraMap K (Q K ι) b * top U) := by
    obtain ⟨x, u, hu, hux⟩ := pivot (by omega : 0 < Module.finrank K U)
    have hne : u ≠ 0 := fun he ↦ by simp [he] at hux
    have hspan : K ∙ u = U := Submodule.eq_of_le_of_finrank_le
      (span_le.mpr (Set.singleton_subset_iff.mpr hu)) (by rw [finrank_span_singleton hne, hr])
    have h := top_split (U := U) (W := ⊥) (p := u) (by simpa using hspan) (by simp [hr])
    refine ⟨u, hu, hne, hspan, ?_⟩
    have h0 : top (⊥ : Submodule K (Vec K ι)) = 1 := by unfold top topProd; simp
    simpa only [h0, mul_one] using h
  constructor
  · intro U hr hc f hf hker
    obtain ⟨u, hu, h0, _, _, b, hb⟩ := hreduce U hr
    have hs := hc.vec hu h0
    have hdeg : Deg (k : ℤ) f := hf.mono (by omega)
    obtain ⟨g, hg, he⟩ := (one_pair k).1 u (by omega) f hdeg (hker u hu)
    refine ⟨b • g, deg_smul hg _, ?_⟩
    rw [he, hb, q_smul]
    ring
  · intro U hr hc f hf hker
    obtain ⟨u, hu, h0, _, _, b, hb⟩ := hreduce U hr
    have hs := hc.vec hu h0
    have hz : f * form u ^ 2 = 0 := by rw [hb, mul_left_comm, hker, mul_zero]
    obtain ⟨g, hg, he⟩ := (one_pair k).2 u (by omega) f hf hz
    rw [he]
    exact gen_single hg hu

omit [Fintype ι] [CharP K 3] [Infinite K] in
private theorem erase_split_vec {U : Submodule K (Vec K ι)} {p : Vec K ι} {x : ι}
    (hp : p ∈ U) (hx : p x = 1) :
    clean x U ⊔ K ∙ eraseVec x p = U.map (eraseVec x) := by
  calc
    _ = (clean x U ⊔ K ∙ p).map (eraseVec x) := by
      rw [Submodule.map_sup, clean_map, Submodule.map_span, Set.image_singleton]
    _ = _ := by rw [clean_split hp hx]

omit [DecidableEq ι] [Infinite K] in
private theorem caseA_step (r k : ℕ) (hrp : 1 ≤ r) (ia : CaseA (K := K) (ι := ι) r k)
    (ib : CaseB (K := K) (ι := ι) (r + 1) k) : CaseA (K := K) (ι := ι) (r + 1) k := by
  classical
  intro U hr hc f hf hker
  obtain ⟨x, p, hp, hx⟩ := pivot (by omega : 0 < Module.finrank K U)
  let W := clean x U
  let T := top W
  let w := form (eraseVec x p)
  let g := E x f - D x f * w
  have hW : Module.finrank K W = r := by
    have hh : Module.finrank K W + 1 = Module.finrank K U := clean_rank hp hx
    omega
  have hform : form p = w + xvar x := form_expand hx
  have hf_eq : f = D x f * form p + g := by rw [hform]; exact rem x f p
  have hg : Deg (k : ℤ) g := rem_deg x hf p
  have hgE : E x g = g := rem_E x f p
  have hpT : f * (form p ^ 2 * T) = 0 := by
    obtain ⟨a, ha⟩ := (top_split (clean_split hp hx) (clean_rank hp hx)).2
    rw [ha, mul_left_comm, hker, mul_zero]
  have hgp : g * (form p ^ 2 * T) = 0 := by
    rw [hf_eq, add_mul] at hpT
    have h := form_cube p
    linear_combination hpT - D x f * T * h
  have hgw : g * T * w = 0 := by
    have h := congrArg (D x) hgp
    have hD : D x (form p) = 1 := by simp only [D_form, hx, map_one]
    have hET : E x T = T := clean_top_E x U
    have hDT : D x T = 0 := clean_top_D x U
    have hEp : E x (form p) = w := E_form x p
    simp only [pow_two, D_mul, map_mul, hEp, hD, hET, hDT,
      D_fixed x hgE, hgE, map_zero, mul_zero, one_mul, mul_one, zero_add] at h
    linear_combination -h + g * T * w * (two_q (K := K) (ι := ι))
  have hT : ∀ u ∈ W, g * T * form u = 0 := by
    intro u hu
    have h := top_ann_mem hu
    linear_combination g * h
  let U' := U.map (eraseVec x)
  have hsmall : Covers (-2) U := hc.mono le_rfl (by omega)
  have hU' : Module.finrank K U' = r + 1 :=
    (finrank_map_restrict _ (eraseVec_ker_inj hsmall (le_refl _) x)).trans hr
  have hc' : Covers (2 * (k : ℤ) - 3) U' :=
    (hc.erase (by omega) x).mono le_rfl (by omega)
  have hdegT : Deg (2 * (r : ℤ)) T := by
    unfold T top topProd
    rw [← hW]
    have haux (s : Finset (Fin (Module.finrank K W))) :
        Deg (2 * (s.card : ℤ)) (∏ j ∈ s, form (basisVec W j) ^ 2) := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using Deg.C (ι := ι) (1 : K)
      | insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.card_insert_of_notMem hjs, pow_two]
        exact (((Deg.form _).mul (Deg.form _)).mul ih).mono (by omega)
    simpa only [Finset.card_univ, Fintype.card_fin] using haux Finset.univ
  have hann : ∀ u ∈ U', (g * T) * form u = 0 := by
    change ∀ u ∈ U.map (eraseVec x), _
    rw [← erase_split_vec hp hx]
    intro u hu
    obtain ⟨v, hv, qv, hqv, he⟩ := Submodule.mem_sup.mp hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hqv
    rw [← he, map_add, map_smul, q_smul, mul_add, hT v hv, zero_add]
    linear_combination (algebraMap K (Q K ι) c) * hgw
  obtain ⟨z, hz, hz_eq⟩ := ib U' hU' hc' (g * T) ((hg.mul hdegT).mono (by omega)) hann
  obtain ⟨a, ha⟩ := erase_top_split hsmall hp hx
  have hminus : (g - (a • z) * w ^ 2) * T = 0 := by
    rw [ha] at hz_eq
    rw [q_smul]
    linear_combination hz_eq
  have hwdeg : Deg 1 w := Deg.form _
  have hw2 : Deg 2 (w ^ 2) := by rw [pow_two]; exact hwdeg.mul hwdeg
  have hdeg : Deg (k : ℤ) (g - (a • z) * w ^ 2) :=
    hg.sub (((deg_smul hz a).mul hw2).mono (by omega))
  have hgenW := ia W hW (hc.mono inf_le_left le_rfl) _ hdeg hminus
  have hcprod : (a • z) * w ^ 2 ∈ Gen (k : ℤ) U := by
    rw [sq_remainder x, ← hform, mul_comm (form p), ← mul_assoc]
    exact gen_single (((deg_smul hz a).mul ((Deg.form _).sub (Deg.X x))).mono (by omega)) hp
  have hn := (Gen (k : ℤ) U).add_mem (gen_mono (show W ≤ U from inf_le_left) hgenW) hcprod
  rw [sub_add_cancel] at hn
  rw [hf_eq]
  exact (Gen (k : ℤ) U).add_mem (gen_single (hf.coefficient x) hp) hn

omit [CharP K 3] [Infinite K] in
private theorem shift_cover {U V : Submodule K (Vec K ι)} {c : ℤ} {x : ι} {v : Vec K ι}
    (hVU : V ≤ U) (hc : Covers c U) (hcV : Covers (c + 4) V)
    (hv : v ∈ clean x U) (hn : v ∉ clean x V) :
    let Y := clean x V ⊔ K ∙ (v + delta x)
    (Y.map (eraseVec x) = clean x V ⊔ K ∙ v) ∧
      Module.finrank K Y = Module.finrank K (clean x V) + 1 ∧ Covers (c + 1) Y := by
  classical
  let W := clean x V
  let Y := W ⊔ K ∙ (v + delta x)
  have hdx : ((v + delta x : Vec K ι) x) = 1 := by simp [clean_val hv]
  have hxv : eraseVec x (v + delta x) = v := by
    rw [map_add, eraseVec_eq_self (clean_val hv)]
    have hd : eraseVec x (delta (K := K) x) = 0 := by
      funext j
      by_cases hj : j = x <;> simp [hj]
    rw [hd, add_zero]
  have hm : Y.map (eraseVec x) = W ⊔ K ∙ v := by
    rw [Submodule.map_sup, clean_map, Submodule.map_span, Set.image_singleton, hxv]
  have hnot : v + delta x ∉ W := fun he ↦ by
    have := clean_val he
    rw [hdx] at this
    exact one_ne_zero this
  have hr := Submodule.finrank_sup_span_singleton hnot
  refine ⟨hm, hr, ?_⟩
  have hi : Function.Injective ((eraseVec x).comp Y.subtype) := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨w, hw, z, hz, he⟩ := Submodule.mem_sup.mp u.property
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have he' : w + a • v = 0 := by
      have h := congrArg (eraseVec x) he
      change eraseVec x (u : Vec K ι) = 0 at hu
      rw [map_add, map_smul, hxv, eraseVec_eq_self (clean_val hw), hu] at h
      exact h
    have ha : a = 0 := by
      by_contra ha
      apply hn
      have hw' : a • v ∈ W := by rw [eq_neg_of_add_eq_zero_right he']; exact W.neg_mem hw
      have h := W.smul_mem a⁻¹ hw'
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
    have hw0 : w = 0 := by simpa [ha] using he'
    apply Subtype.ext
    change (u : Vec K ι) = 0
    simpa [ha, hw0] using he.symm
  intro I hI hpI
  by_cases hxs : x ∈ supp I
  · have hsub : I.map (eraseVec x) ≤ U := by
      exact (Submodule.map_mono hI).trans (hm.symm ▸ sup_le (inf_le_left.trans hVU)
        (span_le.mpr (Set.singleton_subset_iff.mpr hv.1)))
    have hii : Function.Injective ((eraseVec x).comp I.subtype) := by
      intro a b hab
      have hh : (⟨a, hI a.property⟩ : Y) = ⟨b, hI b.property⟩ := hi hab
      exact Subtype.ext (congrArg (fun a : Y ↦ (a : Vec K ι)) hh)
    have hri := finrank_map_restrict _ hii
    have hs := hc (I.map (eraseVec x)) hsub (hri.symm ▸ hpI)
    rw [hri, supp_map_erase] at hs
    have := Finset.card_erase_add_one hxs
    omega
  · have hIV : I ≤ V := by
      intro u hu
      obtain ⟨w, hw, z, hz, he⟩ := Submodule.mem_sup.mp (hI hu)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hzero : u x = 0 := by
        by_contra hn
        exact hxs (mem_supp.mpr ⟨u, hu, hn⟩)
      have hh := congrFun he x
      change w x + a * (v + delta x : Vec K ι) x = u x at hh
      rw [clean_val hw, hdx, mul_one, zero_add, hzero] at hh
      rw [hh, zero_smul, add_zero] at he
      exact he ▸ hw.1
    have hs := hcV I hIV hpI
    omega

-- First advance the annihilator-of-linear-forms assertion, then the assertion for the top product.
omit [DecidableEq ι] in
private theorem caseB_step (r k : ℕ) (hrp : 1 ≤ r)
    (ia : ∀ j, CaseA (K := K) (ι := ι) r j)
    (ib : CaseB (K := K) (ι := ι) r (k + 2))
    (prev : ∀ j < k, CaseA (K := K) (ι := ι) (r + 1) j) :
    CaseB (K := K) (ι := ι) (r + 1) k := by
  classical
  intro U hr hc f hf hann
  obtain ⟨V, hVU, hVr, hcV⟩ := genericHyperplane hc (by omega : 0 < Module.finrank K U)
  have hrV : Module.finrank K V = r := by omega
  obtain ⟨x, p, hp, hx⟩ := pivot (by omega : 0 < Module.finrank K V)
  obtain ⟨v, hv, hvn, hclean⟩ := clean_extend hVU hVr hp hx
  let W := clean x V
  let T := top W
  let w := form (eraseVec x p)
  let b := form v
  let P := form p ^ 2 * T
  have hpU : p ∈ U := hVU hp
  have hform : form p = w + xvar x := form_expand hx
  have hU : V ⊔ K ∙ v = U := by
    calc
      V ⊔ K ∙ v = (W ⊔ K ∙ v) ⊔ K ∙ p := by rw [← clean_split hp hx]; ac_rfl
      _ = U := by rw [hclean, clean_split hpU hx]
  have hwr := clean_rank hp hx
  obtain ⟨cV, hcVtop⟩ := (top_split (clean_split hp hx) hwr).1
  obtain ⟨cV', hcV'top⟩ := (top_split (clean_split hp hx) hwr).2
  have hPa : form p * P = 0 := by
    have h := form_cube p
    dsimp only [P]
    linear_combination T * h
  obtain ⟨g₀, hg₀, hf₀⟩ := ib V hrV
    (hcV.mono le_rfl (by omega)) f (hf.mono (by omega)) (fun u hu ↦ hann u (hVU hu))
  let g₁ := cV • g₀
  have hg₁ : Deg (k : ℤ) g₁ := deg_smul (hg₀.mono (by omega)) cV
  have hfg₁ : f = g₁ * P := by
    rw [hf₀, hcVtop]
    change _ = (cV • g₀) * P
    rw [q_smul]
    ring
  let g := E x g₁ - D x g₁ * w
  have hg : Deg (k : ℤ) g := rem_deg x hg₁ p
  have hgE : E x g = g := rem_E x g₁ p
  have hfg : f = g * P := by
    have hb : g₁ = D x g₁ * form p + g := by rw [hform]; exact rem x g₁ p
    rw [hfg₁, hb, add_mul, mul_assoc, hPa, mul_zero, zero_add]
  have hvk := hann v hv.1
  have hgbP : (g * b) * P = 0 := by rw [hfg] at hvk; linear_combination hvk
  have hgb : g * b ∈ Gen ((k : ℤ) + 1) V := by
    apply ia (k+1) V hrV (hcV.mono le_rfl (by omega))
    · exact (hg.mul (Deg.form v)).mono (by omega)
    · rw [hcVtop]
      change g * b * (algebraMap K (Q K ι) cV * P) = 0
      rw [mul_left_comm, hgbP, mul_zero]
  cases k with
  | zero =>
    obtain ⟨a, ha⟩ := hg.const
    have h0 : g * b ∈ Gen 1 V := by simpa using hgb
    obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp (gen_one h0)
    have hv' : v ∉ V := fun hvV ↦ hvn ⟨hvV, hv.2⟩
    have ha0 : a = 0 := by
      by_contra hane
      have hu_eq : u = a • v := by
        apply form_inj
        rw [map_smul, q_smul]
        exact he.trans (by rw [ha])
      have hvV : a • v ∈ V := hu_eq ▸ hu
      have hh := V.smul_mem a⁻¹ hvV
      rw [smul_smul, inv_mul_cancel₀ hane, one_smul] at hh
      exact hv' hh
    refine ⟨0, Deg.zero _, ?_⟩
    rw [hfg, ha, ha0, map_zero, zero_mul, zero_mul]
  | succ k =>
    have hprev := prev k (Nat.lt_succ_self k)
    have hEw : E x w = w := E_form x _ |>.trans (congrArg form (eraseVec_eq_self (by simp)))
    have hEb : E x b = b := (E_form x v).trans (congrArg form (eraseVec_eq_self (clean_val hv)))
    have hDb : D x b = 0 := by simp only [b, D_form, clean_val hv, map_zero]
    have hEp : E x (form p) = w := E_form x p
    have hDp : D x (form p) = 1 := by simp only [D_form, hx, map_one]
    obtain ⟨a, had, z, hz, hgz⟩ := gen_split (by rw [clean_split hp hx]; exact hgb)
    have he := congrArg (E x) hgz
    simp only [map_mul, map_add, hgE, hEb, hEp] at he
    have hd := congrArg (D x) hgz
    simp only [D_mul, map_add, D_fixed x hgE, hgE, hEb, hDb, hEp, hDp,
      mul_one, zero_mul, mul_zero, add_zero] at hd
    have hEz : E x z * T = 0 := top_mul_gen (clean_gen_erase x hz)
    have hDz : D x z * T = 0 := top_mul_gen (clean_gen_deriv x hz)
    have hrel : (g * b + D x a * w ^ 2) * T = 0 := by
      linear_combination T * he - w * T * hd + hEz - w * hDz
    have hrel' : D x a * (w ^ 2 * (b ^ 2 * T)) = 0 := by
      linear_combination b ^ 2 * hrel - g * T * form_cube v
    have hcmin : Covers (-2) U := hc.mono le_rfl (by omega)
    let U' := U.map (eraseVec x)
    have hr' : Module.finrank K U' = r + 1 :=
      (finrank_map_restrict _ (eraseVec_ker_inj hcmin (le_refl _) x)).trans hr
    have hc' : Covers (2 * (k : ℤ) - 2) U' := (hc.erase (by omega) x).mono le_rfl (by omega)
    obtain ⟨aU, haU⟩ := erase_top_split hcmin hpU hx
    have hwr' : Module.finrank K W + 1 = Module.finrank K (clean x U) := by
      have hh := clean_rank hpU hx
      have hw : Module.finrank K W + 1 = Module.finrank K V := hwr
      omega
    obtain ⟨aW, haW⟩ := (top_split hclean hwr').1
    have hAnn : D x a * top U' = 0 := by
      change D x a * top (U.map (eraseVec x)) = 0
      rw [haU, haW]
      linear_combination (algebraMap K (Q K ι) aU * algebraMap K (Q K ι) aW) * hrel'
    have haD : D x a ∈ Gen (k : ℤ) U' := hprev U' hr' hc' _
      ((had.coefficient x).mono (by omega)) hAnn
    have hdecomp : (W ⊔ K ∙ eraseVec x p) ⊔ K ∙ v = U' := by
      calc
        _ = (W ⊔ K ∙ v) ⊔ K ∙ eraseVec x p := by ac_rfl
        _ = _ := by rw [hclean, erase_split_vec hpU hx]
    obtain ⟨c, hcd, z', hz', hc_eq⟩ := gen_split (by rw [hdecomp]; exact haD)
    have hzann : z' * (w ^ 2 * T) = 0 := by
      apply gen_mul_ann hz'
      intro u hu
      obtain ⟨qv, hqv, sv, hsv, he⟩ := Submodule.mem_sup.mp hu
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hsv
      rw [← he, map_add, map_smul, q_smul, add_mul]
      have hh := top_ann_mem hqv
      linear_combination w ^ 2 * hh + algebraMap K (Q K ι) d * T * form_cube (eraseVec x p)
    have hshift0 : (g + c * w ^ 2) * b * T = 0 := by
      rw [hc_eq] at hrel
      linear_combination hrel - hzann
    let Y := W ⊔ K ∙ (v + delta x)
    obtain ⟨hYmap, hYr, hYcov⟩ := shift_cover hVU hc hcV hv hvn
    have hry : Module.finrank K Y = r := by rw [hYr]; omega
    have hsh : form (v + delta x) = b + xvar x := by rw [map_add, form_delta]
    obtain ⟨d, hdtop⟩ := (top_split (U := Y) (W := W) (p := v + delta x) rfl hYr.symm).1
    have hshift : (g + c * w ^ 2) * top Y = 0 := by
      rw [hdtop, hsh]
      linear_combination (algebraMap K (Q K ι) d * (b + 2 * xvar x)) * hshift0 +
        (g + c * w ^ 2) * T * algebraMap K (Q K ι) d * xvar_sq (K := K) x
    have hwD : Deg 1 w := Deg.form _
    have hw2 : Deg 2 (w ^ 2) := by rw [pow_two]; exact hwD.mul hwD
    have hYgen : g + c * w ^ 2 ∈ Gen ((k.succ : ℕ) : ℤ) Y := ia (k+1) Y hry
      (hYcov.mono le_rfl (by omega)) _
      (hg.add ((hcd.mul hw2).mono (by omega))) hshift
    have hG := gen_erase x hYgen
    rw [show Y.map (eraseVec x) = clean x U from hYmap.trans hclean, map_add, map_mul,
      map_pow, hgE, hEw] at hG
    have hcm : E x c * w ^ 2 ∈ Gen ((k.succ : ℕ) : ℤ) U := by
      rw [sq_remainder x, ← hform, mul_comm (form p), ← mul_assoc]
      exact gen_single ((((hcd.erase x).mul ((Deg.form _).sub (Deg.X x)))).mono (by omega)) hpU
    have hG' := (Gen ((k.succ : ℕ) : ℤ) U).sub_mem
      (gen_mono (show clean x U ≤ U from inf_le_left) hG) hcm
    rw [add_sub_cancel_right] at hG'
    obtain ⟨h, hh, z'', hz'', hg_eq⟩ := gen_split (by rw [hU]; exact hG')
    have hz0 : z'' * P = 0 := by
      change z'' * (form p ^ 2 * T) = 0
      rw [hcV'top]
      linear_combination algebraMap K (Q K ι) cV' * top_mul_gen hz''
    have hf_eq : f = h * b * P := by rw [hfg, hg_eq, add_mul, hz0, add_zero]
    have hhb : h * (b ^ 2 * P) = 0 := by rw [hf_eq] at hvk; linear_combination hvk
    obtain ⟨e, hetop⟩ := (top_split hU hVr).1
    have hhh : h * top U = 0 := by
      rw [hetop, hcVtop]
      linear_combination (algebraMap K (Q K ι) e * algebraMap K (Q K ι) cV) * hhb
    have hlast : h ∈ Gen (k : ℤ) U := hprev U hr (hc.mono le_rfl (by omega)) _
      (hh.mono (by omega)) hhh
    obtain ⟨d', hd', t, ht, ht_eq⟩ := gen_split (by rw [hU]; exact hlast)
    have ht0 : t * P = 0 := by
      change t * (form p ^ 2 * T) = 0
      rw [hcV'top]
      linear_combination algebraMap K (Q K ι) cV' * top_mul_gen ht
    obtain ⟨e', he'⟩ := (top_split hU hVr).2
    refine ⟨(e' * cV') • d', (deg_smul hd' _).mono (by omega), ?_⟩
    have hfact : f = d' * (b ^ 2 * P) := by
      rw [hf_eq, ht_eq]
      linear_combination b * ht0
    rw [hfact]
    change d' * (b ^ 2 * (form p ^ 2 * T)) = _
    rw [hcV'top, q_smul, map_mul]
    linear_combination d' * algebraMap K (Q K ι) cV' * he'

-- Yang Yu, Theorem 7. The outer induction is on rank, the inner one on degree.
omit [DecidableEq ι] in
private theorem rank_cases (r : ℕ) (hr : 0 < r) (k : ℕ) :
    CaseB (K := K) (ι := ι) r k ∧ CaseA (K := K) (ι := ι) r k := by
  induction r generalizing k with
  | zero => omega
  | succ r ih =>
    by_cases he : r = 0
    · subst r
      exact rankOne_cases k
    have hpos : 0 < r := by omega
    induction k using Nat.strong_induction_on with
    | ind k hk =>
      have hb := caseB_step r k (by omega) (fun j ↦ (ih hpos j).2) (ih hpos (k + 2)).1
        (fun j hj ↦ (hk j hj).2)
      exact ⟨hb, caseA_step r k (by omega) (ih hpos k).2 hb⟩

end RankInduction

section FourCubes

open Submodule

private abbrev F := ZMod 3
private abbrev L := RatFunc F

private instance : Infinite L :=
  Infinite.of_injective _ (FaithfulSMul.algebraMap_injective (Polynomial F) L)

private abbrev col {n : ℕ} (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (j : Fin n) : Fin n → F :=
  e (Pi.single j 1)

private theorem col_sum {n : ℕ} (e : (Fin n → F) ≃ₗ[F] (Fin n → F)) (v : Fin n → F) :
    ∑ j, v j • col e j = e v := by
  simp only [col, ← map_smul, ← map_sum]
  congr 1
  simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun F (Fin n)).sum_repr v

private def rows {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    (Fin n → L) →ₗ[L] (Fin 4 × Fin n → L) where
  toFun a t := ∑ i, a i * algebraMap F L (col (e t.1) t.2 i)
  map_add' a b := by ext t; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem recover_row {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F))
    (a : Fin n → L) (b : Fin 4) (i : Fin n) :
    (∑ j, rows e a (b,j) * algebraMap F L (col (e b).symm i j)) = a i := by
  change (∑ j, (∑ k, a k * algebraMap F L (col (e b) j k)) *
    algebraMap F L (col (e b).symm i j)) = _
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have h (k : Fin n) :
      ∑ j, col (e b) j k * col (e b).symm i j = (Pi.single i (1 : F) : Fin n → F) k := by
    have hh := congrFun (col_sum (e b) (col (e b).symm i)) k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, LinearEquiv.apply_symm_apply,
      mul_comm] using hh
  simp only [← Finset.mul_sum, ← map_mul, ← map_sum, h]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · simp

private theorem block_inj {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) (b : Fin 4) :
    Function.Injective (fun a : Fin n → L ↦ fun j ↦ rows e a (b,j)) := by
  intro a c h
  funext i
  rw [← recover_row e a b i, ← recover_row e c b i]
  apply Finset.sum_congr rfl
  intro j _
  rw [show rows e a (b,j) = rows e c (b,j) from congrFun h j]

private theorem rows_inj {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    Function.Injective (rows e) := fun _ _ h ↦ block_inj e 0 (congrArg (fun f j ↦ f (0,j)) h)

private theorem rows_cover {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    Covers 0 (LinearMap.range (rows e)) := by
  classical
  intro W hW _
  let block (b : Fin 4) := (Finset.univ : Finset (Fin n)).filter (fun j ↦ (b,j) ∈ supp W)
  have hbound (b : Fin 4) : Module.finrank L W ≤ (block b).card := by
    let π : W →ₗ[L] (↥(block b) → L) :=
      LinearMap.pi (fun j ↦ (LinearMap.proj (b,j.val)).comp W.subtype)
    have hi : Function.Injective π := by
      intro a c hac
      obtain ⟨u, hu⟩ := hW a.property
      obtain ⟨v, hv⟩ := hW c.property
      apply Subtype.ext
      have he : u = v := by
        apply block_inj e b
        funext j
        change rows e u (b,j) = rows e v (b,j)
        rw [hu, hv]
        by_cases hj : j ∈ block b
        · exact congrFun hac ⟨j, hj⟩
        · have hz (q : W) : (q : Fin 4 × Fin n → L) (b,j) = 0 := by
            by_contra hn
            exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,
              mem_supp.mpr ⟨q, q.property, hn⟩⟩)
          rw [hz a, hz c]
      exact hu.symm.trans (he ▸ hv)
    simpa using LinearMap.finrank_le_finrank_of_injective hi
  have hcard : (supp W).card = ∑ b, (block b).card := by
    have he (b : Fin 4) : (∑ j : Fin n, if (b,j) ∈ supp W then (1 : ℕ) else 0) =
        (block b).card := by
      dsimp only [block]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    calc
      (supp W).card = ∑ t : Fin 4 × Fin n, if t ∈ supp W then (1 : ℕ) else 0 := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.univ_inter]
      _ = _ := by rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun b _ ↦ he b
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun b _ ↦ hbound b)
  rw [← hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  omega

private theorem rows_top_ne {n : ℕ} (hn : 0 < n)
    (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) :
    topProd (fun i : Fin n ↦ rows e (Pi.single i 1)) ≠ 0 := by
  classical
  let U := LinearMap.range (rows e)
  have hr : Module.finrank L U = n := by
    rw [LinearMap.finrank_range_of_inj (rows_inj e)]
    simp
  have hc := (rows_cover e).mono (V := U) le_rfl (show (-2 : ℤ) ≤ 0 by omega)
  have htop : top U ≠ 0 := by
    intro h
    have hd : Deg (0 : ℤ) (1 : Q L (Fin 4 × Fin n)) := by simpa using Deg.C (1 : L)
    have he := (rank_cases n hn 0).2 U hr (by simpa using hc) 1 hd (by rw [h, mul_zero])
    have h1 := gen_eq_zero (by omega) he
    exact one_ne_zero (by simpa only [map_one, map_zero] using congrArg aug h1)
  let b : Fin n → Vec L (Fin 4 × Fin n) := fun i ↦ rows e (Pi.single i 1)
  have hb : Submodule.span L (Set.range b) = U := by
    have h := (Pi.basisFun L (Fin n)).span_eq
    have h' := congrArg (Submodule.map (rows e)) h
    rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h'
    simpa only [b, U, Function.comp_def, Pi.basisFun_apply] using h'
  obtain ⟨c, h⟩ := top_transfer b (basisVec U) (by simpa using hr.symm)
    (fun j ↦ by rw [hb]; exact (Module.finBasis L U j).property)
  intro hz
  apply htop
  rw [show top U = _ from h, show topProd b = 0 from hz, mul_zero]

private def rowForm {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) (i : Fin n) :
    MvPolynomial (Fin 4 × Fin n) F := formPoly (fun t ↦ col (e t.1) t.2 i)

private theorem rowForm_map {n : ℕ} (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) (i : Fin n) :
    MvPolynomial.map (algebraMap F L) (rowForm e i) = formPoly (rows e (Pi.single i 1)) := by
  change MvPolynomial.map _ (∑ t : Fin 4 × Fin n, C (col (e t.1) t.2 i) * X t) =
    ∑ t : Fin 4 × Fin n, C (rows e (Pi.single i 1) t) * X t
  simp only [map_sum, map_mul, map_C, map_X]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  congr 2
  change _ = ∑ j, (Pi.single i (1 : L) : Fin n → L) j * algebraMap F L (col (e t.1) t.2 j)
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem q_squarefree_coeff {R τ : Type*} [Field R] {p : MvPolynomial τ R}
    (h : q p ≠ 0) : ∃ d : τ →₀ ℕ, (∀ j, d j ≤ 1) ∧ p.coeff d ≠ 0 := by
  classical
  by_contra! hn
  apply h
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have he : sqIdeal R τ =
      Ideal.span ((fun m ↦ monomial m (1 : R)) '' Set.range (fun j : τ ↦ Finsupp.single j 2)) := by
    unfold sqIdeal
    congr 1
    ext f
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨Finsupp.single j 2, Set.mem_range_self j, ?_⟩
      exact X_pow_eq_monomial.symm
    · rintro ⟨m, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, X_pow_eq_monomial⟩
  rw [he, MvPolynomial.mem_ideal_span_monomial_image]
  intro d hd
  obtain ⟨j, hj⟩ : ∃ j, 2 ≤ d j := by
    by_contra! he
    exact (mem_support_iff.mp hd) (hn d (fun j ↦ by have := he j; omega))
  exact ⟨Finsupp.single j 2, Set.mem_range_self _, Finsupp.single_le_iff.mpr hj⟩

-- Only the highest-degree terms of the indicators can contribute to the chosen coefficient.
private theorem degree_prod_sub_prod {R τ J : Type*} [Field R] (s : Finset J)
    (A B : J → MvPolynomial τ R) (hA : ∀ j ∈ s, (A j).totalDegree ≤ 2)
    (hB : ∀ j ∈ s, (B j).totalDegree ≤ 2) (hD : ∀ j ∈ s, (A j - B j).totalDegree ≤ 1) :
    ((∏ j ∈ s, A j) - ∏ j ∈ s, B j).totalDegree ≤ 2 * s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, i ∈ insert j s := fun i hi ↦ Finset.mem_insert_of_mem hi
    have hdiff := ih (fun i hi ↦ hA i (hs _ hi)) (fun i hi ↦ hB i (hs _ hi))
      (fun i hi ↦ hD i (hs _ hi))
    have hprod : (∏ i ∈ s, A i).totalDegree ≤ 2 * s.card := by
      have hh := totalDegree_finsetProd s A
      refine hh.trans ?_
      simpa [Finset.sum_const, Nat.mul_comm] using
        (Finset.sum_le_sum fun i hi ↦ hA i (hs _ hi))
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    rw [show A j * (∏ i ∈ s, A i) - B j * (∏ i ∈ s, B i) =
      (A j - B j) * (∏ i ∈ s, A i) + B j * ((∏ i ∈ s, A i) - ∏ i ∈ s, B i) by ring]
    apply (totalDegree_add _ _).trans
    apply max_le
    · have hh := totalDegree_mul (A j - B j) (∏ i ∈ s, A i)
      have hd := hD j (Finset.mem_insert_self _ _)
      omega
    · by_cases he : s = ∅
      · simp [he]
      · have hh := totalDegree_mul (B j) ((∏ i ∈ s, A i) - ∏ i ∈ s, B i)
        have hd := hB j (Finset.mem_insert_self _ _)
        have hs' := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        omega

private theorem fourBinary {n : ℕ} (hn : 0 < n)
    (e : Fin 4 → (Fin n → F) ≃ₗ[F] (Fin n → F)) (v : Fin n → F) :
    ∃ a : Fin 4 × Fin n → F, (∀ t, a t = 0 ∨ a t = 1) ∧
      v = ∑ b, e b (fun j ↦ a (b,j)) := by
  classical
  let T := ∏ i, rowForm e i ^ 2
  have hT : q (MvPolynomial.map (algebraMap F L) T) ≠ 0 := by
    simp only [T, map_prod, map_pow, rowForm_map]
    exact rows_top_ne hn e
  obtain ⟨d, hd, hdc⟩ := q_squarefree_coeff hT
  have hcoeff : T.coeff d ≠ 0 := by
    intro h
    apply hdc
    rw [coeff_map, h, map_zero]
  have he : T.IsHomogeneous (2 * n) := by
    have h (i : Fin n) : (rowForm e i).IsHomogeneous 1 := by
      apply IsHomogeneous.sum
      intro j _
      exact isHomogeneous_C_mul_X _ _
    simpa [T, Nat.mul_comm] using IsHomogeneous.prod Finset.univ (fun i ↦ rowForm e i ^ 2)
      (fun _ ↦ 2) (fun i _ ↦ by simpa using (h i).pow 2)
  have hdeg : d.degree = 2 * n :=
    (he.degree_eq_sum_deg_support (mem_support_iff.mpr hcoeff)).symm
  let A (i : Fin n) := 1 - (rowForm e i - C (v i)) ^ 2
  let B (i : Fin n) := -(rowForm e i ^ 2)
  let P := ∏ i, A i
  have hL (i : Fin n) : (rowForm e i).totalDegree ≤ 1 := formPoly_degree _
  have hdiff (i : Fin n) : (A i - B i).totalDegree ≤ 1 := by
    have hh : A i - B i = C (1 - (v i)^2) + C (2 * v i) * rowForm e i := by
      dsimp only [A, B]
      simp only [map_mul, map_sub, map_pow, map_one, map_ofNat]
      ring
    rw [hh]
    have hmul := totalDegree_mul (C (2 * v i)) (rowForm e i)
    apply (totalDegree_add _ _).trans
    simp only [totalDegree_C, zero_add, Nat.zero_le, sup_of_le_right] at hmul ⊢
    exact hmul.trans (hL i)
  have hB (i : Fin n) : (B i).totalDegree ≤ 2 := by
    have hz := totalDegree_pow (rowForm e i) 2
    have hl := hL i
    simpa [B] using show (rowForm e i ^ 2).totalDegree ≤ 2 by omega
  have hA (i : Fin n) : (A i).totalDegree ≤ 2 := by
    have hh := totalDegree_add (A i - B i) (B i)
    rw [sub_add_cancel] at hh
    exact hh.trans (max_le ((hdiff i).trans (by decide)) (hB i))
  have hP : P.totalDegree ≤ 2 * n := by
    apply (totalDegree_finsetProd _ _).trans
    simpa [Finset.sum_const, Nat.mul_comm] using
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hA i))
  have hD := degree_prod_sub_prod Finset.univ A B (fun i _ ↦ hA i) (fun i _ ↦ hB i)
    (fun i _ ↦ hdiff i)
  have hcoef : P.coeff d = (∏ i, B i).coeff d := by
    have hsmall : (P - ∏ i, B i).totalDegree < ∑ j ∈ d.support, d j := by
      rw [← Finsupp.degree_apply, hdeg]
      simpa [P, Nat.mul_comm] using lt_of_le_of_lt hD (by simp; omega)
    simpa only [coeff_sub, sub_eq_zero] using coeff_eq_zero_of_totalDegree_lt hsmall
  have hPNZ : P.coeff d ≠ 0 := by
    rw [hcoef, show (∏ i, B i) = C ((-1 : F)^n) * T by
      simp only [B, T, Finset.prod_neg, Finset.card_univ, Fintype.card_fin, map_pow, map_neg,
        map_one]]
    rw [coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hcoeff
  have hdegree : P.totalDegree = d.degree := by
    apply le_antisymm (hdeg ▸ hP)
    exact le_totalDegree (mem_support_iff.mpr hPNZ)
  let S : Finset F := {0, 1}
  obtain ⟨a, ha, hne⟩ := combinatorial_nullstellensatz_exists_eval_ne_zero P d hPNZ hdegree
    (fun _ ↦ S) (fun j ↦ by simpa [S] using Nat.lt_succ_of_le (hd j))
  refine ⟨a, fun j ↦ by simpa [S] using ha j, ?_⟩
  ext i
  have hi : eval a (A i) ≠ 0 := by
    intro h0
    apply hne
    rw [show P = ∏ j, A j from rfl, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hF3 : ∀ z : F, (1 - z^2 ≠ 0) → z = 0 := by decide
  have hi' : eval a (rowForm e i) = v i := sub_eq_zero.mp (hF3 _ (by
    simpa only [A, map_sub, map_one, map_pow, eval_C] using hi))
  rw [← hi']
  change eval a (∑ t : Fin 4 × Fin n, C (col (e t.1) t.2 i) * X t) = _
  simp only [map_sum, map_mul, eval_C, eval_X, Finset.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [← col_sum (e b) (fun j ↦ a (b,j))]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

end FourCubes

end
end Green69

@[expose] public section

namespace MathlibExt.Combinatorics.GreenProblem69Wanted

/-! Source record `UM-00000157-Q001`. -/
/-- **The standard cube in $\mathbb{F}_3^n$.** For $n \in \mathbb{N}$, the standard cube is the set
$\{0, 1\}^n \subseteq \mathbb{F}_3^n$ of vectors each of whose coordinates is $0$ or $1$. -/
def cubeOrigin (n : ℕ) : Set (Fin n → ZMod 3) :=
  { x | ∀ i : Fin n, x i = 0 ∨ x i = 1 }

/-- **Cubes in $\mathbb{F}_3^n$.** A set $A \subseteq \mathbb{F}_3^n$ is a cube if there is an
$\mathbb{F}_3$-linear automorphism $e$ of $\mathbb{F}_3^n$ with $A = e(\{0, 1\}^n)$, the image of
the standard cube $\{0, 1\}^n$ under $e$. -/
def IsCube (n : ℕ) (A : Set (Fin n → ZMod 3)) : Prop :=
  ∃ e : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3),
    A = Set.image (e : (Fin n → ZMod 3) → (Fin n → ZMod 3)) (cubeOrigin n)

/-- **A sumset of $100$ sets equal to $\mathbb{F}_3^n$.** For sets
$A_1, \dots, A_{100} \subseteq \mathbb{F}_3^n$, the property that every $v \in \mathbb{F}_3^n$ can
be written as $v = a_1 + \dots + a_{100}$ with $a_i \in A_i$ for each $i$, that is,
$A_1 + \dots + A_{100} = \mathbb{F}_3^n$. -/
def SumsetEqUniv (n : ℕ) (A : Fin 100 → Set (Fin n → ZMod 3)) : Prop :=
  ∀ v : Fin n → ZMod 3,
    ∃ a : Fin 100 → Fin n → ZMod 3,
      (∀ i, a i ∈ A i) ∧ v = Finset.sum (Finset.univ : Finset (Fin 100)) a

/-- **Green's problem on sums of $100$ cubes in $\mathbb{F}_3^n$.** The statement that for every
$n \ge 1$ and every family $A_1, \dots, A_{100}$ of cubes in $\mathbb{F}_3^n$ (not necessarily
distinct), that is, images of $\{0, 1\}^n$ under linear automorphisms of $\mathbb{F}_3^n$, the
sumset $A_1 + \dots + A_{100}$ is all of $\mathbb{F}_3^n$. -/
def conjecture : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (A : Fin 100 → Set (Fin n → ZMod 3)),
      (∀ i, IsCube n (A i)) → SumsetEqUniv n A

-- Carried source audit `UM-00000157-Q001` (see the Moved/ record).

/--
**Any $100$ cubes sum to all of $\mathbb{F}_3^n$.** For every $n \ge 1$ and every family
$A_1, \dots, A_{100}$ of cubes in $\mathbb{F}_3^n$ (not necessarily distinct), that is, images
of $\{0, 1\}^n$ under linear automorphisms of $\mathbb{F}_3^n$, the sumset
$A_1 + \dots + A_{100}$ is all of $\mathbb{F}_3^n$.

Yang Yu proves that over $\mathbb{F}_3$ the union of any four linear bases is an additive basis,
so any four cubes already sum to $\mathbb{F}_3^n$, and the remaining summands can be taken to be
$0$. Ben Green's author-maintained 100 Open Problems (December 2025) marks this problem, current
Problem 26, solved on that basis; the analogue over $\mathbb{F}_p$ remains open.

Source: Yang Yu, The Permanent
Rank of a Matrix (Part Three) Note on the Additive Basis Conjecture, arXiv:2510.01300v2,
https://arxiv.org/abs/2510.01300v2. Moved from `OpenConjectures/Combinatorics/GreenProblem69`.
-/
public theorem conjecture_holds : conjecture := by
  intro n hn A hA v
  classical
  choose e he using hA
  let emb : Fin 4 ↪ Fin 100 := Fin.castLEEmb (by decide)
  obtain ⟨a, hab, hsum⟩ := Green69.fourBinary hn (fun b ↦ e (emb b)) v
  let s : Fin 4 → Fin n → ZMod 3 := fun i j ↦ a (i, j)
  let z : Fin 100 → Fin n → ZMod 3 := fun i ↦
    if h : i ∈ Set.range emb then s (Classical.choose h) else 0
  have hz (b : Fin 4) : z (emb b) = s b := by
    have h : emb b ∈ Set.range emb := ⟨b, rfl⟩
    rw [show z (emb b) = s (Classical.choose h) from dite_eq_left h]
    exact congrArg s (emb.injective (Classical.choose_spec h))
  refine ⟨fun i ↦ e i (z i), ?_, ?_⟩
  · intro i
    rw [he i]
    refine ⟨z i, ?_, rfl⟩
    change ∀ j : Fin n, z i j = 0 ∨ z i j = 1
    intro j
    by_cases h : i ∈ Set.range emb
    · obtain ⟨b, rfl⟩ := h
      rw [hz]
      exact hab (b, j)
    · change (if h : i ∈ Set.range emb then s (Classical.choose h) else 0) j = 0 ∨ _
      rw [dite_eq_right h]
      exact Or.inl rfl
  · calc
      v = ∑ b, e (emb b) (s b) := hsum
      _ = ∑ i ∈ Finset.univ.map emb, e i (z i) := by simp only [Finset.sum_map, hz]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi ↦ by
        have h : i ∉ Set.range emb := by
          rintro ⟨b, rfl⟩
          exact hi (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
        rw [show z i = 0 from dite_eq_right h, map_zero])

end MathlibExt.Combinatorics.GreenProblem69Wanted
