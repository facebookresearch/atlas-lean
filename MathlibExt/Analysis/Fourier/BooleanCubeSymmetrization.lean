/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCube
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Symmetrization and the approximate degree of parity

Minsky-Papert symmetrization on the Boolean cube and the approximate degree of parity (de Wolf, arXiv:1907.09415, Ch. 11.2). The query lower-bound corollary is downstream.
-/

@[expose] public section

open scoped BigOperators
namespace BooleanCube

set_option autoImplicit false

/-- |x| -/
def hammingWeight {n : ℕ} (x : BoolCube n) : ℕ := (Finset.univ.filter fun i => x i = true).card

/-- PARITY_N -/
def parityFunction {n : ℕ} (x : BoolCube n) : Bool := decide (Odd (hammingWeight x))

/-- q = (1/N!) Σ_π p ∘ π (de Wolf 11.2) -/
noncomputable def symmetrize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ := ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ p



/-- For a real polynomial `p` in `n` variables and a point `x` of the Boolean cube, read with
`true` as `1` and `false` as `0`, the symmetrization `symmetrize p`, the average of
`p (X_{σ 1}, …, X_{σ n})` over the permutations `σ`, evaluates at `x` to
`(n!)⁻¹ * ∑ σ, p (x_{σ 1}, …, x_{σ n})`. -/
theorem eval_symmetrize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : BoolCube n) : MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (symmetrize p) = (n.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p := by
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (MvPolynomial.rename σ p)
        = MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p := by
    intro σ
    rw [MvPolynomial.eval_rename]
    rfl
  unfold symmetrize
  rw [MvPolynomial.smul_eval, MvPolynomial.eval_sum]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => hterm σ)



/-- deg q ≤ deg p -/
theorem totalDegree_symmetrize_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : (symmetrize p).totalDegree ≤ p.totalDegree := by
  have hsmul : ∀ (c : ℝ) (q : MvPolynomial (Fin n) ℝ),
      (c • q).totalDegree ≤ q.totalDegree := by
    intro c q
    first
      | exact MvPolynomial.totalDegree_smul
      | exact MvPolynomial.totalDegree_smul c q
      | exact MvPolynomial.totalDegree_smul _ _
      | exact MvPolynomial.totalDegree_smul_le
      | exact MvPolynomial.totalDegree_smul_le c q
      | exact MvPolynomial.totalDegree_smul_le _ _
      | calc (c • q).totalDegree = (MvPolynomial.C c * q).totalDegree := by
              first
                | rw [MvPolynomial.smul_eq_C_mul]
                | rw [← MvPolynomial.C_mul']
                | rw [← MvPolynomial.C_mul]
                | rw [Algebra.smul_def, MvPolynomial.algebraMap_eq_apply]
                | rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
          _ ≤ (MvPolynomial.C c).totalDegree + q.totalDegree :=
              MvPolynomial.totalDegree_mul
          _ ≤ q.totalDegree := by
              have hc : (MvPolynomial.C c).totalDegree ≤ 0 := by
                first
                  | exact MvPolynomial.totalDegree_C _
                  | exact MvPolynomial.totalDegree_C
              omega
  have hsum : (Finset.univ.sum (fun σ : Equiv.Perm (Fin n) => MvPolynomial.rename σ p)).totalDegree ≤ p.totalDegree := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro σ _
    exact MvPolynomial.totalDegree_rename_le σ p
  unfold symmetrize
  exact le_trans (hsmul _ _) hsum


/-- Univariate contribution of one monomial to the symmetrized polynomial. -/
private noncomputable def monoPoly {n : ℕ} (c : ℝ) (t : ℕ) : Polynomial ℝ :=
  Polynomial.C ((n.factorial : ℝ)⁻¹ * c * (Nat.factorial (n - t) : ℝ)) * descPochhammer ℝ t

/-- The univariate contribution of one monomial has degree at most `t`. -/
private theorem natDegree_monoPoly_le {n : ℕ} (c : ℝ) (t : ℕ) :
    (monoPoly (n := n) c t).natDegree ≤ t := by
  unfold monoPoly
  refine le_trans Polynomial.natDegree_mul_le ?_
  have hC : (Polynomial.C ((n.factorial : ℝ)⁻¹ * c * (Nat.factorial (n - t) : ℝ))).natDegree ≤ 0 := by
    first
      | exact Polynomial.natDegree_C_le _
      | exact le_of_eq (Polynomial.natDegree_C _)
      | simp
  have hP : (descPochhammer ℝ t).natDegree ≤ t := by
    first
      | exact natDegree_descPochhammer
      | exact Polynomial.natDegree_descPochhammer
      | exact le_of_eq natDegree_descPochhammer
      | exact le_of_eq Polynomial.natDegree_descPochhammer
      | simp
  omega


/-- Evaluation of the univariate contribution of one monomial. -/
private theorem eval_monoPoly {n : ℕ} (c : ℝ) (t w : ℕ) :
    (monoPoly (n := n) c t).eval (w : ℝ)
      = ((n.factorial : ℝ)⁻¹ * c * (Nat.factorial (n - t) : ℝ))
        * (Nat.descFactorial w t : ℝ) := by
  unfold monoPoly
  first
    | (rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial]; rfl)
    | simp only [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial]


/-- Gluing two bijections into a permutation, forward map. -/
private noncomputable def glueFun {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) : Fin n → Fin n :=
  fun i => if hi : i ∈ T then (e₁ ⟨i, hi⟩).1 else (e₂ ⟨i, Finset.mem_compl.mpr hi⟩).1

/-- Gluing two bijections into a permutation, inverse map. -/
private noncomputable def glueFunInv {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) : Fin n → Fin n :=
  fun j => if hj : j ∈ U then (e₁.symm ⟨j, hj⟩).1
    else (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩).1

/-- A permutation mapping `T` onto `U` preserves membership. -/
private theorem mem_of_image_eq {n : ℕ} {T U : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hs : T.image ⇑σ = U) (i : Fin n) :
    (i ∈ T) ↔ (σ i ∈ U) := by
  constructor
  · intro hi
    rw [← hs]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro hj
    have hj' : σ i ∈ T.image ⇑σ := by rw [hs]; exact hj
    obtain ⟨k, hkT, heq⟩ := Finset.mem_image.mp hj'
    have hki : k = i := by
      first
        | exact Equiv.apply_eq_iff_eq.mp heq
        | (have h2 := congrArg σ.symm heq; simpa using h2)
    rw [hki] at hkT
    exact hkT

/-- A permutation mapping `T` onto `U` preserves complementary membership. -/
private theorem mem_compl_of_image_eq {n : ℕ} {T U : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hs : T.image ⇑σ = U) (i : Fin n) :
    (i ∈ Tᶜ) ↔ (σ i ∈ Uᶜ) := by
  rw [Finset.mem_compl, Finset.mem_compl]
  constructor
  · intro hi hcon
    have hj' : σ i ∈ T.image ⇑σ := by rw [hs]; exact hcon
    obtain ⟨k, hkT, heq⟩ := Finset.mem_image.mp hj'
    have hki : k = i := by
      first
        | exact Equiv.apply_eq_iff_eq.mp heq
        | (have h2 := congrArg σ.symm heq; simpa using h2)
    rw [hki] at hkT
    exact hi hkT
  · intro hi hcon
    have hmem : σ i ∈ T.image ⇑σ := Finset.mem_image.mpr ⟨i, hcon, rfl⟩
    rw [hs] at hmem
    exact hi hmem

/-- The glued map on `T`. -/
private theorem glueFun_pos {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (i : Fin n) (hi : i ∈ T) :
    glueFun e₁ e₂ i = (e₁ ⟨i, hi⟩).1 := by
  unfold glueFun
  rw [dite_eq_left hi]

/-- The glued map off `T`. -/
private theorem glueFun_neg {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (i : Fin n) (hi : i ∉ T) :
    glueFun e₁ e₂ i = (e₂ ⟨i, Finset.mem_compl.mpr hi⟩).1 := by
  unfold glueFun
  rw [dite_eq_right hi]

/-- The glued inverse map on `U`. -/
private theorem glueFunInv_pos {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (j : Fin n) (hj : j ∈ U) :
    glueFunInv e₁ e₂ j = (e₁.symm ⟨j, hj⟩).1 := by
  unfold glueFunInv
  rw [dite_eq_left hj]

/-- The glued inverse map off `U`. -/
private theorem glueFunInv_neg {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (j : Fin n) (hj : j ∉ U) :
    glueFunInv e₁ e₂ j = (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩).1 := by
  unfold glueFunInv
  rw [dite_eq_right hj]

/-- The glued maps are mutually inverse, one direction. -/
private theorem glue_left_inv {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (i : Fin n) :
    glueFunInv e₁ e₂ (glueFun e₁ e₂ i) = i := by
  by_cases hi : i ∈ T
  · have hmem : (e₁ ⟨i, hi⟩).1 ∈ U := (e₁ ⟨i, hi⟩).2
    rw [glueFun_pos e₁ e₂ i hi, glueFunInv_pos e₁ e₂ _ hmem]
    show (e₁.symm (e₁ ⟨i, hi⟩)).1 = i
    rw [Equiv.symm_apply_apply]
  · have hmem : (e₂ ⟨i, Finset.mem_compl.mpr hi⟩).1 ∉ U :=
      Finset.mem_compl.mp (e₂ ⟨i, Finset.mem_compl.mpr hi⟩).2
    rw [glueFun_neg e₁ e₂ i hi, glueFunInv_neg e₁ e₂ _ hmem]
    show (e₂.symm (e₂ ⟨i, Finset.mem_compl.mpr hi⟩)).1 = i
    rw [Equiv.symm_apply_apply]

/-- The glued maps are mutually inverse, the other direction. -/
private theorem glue_right_inv {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) (j : Fin n) :
    glueFun e₁ e₂ (glueFunInv e₁ e₂ j) = j := by
  by_cases hj : j ∈ U
  · have hmem : (e₁.symm ⟨j, hj⟩).1 ∈ T := (e₁.symm ⟨j, hj⟩).2
    rw [glueFunInv_pos e₁ e₂ j hj, glueFun_pos e₁ e₂ _ hmem]
    show (e₁ (e₁.symm ⟨j, hj⟩)).1 = j
    rw [Equiv.apply_symm_apply]
  · have hmem : (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩).1 ∉ T :=
      Finset.mem_compl.mp (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩).2
    rw [glueFunInv_neg e₁ e₂ j hj, glueFun_neg e₁ e₂ _ hmem]
    show (e₂ (e₂.symm ⟨j, Finset.mem_compl.mpr hj⟩)).1 = j
    rw [Equiv.apply_symm_apply]

/-- The glued permutation maps `T` onto `U`. -/
private theorem image_glueFun {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) : T.image (glueFun e₁ e₂) = U := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hiT, heq⟩ := Finset.mem_image.mp hj
    have hgi : glueFun e₁ e₂ i = (e₁ ⟨i, hiT⟩).1 := glueFun_pos e₁ e₂ i hiT
    rw [hgi] at heq
    rw [← heq]
    exact (e₁ ⟨i, hiT⟩).2
  · intro hjU
    have hiT : (e₁.symm ⟨j, hjU⟩).1 ∈ T := (e₁.symm ⟨j, hjU⟩).2
    have hgi : glueFun e₁ e₂ (e₁.symm ⟨j, hjU⟩).1 = j := by
      have h1 : glueFun e₁ e₂ (e₁.symm ⟨j, hjU⟩).1
          = (e₁ ⟨(e₁.symm ⟨j, hjU⟩).1, hiT⟩).1 :=
        glueFun_pos e₁ e₂ _ hiT
      rw [h1]
      show (e₁ (e₁.symm ⟨j, hjU⟩)).1 = j
      rw [Equiv.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨_, hiT, hgi⟩

/-- The permutation obtained by gluing two bijections. -/
private noncomputable def gluedPerm {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) : Equiv.Perm (Fin n) where
  toFun := glueFun e₁ e₂
  invFun := glueFunInv e₁ e₂
  left_inv := glue_left_inv e₁ e₂
  right_inv := glue_right_inv e₁ e₂

/-- The glued permutation maps `T` onto `U`. -/
private theorem image_gluedPerm {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) : T.image ⇑(gluedPerm e₁ e₂) = U :=
  image_glueFun e₁ e₂

/-- Restricting the glued permutation recovers the first bijection. -/
private theorem fiber_fst {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) :
    Equiv.subtypeEquiv (gluedPerm e₁ e₂)
        (mem_of_image_eq (image_gluedPerm e₁ e₂)) = e₁ := by
  apply Equiv.ext
  intro x
  obtain ⟨i, hi⟩ := x
  have hσi : (gluedPerm e₁ e₂) i = (e₁ ⟨i, hi⟩).1 := by
    show glueFun e₁ e₂ i = _
    rw [glueFun_pos e₁ e₂ i hi]
  first
    | refine Subtype.ext ?_
    | ext
  show (gluedPerm e₁ e₂) i = (e₁ ⟨i, hi⟩).1
  exact hσi

/-- Restricting the glued permutation recovers the second bijection. -/
private theorem fiber_snd {n : ℕ} {T U : Finset (Fin n)} (e₁ : T ≃ U)
    (e₂ : ↥(Tᶜ) ≃ ↥(Uᶜ)) :
    Equiv.subtypeEquiv (gluedPerm e₁ e₂)
        (mem_compl_of_image_eq (image_gluedPerm e₁ e₂)) = e₂ := by
  apply Equiv.ext
  intro x
  obtain ⟨i, hi⟩ := x
  have hiT : i ∉ T := Finset.mem_compl.mp hi
  have hσi : (gluedPerm e₁ e₂) i = (e₂ ⟨i, Finset.mem_compl.mpr hiT⟩).1 := by
    show glueFun e₁ e₂ i = _
    rw [glueFun_neg e₁ e₂ i hiT]
  first
    | refine Subtype.ext ?_
    | ext
  show (gluedPerm e₁ e₂) i = (e₂ ⟨i, hi⟩).1
  exact hσi

/-- Permutations mapping `T` onto `U`, as pairs of bijections. -/
private noncomputable def fiberEquiv {n : ℕ} (T U : Finset (Fin n)) :
    { σ : Equiv.Perm (Fin n) // T.image ⇑σ = U } ≃ (T ≃ U) × (↥(Tᶜ) ≃ ↥(Uᶜ)) where
  toFun := fun σ =>
    ((Equiv.subtypeEquiv σ.1 (mem_of_image_eq σ.2) : T ≃ U),
      (Equiv.subtypeEquiv σ.1 (mem_compl_of_image_eq σ.2) : ↥(Tᶜ) ≃ ↥(Uᶜ)))
  invFun := fun p => ⟨gluedPerm p.1 p.2, image_gluedPerm p.1 p.2⟩
  left_inv := fun σ => by
    first
      | refine Subtype.ext ?_
      | ext
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ T
    · show glueFun _ _ i = σ.1 i
      rw [glueFun_pos _ _ _ hi]
      rfl
    · show glueFun _ _ i = σ.1 i
      rw [glueFun_neg _ _ _ hi]
      rfl
  right_inv := fun p => by
    obtain ⟨e₁, e₂⟩ := p
    first
      | refine Prod.ext ?_ ?_
      | ext
    · exact fiber_fst e₁ e₂
    · exact fiber_snd e₁ e₂
/-- The number of permutations mapping `T` onto a fixed `t`-set `U`. -/
private theorem fiber_card {n : ℕ} (T U : Finset (Fin n)) (t : ℕ)
    (hT : T.card = t) (hU : U.card = t) :
    Fintype.card { σ : Equiv.Perm (Fin n) // T.image ⇑σ = U }
      = t.factorial * (n - t).factorial := by
  have hΦ := Fintype.card_congr (fiberEquiv T U)
  rw [Fintype.card_prod] at hΦ
  have h1 : Fintype.card (T ≃ U) = t.factorial := by
    have e : T ≃ U := Finset.equivOfCardEq (hT.trans hU.symm)
    have h := Fintype.card_equiv e
    rw [Fintype.card_coe, hT] at h
    exact h
  have hTc : (Tᶜ).card = n - t := by
    have hfin : Fintype.card (Fin n) = n := Fintype.card_fin n
    first
      | (have hcc := Finset.card_compl T; omega)
      | (have hcc : (Tᶜ).card = Fintype.card (Fin n) - T.card := Finset.card_compl; omega)
      | (have hcc := Finset.card_compl_add_card T; omega)
  have hUc : (Uᶜ).card = n - t := by
    have hfin : Fintype.card (Fin n) = n := Fintype.card_fin n
    first
      | (have hcc := Finset.card_compl U; omega)
      | (have hcc : (Uᶜ).card = Fintype.card (Fin n) - U.card := Finset.card_compl; omega)
      | (have hcc := Finset.card_compl_add_card U; omega)
  have h2 : Fintype.card (↥(Tᶜ) ≃ ↥(Uᶜ)) = (n - t).factorial := by
    have e : ↥(Tᶜ) ≃ ↥(Uᶜ) := Finset.equivOfCardEq (hTc.trans hUc.symm)
    have h := Fintype.card_equiv e
    rw [Fintype.card_coe, hTc] at h
    exact h
  rw [h1, h2] at hΦ
  exact hΦ

/-- Permutations mapping `T` into `S`, counted by image. -/
private theorem count_perms_image_subset {n : ℕ} (T S : Finset (Fin n)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => T.image ⇑σ ⊆ S)).card
      = Nat.descFactorial S.card T.card * (n - T.card).factorial := by
  set t := T.card with ht
  have hinj : ∀ σ : Equiv.Perm (Fin n), Function.Injective ⇑σ := by
    intro σ a b h
    first
      | exact Equiv.apply_eq_iff_eq.mp h
      | (have h2 := congrArg σ.symm h; simpa using h2)
  have hcard : ∀ σ : Equiv.Perm (Fin n), (T.image ⇑σ).card = t := by
    intro σ
    have h2 : (T.image ⇑σ).card = T.card := by
      first
        | exact Finset.card_image_of_injective T (hinj σ)
        | exact Finset.card_image_of_injective _ (hinj σ)
        | exact Finset.card_image_of_injective _ _ (hinj σ)
        | exact Finset.card_image_of_injOn _ (Set.injOn_of_injective (hinj σ) _)
    rw [h2]
  have hmem : ∀ σ : Equiv.Perm (Fin n),
      T.image ⇑σ ⊆ S → T.image ⇑σ ∈ S.powersetCard t := by
    intro σ hσ
    first
      | rw [Finset.mem_powersetCard]
      | rw [Finset.mem_powerset_card]
    first
      | exact ⟨hσ, hcard σ⟩
      | exact ⟨hcard σ, hσ⟩
  have hsub' : ∀ (U : Finset (Fin n)) (_ : U ∈ S.powersetCard t)
      (σ : Equiv.Perm (Fin n)), T.image ⇑σ = U → T.image ⇑σ ⊆ S := by
    intro U hU σ heq
    have h : U ⊆ S := by
      first
        | exact (Finset.mem_powersetCard.mp hU).1
        | exact (Finset.mem_powersetCard.mp hU).2
        | exact (Finset.mem_powerset_card.mp hU).1
        | exact (Finset.mem_powerset_card.mp hU).2
    rw [heq]
    exact h
  have hE : { σ : Equiv.Perm (Fin n) // T.image ⇑σ ⊆ S } ≃
      (Σ _U : { U : Finset (Fin n) // U ∈ S.powersetCard t },
        { σ : Equiv.Perm (Fin n) // T.image ⇑σ = _U.1 }) :=
    { toFun := fun σ => ⟨⟨T.image ⇑σ.1, hmem σ.1 σ.2⟩, σ.1, rfl⟩
      invFun := fun Uσ => ⟨Uσ.2.1, hsub' Uσ.1.1 Uσ.1.2 Uσ.2.1 Uσ.2.2⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        rfl
      right_inv := by
        rintro ⟨⟨U, hU⟩, σ, heq⟩
        have heq' : T.image ⇑σ = U := heq
        subst heq'
        rfl }
  have hcardE := Fintype.card_congr hE
  rw [Fintype.card_sigma] at hcardE
  have hfib : ∀ U : { U : Finset (Fin n) // U ∈ S.powersetCard t },
      Fintype.card { σ : Equiv.Perm (Fin n) // T.image ⇑σ = U.1 }
        = t.factorial * (n - t).factorial := by
    intro U
    have hUt : U.1.card = t := by
      first
        | exact (Finset.mem_powersetCard.mp U.2).2
        | exact (Finset.mem_powersetCard.mp U.2).1
        | exact (Finset.mem_powerset_card.mp U.2).2
        | exact (Finset.mem_powerset_card.mp U.2).1
    exact fiber_card T U.1 t ht.symm hUt
  simp only [hfib] at hcardE
  rw [Finset.sum_const, Finset.card_univ] at hcardE
  have hpc : Fintype.card { U : Finset (Fin n) // U ∈ S.powersetCard t }
      = (S.powersetCard t).card := by
    first
      | exact Fintype.card_coe _
      | exact Fintype.card_coe
      | exact Finset.card_coe _
      | exact Finset.card_coe
      | simp
  rw [hpc] at hcardE
  have hpcard : (S.powersetCard t).card = S.card.choose t := by
    first
      | exact Finset.card_powersetCard
      | exact Finset.card_powersetCard _ _
      | exact Finset.card_powerset_card
      | exact Finset.card_powerset_card _ _
      | simp [Finset.card_powersetCard]
      | simp [Finset.card_powerset_card]
  have hsub : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => T.image ⇑σ ⊆ S)).card
      = Fintype.card { σ : Equiv.Perm (Fin n) // T.image ⇑σ ⊆ S } := by
    first
      | exact Fintype.card_subtype
      | exact (Fintype.card_subtype).symm
      | rw [Fintype.card_subtype]
      | simp [Fintype.card_subtype]
      | simp
  rw [hsub, hcardE, hpcard, Nat.descFactorial_eq_factorial_mul_choose]
  first
    | (rw [nsmul_eq_mul]; simp only [Nat.cast_id]; ring)
    | (simp [nsmul_eq_mul]; ring)
    | ring

/-- Powers of `0/1` values collapse. -/
private theorem pow_bit {n : ℕ} (x : BoolCube n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (k : ℕ) (hk : k ≠ 0) :
    (if x (σ i) then (1 : ℝ) else 0) ^ k
      = (if x (σ i) then (1 : ℝ) else 0) := by
  by_cases h : x (σ i) = true
  · simp only [ite_eq_left h, one_pow]
  · simp only [ite_eq_right h]
    first
      | exact zero_pow hk
      | exact zero_pow _ hk
      | (cases k with
        | zero => exact absurd rfl hk
        | succ m => show (0:ℝ)^(m+1) = 0; rw [pow_succ, mul_zero])

/-- A symmetrized monomial is a falling factorial in the weight. -/
private theorem eval_symmetrize_monomial {n : ℕ} (s : Fin n →₀ ℕ) (a : ℝ)
    (x : BoolCube n) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
        (symmetrize (MvPolynomial.monomial s a))
      = (monoPoly (n := n) a s.support.card).eval (hammingWeight x : ℝ) := by
  set S := Finset.univ.filter (fun i : Fin n => x i = true) with hS
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0)
          (MvPolynomial.monomial s a)
        = a * (if s.support.image ⇑σ ⊆ S then (1 : ℝ) else 0) := by
    intro σ
    have heval : MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0)
          (MvPolynomial.monomial s a)
        = a * s.prod (fun i k => (if x (σ i) then (1 : ℝ) else 0) ^ k) :=
      MvPolynomial.eval_monomial
    have hsub : s.support ⊆ s.support := by
      first
        | exact Finset.Subset.rfl
        | exact Subset.rfl
        | exact fun x hx => hx
        | simp
    have hbridge : s.prod (fun i k => (if x (σ i) then (1 : ℝ) else 0) ^ k)
        = ∏ i ∈ s.support,
          (fun i k => (if x (σ i) then (1 : ℝ) else 0) ^ k) i (s i) := by
      first
        | (rw [Finsupp.prod_mem_support]; rfl)
        | (rw [Finsupp.prod_of_support_subset hsub]; rfl)
        | (simp only [Finsupp.prod_mem_support]; rfl)
        | (simp only [Finsupp.prod_of_support_subset]; rfl)
    have hprod : s.prod (fun i k => (if x (σ i) then (1 : ℝ) else 0) ^ k)
        = ∏ i ∈ s.support, (if x (σ i) then (1 : ℝ) else 0) := by
      rw [hbridge]
      apply Finset.prod_congr rfl
      intro i hi
      have hne : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
      exact pow_bit x σ i (s i) hne
    have hif := Finset.prod_boole (M₀ := ℝ) (s := s.support) (p := fun i => x (σ i) = true)
    have hcond : (∀ i ∈ s.support, x (σ i) = true)
        ↔ (s.support.image ⇑σ ⊆ S) := by
      constructor
      · intro h j hj
        obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hj
        have hS : σ i ∈ S ↔ x (σ i) = true := by
          simp [hS, Finset.mem_filter, Finset.mem_univ]
        exact hS.mpr (h i hiT)
      · intro h i hi
        have hS : σ i ∈ S ↔ x (σ i) = true := by
          simp [hS, Finset.mem_filter, Finset.mem_univ]
        exact hS.mp (h (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    rw [heval, hprod, hif]
    simp only [hcond]
  have hsum : (∑ σ : Equiv.Perm (Fin n), MvPolynomial.eval
        (fun i => if x (σ i) then (1 : ℝ) else 0) (MvPolynomial.monomial s a))
      = a * ((Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => s.support.image ⇑σ ⊆ S)).card : ℝ) := by
    have hboole : ((Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => s.support.image ⇑σ ⊆ S)).card : ℝ)
        = ∑ σ : Equiv.Perm (Fin n),
          (if s.support.image ⇑σ ⊆ S then (1 : ℝ) else 0) := by
      first
        | exact (Finset.sum_boole).symm
        | exact (Finset.sum_boole _ _).symm
        | (rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]; rfl)
        | (rw [Finset.sum_filter, Finset.sum_const, nsmul_one]; rfl)
    rw [hboole, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => hterm σ)
  have hw : hammingWeight x = S.card := by
    first
      | rfl
      | (unfold hammingWeight; rfl)
      | simp only [hammingWeight]
  rw [eval_symmetrize, hsum, eval_monoPoly, count_perms_image_subset, hw]
  first
    | (push_cast; ring)
    | (simp [Nat.cast_mul]; ring)
    | ring

/-- The support size is bounded by the total exponent sum. -/
private theorem card_support_le_sum {n : ℕ} (s : Fin n →₀ ℕ) :
    s.support.card ≤ s.sum (fun _ k => k) := by
  have h1 : ∀ i ∈ s.support, 1 ≤ s i := by
    intro i hi
    have hne : s i ≠ 0 := Finsupp.mem_support_iff.mp hi
    omega
  have hsum : s.sum (fun _ k => k) = ∑ i ∈ s.support, s i := by
    exact Finsupp.sum_of_support_subset s (fun x hx => hx) _ (fun i _ => rfl)
  rw [hsum]
  have h2 : (∑ _i ∈ s.support, 1) ≤ (∑ i ∈ s.support, s i) :=
    Finset.sum_le_sum h1
  have h3 : s.support.card = ∑ _i ∈ s.support, 1 := by
    first
      | exact Finset.card_eq_sum_ones
      | exact Finset.card_eq_sum_ones.symm
      | simp
  omega

/-- Minsky-Papert symmetrization: q(x) = r(|x|) with deg r ≤ deg p (de Wolf fn. 4: r(z) = Σ_i a_i C(z, i)) -/
theorem exists_polynomial_eval_symmetrize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ∃ r : Polynomial ℝ, r.natDegree ≤ p.totalDegree ∧ ∀ x : BoolCube n, MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (symmetrize p) = r.eval (hammingWeight x : ℝ) := by
  refine ⟨p.support.sum
    (fun s => monoPoly (n := n) (p.coeff s) s.support.card), ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    refine le_trans (natDegree_monoPoly_le _ _) ?_
    have h1 : s.support.card ≤ s.sum (fun _ k => k) := card_support_le_sum s
    have h2 : (s.sum fun _ k => k) ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
    omega
  · intro x
    have hdecomp : p
        = p.support.sum
          (fun s => MvPolynomial.monomial s (p.coeff s)) := by
      first
        | exact MvPolynomial.as_sum p
        | exact MvPolynomial.as_sum _
        | exact (MvPolynomial.support_sum_monomial_coeff p).symm
        | rw [MvPolynomial.as_sum]
        | simp [MvPolynomial.as_sum]
    have heval_sum : ∀ σ : Equiv.Perm (Fin n),
        MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          = ∑ s ∈ p.support, MvPolynomial.eval
            (fun i => if x (σ i) then (1 : ℝ) else 0)
            (MvPolynomial.monomial s (p.coeff s)) := by
      intro σ
      conv_lhs => rw [hdecomp]
      exact MvPolynomial.eval_sum _ _ _
    rw [eval_symmetrize]
    simp only [heval_sum]
    rw [Finset.sum_comm, Finset.mul_sum, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro s hs
    have hsym : (n.factorial : ℝ)⁻¹
          * (∑ σ : Equiv.Perm (Fin n), MvPolynomial.eval
            (fun i => if x (σ i) then (1 : ℝ) else 0)
            (MvPolynomial.monomial s (p.coeff s)))
          = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
            (symmetrize (MvPolynomial.monomial s (p.coeff s))) :=
      (eval_symmetrize _ _).symm
    exact hsym.trans (eval_symmetrize_monomial s _ x)
/-- Precomposing with a permutation preserves the Hamming weight. -/
private theorem weight_comp_perm {n : ℕ} (x : BoolCube n)
    (σ : Equiv.Perm (Fin n)) :
    hammingWeight (fun i => x (σ i)) = hammingWeight x := by
  have hinj : Function.Injective ⇑σ.symm := by
    intro a b h
    have h2 := congrArg ⇑σ h
    simpa using h2
  have hset : Finset.univ.filter (fun i : Fin n => x (σ i) = true)
      = (Finset.univ.filter (fun i : Fin n => x i = true)).image ⇑σ.symm := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      obtain ⟨-, hxi⟩ := hi
      have hSi : σ i ∈ Finset.univ.filter (fun i : Fin n => x i = true) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hxi⟩
      have heq : σ.symm (σ i) = i := by exact Equiv.symm_apply_apply σ i
      exact Finset.mem_image.mpr ⟨σ i, hSi, heq⟩
    · intro hi
      obtain ⟨j, hjS, heq⟩ := Finset.mem_image.mp hi
      have hjS' : x j = true := by
        rw [Finset.mem_filter] at hjS
        exact hjS.2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsi : σ i = j := by rw [← heq, Equiv.apply_symm_apply]
      rw [hsi]
      exact hjS'
  unfold hammingWeight
  show (Finset.univ.filter (fun i : Fin n => x (σ i) = true)).card
    = (Finset.univ.filter (fun i : Fin n => x i = true)).card
  rw [hset]
  first
    | exact Finset.card_image_of_injective _ hinj
    | exact Finset.card_image_of_injective _ _ hinj
    | exact Finset.card_image_of_injOn _ (Set.injOn_of_injective hinj _)

/-- Precomposing with a permutation preserves parity. -/
private theorem parity_comp_perm {n : ℕ} (x : BoolCube n)
    (σ : Equiv.Perm (Fin n)) :
    parityFunction (fun i => x (σ i)) = parityFunction x := by
  unfold parityFunction
  rw [weight_comp_perm]

/-- Symmetrization preserves approximation of parity. -/
private theorem approx_symmetrize {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ x : BoolCube n, |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p
      - (if parityFunction x then 1 else 0)| ≤ 1 / 3)
    (x : BoolCube n) :
    |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (symmetrize p)
      - (if parityFunction x then 1 else 0)| ≤ 1 / 3 := by
  have hfact0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    first
      | exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      | positivity
      | simp [Nat.factorial_ne_zero]
  have hc : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have heval := eval_symmetrize p x
  have hP : (if parityFunction x then (1:ℝ) else 0)
      = (n.factorial : ℝ)⁻¹ * (∑ _σ : Equiv.Perm (Fin n),
        (if parityFunction x then (1:ℝ) else 0)) := by
    rw [Finset.sum_const, hc, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hfact0, one_mul]
  have hdiff : MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0)
        (symmetrize p) - (if parityFunction x then (1 : ℝ) else 0)
      = (n.factorial : ℝ)⁻¹ * (∑ σ : Equiv.Perm (Fin n),
        (MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0))) := by
    rw [heval]
    conv_lhs => rw [hP]
    first
      | rw [← mul_sub]
      | rw [mul_sub]
    rw [← Finset.sum_sub_distrib]
  have hnonneg : (0:ℝ) ≤ (n.factorial : ℝ)⁻¹ := by
    first
      | exact inv_nonneg.mpr (Nat.cast_nonneg _)
      | positivity
      | simp
  have habs : |(n.factorial : ℝ)⁻¹ * (∑ σ : Equiv.Perm (Fin n),
        (MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0)))|
      = (n.factorial : ℝ)⁻¹ * |(∑ σ : Equiv.Perm (Fin n),
        (MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0)))| := by
    rw [abs_mul, abs_of_nonneg hnonneg]
  have hle1 : |(∑ σ : Equiv.Perm (Fin n),
        (MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0)))|
      ≤ ∑ σ : Equiv.Perm (Fin n), |(MvPolynomial.eval
        (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0))| :=
    Finset.abs_sum_le_sum_abs _ _
  have hle2 : (∑ σ : Equiv.Perm (Fin n), |(MvPolynomial.eval
        (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0))|)
      ≤ ∑ _σ : Equiv.Perm (Fin n), (1/3 : ℝ) := by
    apply Finset.sum_le_sum
    intro σ _
    have hpx := hp (fun i => x (σ i))
    rw [parity_comp_perm] at hpx
    exact hpx
  have hsum13 : (∑ _σ : Equiv.Perm (Fin n), (1/3 : ℝ))
      = (n.factorial : ℝ) * (1/3) := by
    rw [Finset.sum_const, hc, nsmul_eq_mul]
  have hle : (n.factorial : ℝ)⁻¹ * |(∑ σ : Equiv.Perm (Fin n),
        (MvPolynomial.eval (fun i => if x (σ i) then (1 : ℝ) else 0) p
          - (if parityFunction x then (1 : ℝ) else 0)))|
      ≤ (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * (1/3)) := by
    apply mul_le_mul_of_nonneg_left _ hnonneg
    exact le_trans hle1 (le_trans hle2 (le_of_eq hsum13))
  have heq : (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * (1/3)) = 1/3 := by
    rw [← mul_assoc, inv_mul_cancel₀ hfact0, one_mul]
  rw [hdiff, habs]
  rw [heq] at hle
  exact hle

/-- The canonical point of weight `k`. -/
private def repPoint {n : ℕ} (k : ℕ) : BoolCube n :=
  fun i => decide (i.val < k)

/-- The canonical point has weight `k`. -/
private theorem weight_repPoint {n : ℕ} (k : ℕ) (hkn : k ≤ n) :
    hammingWeight (repPoint (n := n) k) = k := by
  have hterm : ∀ i : Fin n, (if decide (i.val < k) = true then (1:ℕ) else 0)
      = (if i.val < k then (1:ℕ) else 0) := by
    intro i
    by_cases h : i.val < k
    · rw [ite_eq_left h]
      have hd : decide (i.val < k) = true := by
        first
          | exact decide_eq_true h
          | exact decide_eq_true.mpr h
          | exact of_eq_true h
          | simp [h]
      rw [ite_eq_left hd]
    · rw [ite_eq_right h]
      have hd : ¬ decide (i.val < k) = true :=
        fun hc => h (of_decide_eq_true hc)
      rw [ite_eq_right hd]
  have hcard : (Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true)).card
      = ∑ i : Fin n, (if decide (i.val < k) = true then (1:ℕ) else 0) := by
    have h1 : (Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true)).card
        = ∑ _i ∈ Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true), 1 := by
      first
        | exact Finset.card_eq_sum_ones
        | exact Finset.card_eq_sum_ones.symm
        | simp
    have h2 : (∑ _i ∈ Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true), 1)
        = ∑ i : Fin n, (if decide (i.val < k) = true then (1:ℕ) else 0) := by
      first
        | exact Finset.sum_filter
        | exact Finset.sum_filter.symm
        | rw [Finset.sum_filter]
        | simp [Finset.sum_filter]
    exact h1.trans h2
  have hrange : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨lt_of_lt_of_le h hkn, h⟩
  have hrange_sum : (∑ j ∈ Finset.range n, (if j < k then (1:ℕ) else 0)) = k := by
    have hfilter : (∑ j ∈ Finset.range n, (if j < k then (1:ℕ) else 0))
        = ((Finset.range n).filter (fun j => j < k)).card := by
      first
        | exact Finset.sum_boole
        | exact (Finset.sum_boole).symm
        | exact Finset.sum_boole _ _
        | simp [Finset.sum_boole]
    rw [hfilter, hrange, Finset.card_range]
  unfold hammingWeight repPoint
  show (Finset.univ.filter (fun i : Fin n => decide (i.val < k) = true)).card = k
  rw [hcard]
  simp only [hterm]
  simp only [Fin.sum_univ_eq_sum_range (fun j => (if j < k then (1:ℕ) else 0)) n]
  exact hrange_sum

/-- deg~_{1/3}(PARITY_N) ≥ N for every real polynomial (covers any multilinear representation the principal leaf picks) -/
theorem le_totalDegree_of_approx_parityFunction {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : ∀ x : BoolCube n, |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p - (if parityFunction x then 1 else 0)| ≤ 1 / 3) : n ≤ p.totalDegree := by
  obtain ⟨r, hrdeg, hrval⟩ := exists_polynomial_eval_symmetrize p
  have hseval : ∀ t : ℝ, (r - Polynomial.C (1/2)).eval t = r.eval t - 1/2 := by
    intro t
    first
      | exact Polynomial.eval_sub
      | rw [Polynomial.eval_sub, Polynomial.eval_C]
      | simp [Polynomial.eval_sub, Polynomial.eval_C]
      | simp
  have hrval_int : ∀ k : ℕ, k ≤ n →
      r.eval (k : ℝ) = MvPolynomial.eval
        (fun i => if repPoint (n := n) k i then (1:ℝ) else 0) (symmetrize p) := by
    intro k hkn
    have h := hrval (repPoint (n := n) k)
    rw [weight_repPoint k hkn] at h
    exact h.symm
  have hsign : ∀ k : ℕ, k ≤ n →
      (Odd k → (1/6 : ℝ) ≤ (r - Polynomial.C (1/2)).eval (k : ℝ))
      ∧ (¬ Odd k → (r - Polynomial.C (1/2)).eval (k : ℝ) ≤ -(1/6 : ℝ)) := by
    intro k hkn
    have happrox := approx_symmetrize p hp (repPoint (n := n) k)
    have hpar : parityFunction (repPoint (n := n) k) = decide (Odd k) := by
      unfold parityFunction
      rw [weight_repPoint k hkn]
    rw [hpar, ← hrval_int k hkn] at happrox
    constructor
    · intro hk
      have hdec : decide (Odd k) = true := by
        first
          | exact decide_eq_true hk
          | exact decide_eq_true.mpr hk
          | exact of_eq_true hk
          | simp [hk]
      first
        | rw [ite_eq_left hdec] at happrox
        | simp [hdec] at happrox
      rw [hseval]
      obtain ⟨hlo, -⟩ := abs_le.mp happrox
      linarith
    · intro hk
      have hdec : ¬ decide (Odd k) = true := fun hc => hk (of_decide_eq_true hc)
      first
        | rw [ite_eq_right hdec] at happrox
        | simp [hdec] at happrox
      rw [hseval]
      obtain ⟨-, hhi⟩ := abs_le.mp happrox
      linarith
  have hs0 : r - Polynomial.C (1/2) ≠ 0 := by
    intro hcon
    have h0 : (0:ℕ) ≤ n := Nat.zero_le n
    have hnotodd : ¬ Odd 0 := by
      first
        | (rw [Nat.odd_iff]; norm_num)
        | simp
        | exact Nat.not_odd_zero
    have hsign0 := (hsign 0 h0).2 hnotodd
    rw [Nat.cast_zero] at hsign0
    have heval0 : (r - Polynomial.C (1/2)).eval (0:ℝ) = 0 := by
      first
        | rw [hcon, Polynomial.eval_zero]
        | simp [hcon]
        | simp
    linarith
  have hroot : ∀ j : ℕ, j < n → ∃ c : ℝ,
      (j:ℝ) < c ∧ c < ((j+1:ℕ):ℝ) ∧ (r - Polynomial.C (1/2)).eval c = 0 := by
    intro j hj
    have hj1 : j + 1 ≤ n := hj
    have hj0 : j ≤ n := le_of_lt hj
    have hsj := hsign j hj0
    have hsj1 := hsign (j+1) hj1
    have hab : (j:ℝ) ≤ ((j+1:ℕ):ℝ) := by push_cast; linarith
    have hcont : ContinuousOn (fun t => (r - Polynomial.C (1/2)).eval t)
        (Set.Icc (j:ℝ) ((j+1:ℕ):ℝ)) := by
      first
        | exact (Polynomial.continuous).continuousOn
        | exact (Polynomial.continuous _).continuousOn
        | exact Polynomial.continuousOn
    by_cases hjodd : Odd j
    · have hnodd1 : ¬ Odd (j + 1) := by
        intro hcon
        rw [Nat.odd_iff] at hjodd hcon
        omega
      have hpos : (0:ℝ) < (r - Polynomial.C (1/2)).eval (j:ℝ) := by
        linarith [hsj.1 hjodd]
      have hneg : (r - Polynomial.C (1/2)).eval ((j+1:ℕ):ℝ) < (0:ℝ) := by
        linarith [hsj1.2 hnodd1]
      have hmem : (0:ℝ) ∈ Set.Icc ((r - Polynomial.C (1/2)).eval ((j+1:ℕ):ℝ))
          ((r - Polynomial.C (1/2)).eval (j:ℝ)) :=
        Set.mem_Icc.mpr ⟨le_of_lt hneg, le_of_lt hpos⟩
      have hsub' := intermediate_value_Icc' hab hcont
      have himg := hsub' hmem
      obtain ⟨c, hcIcc, hc0⟩ := (Set.mem_image _ _ _).mp himg
      have hc0' : (r - Polynomial.C (1/2)).eval c = 0 := hc0
      have hcIcc' := Set.mem_Icc.mp hcIcc
      have hne1 : c ≠ (j:ℝ) := by
        intro heq
        rw [heq] at hc0'
        linarith [hpos]
      have hne2 : c ≠ ((j+1:ℕ):ℝ) := by
        intro heq
        rw [heq] at hc0'
        linarith [hneg]
      have hlt1 : (j:ℝ) < c := by
        rw [← not_le]
        intro hcon
        exact (fun h => hne1 h.symm) (le_antisymm hcIcc'.1 hcon)
      have hlt2 : c < ((j+1:ℕ):ℝ) := by
        rw [← not_le]
        intro hcon
        exact (fun h => hne2 h.symm) (le_antisymm hcon hcIcc'.2)
      exact ⟨c, hlt1, hlt2, hc0'⟩
    · have hodd1 : Odd (j + 1) := by
        rw [Nat.odd_iff]
        rw [Nat.odd_iff] at hjodd
        omega
      have hneg : (r - Polynomial.C (1/2)).eval (j:ℝ) < (0:ℝ) := by
        linarith [hsj.2 hjodd]
      have hpos : (0:ℝ) < (r - Polynomial.C (1/2)).eval ((j+1:ℕ):ℝ) := by
        linarith [hsj1.1 hodd1]
      have hmem : (0:ℝ) ∈ Set.Icc ((r - Polynomial.C (1/2)).eval (j:ℝ))
          ((r - Polynomial.C (1/2)).eval ((j+1:ℕ):ℝ)) :=
        Set.mem_Icc.mpr ⟨le_of_lt hneg, le_of_lt hpos⟩
      have hsub' := intermediate_value_Icc hab hcont
      have himg := hsub' hmem
      obtain ⟨c, hcIcc, hc0⟩ := (Set.mem_image _ _ _).mp himg
      have hc0' : (r - Polynomial.C (1/2)).eval c = 0 := hc0
      have hcIcc' := Set.mem_Icc.mp hcIcc
      have hne1 : c ≠ (j:ℝ) := by
        intro heq
        rw [heq] at hc0'
        linarith [hneg]
      have hne2 : c ≠ ((j+1:ℕ):ℝ) := by
        intro heq
        rw [heq] at hc0'
        linarith [hpos]
      have hlt1 : (j:ℝ) < c := by
        rw [← not_le]
        intro hcon
        exact (fun h => hne1 h.symm) (le_antisymm hcIcc'.1 hcon)
      have hlt2 : c < ((j+1:ℕ):ℝ) := by
        rw [← not_le]
        intro hcon
        exact (fun h => hne2 h.symm) (le_antisymm hcon hcIcc'.2)
      exact ⟨c, hlt1, hlt2, hc0'⟩
  have hroot' : ∀ j : ℕ, ∃ c : ℝ, j < n →
      ((j:ℝ) < c ∧ c < ((j+1:ℕ):ℝ) ∧ (r - Polynomial.C (1/2)).eval c = 0) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨c, hc1, hc2, hc0⟩ := hroot j hj
      exact ⟨c, fun _ => ⟨hc1, hc2, hc0⟩⟩
    · exact ⟨0, fun hcon => absurd hcon hj⟩
  choose c hc using hroot'
  have hinj : Set.InjOn c (↑(Finset.range n)) := by
    intro a ha b hb hab
    have ha' : a < n := by
      first
        | exact Finset.mem_range.mp (Finset.mem_coe.mp ha)
        | exact Finset.mem_range.mp ha
        | simpa using ha
    have hb' : b < n := by
      first
        | exact Finset.mem_range.mp (Finset.mem_coe.mp hb)
        | exact Finset.mem_range.mp hb
        | simpa using hb
    obtain ⟨ha1, ha2, -⟩ := hc a ha'
    obtain ⟨hb1, hb2, -⟩ := hc b hb'
    by_cases heq : a = b
    · exact heq
    · have hlt : a < b ∨ b < a := by
        first
          | exact lt_or_gt_of_ne heq
          | exact Ne.lt_or_gt heq
      rcases hlt with hlt | hlt
      · have hab1 : a + 1 ≤ b := by omega
        have hle : ((a+1:ℕ):ℝ) ≤ (b:ℝ) := by
          first
            | exact_mod_cast hab1
            | exact Nat.cast_le.mpr hab1
            | simp [hab1]
        have hfalse : False := by linarith [ha2, hle, hb1, hab]
        exact False.elim hfalse
      · have hab1 : b + 1 ≤ a := by omega
        have hle : ((b+1:ℕ):ℝ) ≤ (a:ℝ) := by
          first
            | exact_mod_cast hab1
            | exact Nat.cast_le.mpr hab1
            | simp [hab1]
        have hfalse : False := by linarith [hb2, hle, ha1, hab]
        exact False.elim hfalse
  have hZcard : ((Finset.range n).image c).card = n := by
    have h : ((Finset.range n).image c).card = (Finset.range n).card := by
      first
        | exact Finset.card_image_of_injOn _ hinj
        | exact Finset.card_image_of_injOn _ _ hinj
        | exact Finset.card_image_of_injOn hinj
        | simp [hinj]
    rw [h, Finset.card_range]
  have hmem : ∀ z ∈ (Finset.range n).image c,
      z ∈ (r - Polynomial.C (1/2)).roots := by
    intro z hz
    obtain ⟨j, hjr, rfl⟩ := Finset.mem_image.mp hz
    have hcj := hc j (Finset.mem_range.mp hjr)
    first
      | (rw [Polynomial.mem_roots hs0]; exact hcj.2.2)
      | exact (Polynomial.mem_roots hs0).mpr hcj.2.2
  have hsub : ((Finset.range n).image c).val ⊆ (r - Polynomial.C (1/2)).roots := by
    intro a ha
    have ha' : a ∈ (Finset.range n).image c := by simpa using ha
    exact hmem a ha'
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hZcard] at hle
  have hsub_le : (r - Polynomial.C (1/2)).natDegree ≤ r.natDegree := by
    have h := Polynomial.natDegree_sub_le r (Polynomial.C (1/2 : ℝ))
    rw [Polynomial.natDegree_C] at h
    omega
  exact le_trans hle (le_trans hsub_le hrdeg)

/-- The total degree of a product is bounded by the cardinality, given uniform bounds. -/
private theorem totalDegree_prod_le_card {n : ℕ} (s : Finset (Fin n))
    (g : Fin n → MvPolynomial (Fin n) ℝ) :
    (∀ i ∈ s, (g i).totalDegree ≤ 1) → (s.prod g).totalDegree ≤ s.card := by
  intro hg
  refine le_trans (MvPolynomial.totalDegree_finsetProd s g) ?_
  refine le_trans (Finset.sum_le_card_nsmul s _ 1 hg) ?_
  simp

/-- `1 - X i` has total degree at most one. -/
private theorem totalDegree_one_sub_X_le_one {n : ℕ} (i : Fin n) :
    (1 - MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
  have hX : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have h1 : (1 : MvPolynomial (Fin n) ℝ).totalDegree ≤ 0 := by
    first
      | exact MvPolynomial.totalDegree_C 1
      | exact MvPolynomial.totalDegree_C _
      | exact MvPolynomial.totalDegree_C
      | exact le_of_eq MvPolynomial.totalDegree_one
      | exact MvPolynomial.totalDegree_one
  have h := MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin n) ℝ) (MvPolynomial.X i)
  omega

/-- Each cube basis polynomial has total degree at most `n`. -/
private theorem totalDegree_cubeBasis_le {n : ℕ} (x : BoolCube n) :
    (cubeBasis x).totalDegree ≤ n := by
  have hfactor : ∀ i : Fin n,
      ((if x i then MvPolynomial.X i else 1 - MvPolynomial.X i :
        MvPolynomial (Fin n) ℝ)).totalDegree ≤ 1 := by
    intro i
    by_cases h : x i = true
    · simp only [ite_eq_left h]
      exact le_of_eq (MvPolynomial.totalDegree_X _)
    · simp only [ite_eq_right h]
      exact totalDegree_one_sub_X_le_one i
  simp only [cubeBasis]
  refine le_trans (totalDegree_prod_le_card Finset.univ _ ?_) ?_
  · intro i _
    exact hfactor i
  · rw [Finset.card_univ, Fintype.card_fin]

/-- The multilinear extension of parity has degree at most `n`. -/
private theorem totalDegree_multilinearExtension_parity_le (n : ℕ) :
    (multilinearExtension (parityFunction (n := n))).totalDegree ≤ n := by
  have hterm : ∀ x : BoolCube n,
      (MvPolynomial.C (if parityFunction (n := n) x then (1:ℝ) else 0)
        * cubeBasis x).totalDegree ≤ n := by
    intro x
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hc : ((MvPolynomial.C
        (if parityFunction (n := n) x then (1:ℝ) else 0) : MvPolynomial (Fin n) ℝ)).totalDegree ≤ 0 :=
      le_of_eq (MvPolynomial.totalDegree_C _)
    have hb := totalDegree_cubeBasis_le x
    omega
  simp only [multilinearExtension]
  refine le_trans (MvPolynomial.totalDegree_finsetSum_le ?_) (le_refl n)
  intro x _
  exact hterm x

/-- matching upper bound: the exact multilinear representation has degree N, so deg~_{1/3}(PARITY_N) = N -/
theorem booleanDegree_parityFunction (n : ℕ) : booleanDegree (parityFunction (n := n)) = n := by
  have hlow : n ≤ (multilinearExtension (parityFunction (n := n))).totalDegree := by
    apply le_totalDegree_of_approx_parityFunction
    intro x
    rw [eval_multilinearExtension]; simp
  have hup : (multilinearExtension (parityFunction (n := n))).totalDegree ≤ n :=
    totalDegree_multilinearExtension_parity_le n
  show (multilinearExtension (parityFunction (n := n))).totalDegree = n
  exact le_antisymm hup hlow

end BooleanCube
