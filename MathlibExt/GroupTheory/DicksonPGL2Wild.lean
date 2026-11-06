/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import MathlibExt.GroupTheory.DicksonPGL2Tame

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/

namespace MetaMathlibExt

@[expose] public section

namespace Dickson

open scoped BigOperators Pointwise Polynomial

/-- **Injective ring maps induce injective maps of $\mathrm{PGL}_n$.** Let $f : R \to S$ be an
injective homomorphism of commutative rings and let $n$ be a finite index set. Then the
homomorphism $\mathrm{PGL}_n(R) \to \mathrm{PGL}_n(S)$ induced by applying $f$ to matrix entries
is injective, where $\mathrm{PGL}_n(R)$ denotes $\mathrm{GL}_n(R)$ modulo its center. -/
theorem projGenLinGroup_map_injective {n R S : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Matrix.ProjGenLinGroup.map (n := n) f) := by
  have hmapGL : Function.Injective (Matrix.GeneralLinearGroup.map (n := n) f) := by
    intro A B hAB
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply hf
    have := congrArg (fun C : GL n S => (C : Matrix n n S) i j) hAB
    simpa using this
  intro g h hgh
  apply eq_of_inv_mul_eq_one
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (g⁻¹ * h)
  rw [← hA, Matrix.ProjGenLinGroup.mk_eq_one]
  have hcenterS : Matrix.GeneralLinearGroup.map (n := n) f A ∈
      Subgroup.center (GL n S) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    rw [← Matrix.ProjGenLinGroup.map_mk, hA, map_mul, map_inv, hgh]
    simp
  rw [Subgroup.mem_center_iff] at hcenterS ⊢
  intro B
  apply hmapGL
  simpa using hcenterS (Matrix.GeneralLinearGroup.map (n := n) f B)

private lemma dicksonWild_card_center_GL_two (F : Type*) [Field F] [Fintype F] :
    Nat.card (Subgroup.center (GL (Fin 2) F)) = Fintype.card F - 1 := by
  have hscalar : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* GL (Fin 2) F) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) hxy
    simpa using h
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  calc
    Nat.card (MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 2))) =
        Nat.card Fˣ := Nat.card_congr (MonoidHom.ofInjective hscalar).symm
    _ = Fintype.card F - 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card]

/-- **Order of $\mathrm{PGL}_2$ over a finite field.** If $F$ is a finite field with $q$ elements,
then the projective general linear group $\mathrm{PGL}_2(F)$ has order $q(q^2 - 1)$. -/
theorem card_projGenLinGroup_fin_two (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  change Nat.card (GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)) = _
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div,
    dicksonWild_card_center_GL_two, Matrix.card_GL_field, Fin.prod_univ_two]
  change ((q ^ 2 - q ^ (0 : ℕ)) * (q ^ 2 - q ^ (1 : ℕ))) / (q - 1) = _
  norm_num
  have hfactor : q ^ 2 - q = (q - 1) * q := by
    calc
      q ^ 2 - q = q * q - q * 1 := by simp [pow_two]
      _ = q * (q - 1) := (Nat.mul_sub_left_distrib q q 1).symm
      _ = (q - 1) * q := mul_comm _ _
  rw [hfactor]
  rw [show (q ^ 2 - 1) * ((q - 1) * q) =
    (q - 1) * (q * (q ^ 2 - 1)) by ac_rfl]
  rw [Nat.mul_div_cancel_left _ (by omega : 0 < q - 1)]

private lemma dicksonWild_card_SL_two (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
        Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker :=
      Nat.card_congr
        (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).toEquiv
    _ = Nat.card (GL (Fin 2) F) / Nat.card Fˣ := by
      apply Nat.eq_div_of_mul_eq_left Nat.card_pos.ne'
      rw [← (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker.card_mul_index]
      congr 1
      rw [Subgroup.index_ker,
        (MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective)]
      simp
    _ = q * (q ^ 2 - 1) := by
      rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_units,
        Nat.card_eq_fintype_card]
      change ((q ^ 2 - q ^ (0 : ℕ)) * (q ^ 2 - q ^ (1 : ℕ))) / (q - 1) = _
      norm_num
      have hfactor : q ^ 2 - q = (q - 1) * q := by
        calc
          q ^ 2 - q = q * q - q * 1 := by simp [pow_two]
          _ = q * (q - 1) := (Nat.mul_sub_left_distrib q q 1).symm
          _ = (q - 1) * q := mul_comm _ _
      rw [hfactor]
      rw [show (q ^ 2 - 1) * ((q - 1) * q) =
        (q - 1) * (q * (q ^ 2 - 1)) by ac_rfl]
      rw [Nat.mul_div_cancel_left _ (by omega : 0 < q - 1)]

private lemma dicksonWild_card_center_SL_two (p : ℕ) (F : Type*) [Field F] [Finite F]
    [CharP F p] (hp2 : p ≠ 2) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  let _ := Fintype.ofFinite F
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F)
      (0 : Fin 2)).toEquiv]
  simpa using (IsPrimitiveRoot.neg_one p hp2).card_rootsOfUnity

/-- **Order of $\mathrm{PSL}_2$ over a finite field of odd characteristic.** Let $F$ be a finite
field with $q$ elements whose characteristic $p$ is not $2$. Then the projective special linear
group $\mathrm{PSL}_2(F)$ has order $q(q^2 - 1)/2$. -/
theorem card_projectiveSpecialLinearGroup_fin_two (p : ℕ) (F : Type*)
    [Field F] [Fintype F] [CharP F p] (hp2 : p ≠ 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) / 2 := by
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) F ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) = _
  rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div,
    dicksonWild_card_SL_two, dicksonWild_card_center_SL_two p F hp2]

private lemma dicksonWild_matrix_sub_scalar_pow_char {p : ℕ} [Fact (Nat.Prime p)]
    {F : Type*} [Field F] [CharP F p] (M : Matrix (Fin 2) (Fin 2) F) (a : F) :
    (M - Matrix.scalar (Fin 2) a) ^ p =
      M ^ p - Matrix.scalar (Fin 2) (a ^ p) := by
  have hscalar (x : F) :
      algebraMap F (Matrix (Fin 2) (Fin 2) F) x = Matrix.scalar (Fin 2) x := by
    rw [Matrix.algebraMap_eq_diagonal]
    congr 1
  calc
    (M - Matrix.scalar (Fin 2) a) ^ p =
        Polynomial.aeval M ((Polynomial.X - Polynomial.C a) ^ p) := by simp [hscalar]
    _ = Polynomial.aeval M (Polynomial.X ^ p - Polynomial.C (a ^ p)) := by
      congr 1
      rw [sub_pow_char]
      simp
    _ = M ^ p - Matrix.scalar (Fin 2) (a ^ p) := by
      simp only [map_pow, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        hscalar, Matrix.scalar_apply]

private lemma dicksonWild_lift_isParabolic_of_order_eq_char
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (A : GL (Fin 2) F) (horder : orderOf (Matrix.ProjGenLinGroup.mk A) = p) :
    A.IsParabolic := by
  have hpgt : 2 < p := Fact.out
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  have htwo : (2 : F) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff F p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    omega
  let _ : NeZero (2 : F) := ⟨htwo⟩
  have hnonscalar : (A : Matrix (Fin 2) (Fin 2) F) ∉
      Set.range (Matrix.scalar (Fin 2)) := by
    rw [← Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar,
      ← Matrix.ProjGenLinGroup.mk_eq_one]
    exact (orderOf_eq_prime_iff.mp horder).2
  refine ⟨hnonscalar, ?_⟩
  by_contra hdisc
  let M : Matrix (Fin 2) (Fin 2) F := A
  let a : F := M.trace / 2
  let B : Matrix (Fin 2) (Fin 2) F := M - Matrix.scalar (Fin 2) a
  let d : F := M.discr / 4
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 htwo
  have hd : d ≠ 0 := div_ne_zero hdisc hfour
  have hB2 : B ^ 2 = Matrix.scalar (Fin 2) d := Matrix.sub_scalar_sq_eq_discr
  have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    simpa only [map_pow] using (orderOf_eq_prime_iff.mp horder).1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
  obtain ⟨u, hu⟩ := hAp
  have hMp : M ^ p = Matrix.scalar (Fin 2) (u : F) := by
    simpa [M] using congrArg Units.val hu.symm
  have hBp : B ^ p = Matrix.scalar (Fin 2) ((u : F) - a ^ p) := by
    rw [show B = M - Matrix.scalar (Fin 2) a from rfl,
      dicksonWild_matrix_sub_scalar_pow_char, hMp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  let k := p / 2
  have hpdecomp : 2 * k + 1 = p := Nat.two_mul_div_two_add_one_of_odd hpodd
  have hBpow : B ^ p = Matrix.scalar (Fin 2) (d ^ k) * B := by
    calc
      B ^ p = B ^ (2 * k + 1) := by rw [hpdecomp]
      _ = (B ^ 2) ^ k * B := by rw [pow_add, pow_mul, pow_one]
      _ = Matrix.scalar (Fin 2) d ^ k * B := by rw [hB2]
    change Matrix.diagonal (fun _ : Fin 2 => d) ^ k * B = _
    rw [Matrix.diagonal_pow]
    rfl
  have hs : d ^ k ≠ 0 := pow_ne_zero _ hd
  have hcoeff : Matrix.scalar (Fin 2) (d ^ k) * B =
      Matrix.scalar (Fin 2) ((u : F) - a ^ p) := hBpow.symm.trans hBp
  have hBscalar : B = Matrix.scalar (Fin 2) (((u : F) - a ^ p) / d ^ k) := by
    ext i j
    have hentry := congrArg (fun C : Matrix (Fin 2) (Fin 2) F => C i j) hcoeff
    change (Matrix.diagonal (fun _ : Fin 2 => d ^ k) * B) i j =
      Matrix.diagonal (fun _ : Fin 2 => (u : F) - a ^ p) i j at hentry
    rw [Matrix.diagonal_mul] at hentry
    by_cases hij : i = j
    · subst j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      apply (eq_div_iff hs).2
      rw [Matrix.diagonal_apply_eq] at hentry
      simpa [mul_comm] using hentry
    · have hzero : B i j = 0 := by
        simpa [Matrix.scalar_apply, hij, hs] using hentry
      rw [hzero]
      simp [Matrix.scalar_apply, hij]
  apply hnonscalar
  refine ⟨a + ((u : F) - a ^ p) / d ^ k, ?_⟩
  change Matrix.scalar (Fin 2) (a + ((u : F) - a ^ p) / d ^ k) = M
  rw [show M = Matrix.scalar (Fin 2) a + B by simp [B]]
  rw [hBscalar]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

private lemma dicksonWild_orderOf_mk_eq_char_of_isParabolic
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (A : GL (Fin 2) F) (hA : A.IsParabolic) :
    orderOf (Matrix.ProjGenLinGroup.mk A) = p := by
  have hpgt : 2 < p := Fact.out
  have htwo : (2 : F) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff F p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    omega
  let _ : NeZero (2 : F) := ⟨htwo⟩
  let M : Matrix (Fin 2) (Fin 2) F := A
  let a : F := M.trace / 2
  let B : Matrix (Fin 2) (Fin 2) F := M - Matrix.scalar (Fin 2) a
  have hB2 : B ^ 2 = 0 := by
    rw [Matrix.sub_scalar_sq_eq_discr, hA.2]
    ext i j
    simp [Matrix.scalar_apply]
  have hBp : B ^ p = 0 := by
    rw [show p = 2 + (p - 2) by omega, pow_add, hB2]
    simp
  have hAp : M ^ p = Matrix.scalar (Fin 2) (a ^ p) := by
    have h := dicksonWild_matrix_sub_scalar_pow_char M a
    rw [show M - Matrix.scalar (Fin 2) a = B from rfl, hBp] at h
    exact sub_eq_zero.mp h.symm
  apply orderOf_eq_prime_iff.mpr
  constructor
  · rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨a ^ p, hAp.symm⟩
  · intro hmk
    rw [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hmk
    exact hA.1 hmk

private lemma dicksonWild_exists_normalized_lift_of_orderOf_eq_char
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (S : GL (Fin 2) F) (horder : orderOf (Matrix.ProjGenLinGroup.mk S) = p)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ T : GL (Fin 2) F,
      Matrix.ProjGenLinGroup.mk T = Matrix.ProjGenLinGroup.mk S ∧
      Matrix.trace (T : Matrix (Fin 2) (Fin 2) F) = 2 ∧
      Matrix.det (T : Matrix (Fin 2) (Fin 2) F) = 1 ∧
      (T : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
  have htwo : (2 : F) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff F p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    have hpgt : 2 < p := Fact.out
    omega
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have hpar := dicksonWild_lift_isParabolic_of_order_eq_char S horder
  have htraceSq : Matrix.trace (S : Matrix (Fin 2) (Fin 2) F) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) F) := by
    rw [← sub_eq_zero, ← Matrix.discr_fin_two]
    exact hpar.2
  have htrace : Matrix.trace (S : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    intro hzero
    have hbad : (4 : F) * Matrix.det (S : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [hzero] at htraceSq
      simpa using htraceSq.symm
    exact (mul_ne_zero hfour S.det_ne_zero) hbad
  let r : Fˣ := Units.mk0
    (2 / Matrix.trace (S : Matrix (Fin 2) (Fin 2) F)) (div_ne_zero htwo htrace)
  let T : GL (Fin 2) F := S * Matrix.GeneralLinearGroup.scalar (Fin 2) r
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · simp [T]
  · change Matrix.trace ((S : Matrix (Fin 2) (Fin 2) F) *
        Matrix.scalar (Fin 2) (r : F)) = 2
    have htraceEntry : (S : Matrix (Fin 2) (Fin 2) F) 0 0 + S 1 1 ≠ 0 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using htrace
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, r]
    field_simp [htraceEntry]
  · change Matrix.det ((S : Matrix (Fin 2) (Fin 2) F) *
        Matrix.scalar (Fin 2) (r : F)) = 1
    rw [Matrix.det_mul]
    rw [show Matrix.det (Matrix.scalar (Fin 2) (r : F)) = (r : F) ^ 2 by
      simp [Matrix.scalar_apply, pow_two]]
    dsimp [r]
    field_simp [htrace]
    rw [htraceSq]
    ring
  · change (((S : Matrix (Fin 2) (Fin 2) F) *
        Matrix.scalar (Fin 2) (r : F)) 1 0) ≠ 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, hS10, r, htwo, htrace]

private lemma dicksonWild_exists_psl_preimage_of_det_square
    {F : Type*} [Field F] (A : GL (Fin 2) F) (r : Fˣ)
    (hr : r ^ 2 = Matrix.GeneralLinearGroup.det A) :
    ∃ z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
      Matrix.ProjectiveSpecialLinearGroup.toPGL z = Matrix.ProjGenLinGroup.mk A := by
  let B : GL (Fin 2) F := A * Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹
  have hBdetUnits : Matrix.GeneralLinearGroup.det B = 1 := by
    dsimp [B]
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
    norm_num
    rw [← hr]
    group
  have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val hBdetUnits
  let b : Matrix.SpecialLinearGroup (Fin 2) F := ⟨(B : Matrix (Fin 2) (Fin 2) F), hBdet⟩
  refine ⟨QuotientGroup.mk b, ?_⟩
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  have hbGL : Matrix.SpecialLinearGroup.toGL b = B := by
    apply Units.ext
    rfl
  rw [hbGL]
  change Matrix.ProjGenLinGroup.mk B = Matrix.ProjGenLinGroup.mk A
  calc
    Matrix.ProjGenLinGroup.mk B = Matrix.ProjGenLinGroup.mk A *
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹) := by
      exact map_mul Matrix.ProjGenLinGroup.mk A
        (Matrix.GeneralLinearGroup.scalar (Fin 2) r⁻¹)
    _ = Matrix.ProjGenLinGroup.mk A := by simp

private lemma dicksonWild_exists_embedded_psl_preimage_of_entries_mem
    {F : Type*} [Field F] (M : Subfield F) (S : GL (Fin 2) F)
    (hentries : ∀ i k, (S : Matrix (Fin 2) (Fin 2) F) i k ∈ M)
    (hdet : Matrix.det (S : Matrix (Fin 2) (Fin 2) F) = 1) :
    ∃ z : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M,
      Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = Matrix.ProjGenLinGroup.mk S := by
  let A : Matrix (Fin 2) (Fin 2) M := fun i k ↦ ⟨S i k, hentries i k⟩
  have hmapA : A.map M.subtype = (S : Matrix (Fin 2) (Fin 2) F) := by
    ext i k
    rfl
  have hdetA : Matrix.det A = 1 := by
    apply M.subtype.injective
    calc
      M.subtype (Matrix.det A) = Matrix.det (A.map M.subtype) := M.subtype.map_det A
      _ = 1 := by rw [hmapA, hdet]
      _ = M.subtype 1 := (map_one M.subtype).symm
  let Agl : GL (Fin 2) M := Matrix.GeneralLinearGroup.mkOfDetNeZero A
    (by rw [hdetA]; exact one_ne_zero)
  have hAglDet : Matrix.GeneralLinearGroup.det Agl = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdetA
  obtain ⟨z, hz⟩ := dicksonWild_exists_psl_preimage_of_det_square Agl 1 (by
    rw [one_pow, hAglDet])
  refine ⟨z, ?_⟩
  rw [hz, Matrix.ProjGenLinGroup.map_mk]
  congr 1
  apply Units.ext
  exact hmapA

private lemma dicksonWild_exists_embedded_pgl_preimage_of_entries_mem
    {F : Type*} [Field F] (M : Subfield F) (S : GL (Fin 2) F)
    (hentries : ∀ i k, (S : Matrix (Fin 2) (Fin 2) F) i k ∈ M) :
    ∃ z : Matrix.ProjGenLinGroup (Fin 2) M,
      Matrix.ProjGenLinGroup.map M.subtype z = Matrix.ProjGenLinGroup.mk S := by
  let A : Matrix (Fin 2) (Fin 2) M := fun i k ↦ ⟨S i k, hentries i k⟩
  have hmapA : A.map M.subtype = (S : Matrix (Fin 2) (Fin 2) F) := by
    ext i k
    rfl
  have hdetA : Matrix.det A ≠ 0 := by
    intro hzero
    apply S.det_ne_zero
    calc
      Matrix.det (S : Matrix (Fin 2) (Fin 2) F) =
          Matrix.det (A.map M.subtype) := congrArg Matrix.det hmapA.symm
      _ = M.subtype (Matrix.det A) := (M.subtype.map_det A).symm
      _ = 0 := by rw [hzero, map_zero]
  let Agl : GL (Fin 2) M := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA
  refine ⟨Matrix.ProjGenLinGroup.mk Agl, ?_⟩
  rw [Matrix.ProjGenLinGroup.map_mk]
  congr 1
  apply Units.ext
  exact hmapA

private noncomputable def dicksonWild_projectiveSpecialLinearGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup n R ≃*
      Matrix.ProjectiveSpecialLinearGroup n S := by
  let f := Matrix.SpecialLinearGroup.map (n := n) e.toRingHom
  let g := Matrix.SpecialLinearGroup.map (n := n) e.symm.toRingHom
  have hgf (x : Matrix.SpecialLinearGroup n R) : g (f x) = x := by
    ext i k
    exact e.symm_apply_apply (x i k)
  have hfg (x : Matrix.SpecialLinearGroup n S) : f (g x) = x := by
    ext i k
    exact e.apply_symm_apply (x i k)
  have hfSurj : Function.Surjective f := fun y ↦ ⟨g y, hfg y⟩
  have hgSurj : Function.Surjective g := fun x ↦ ⟨f x, hgf x⟩
  have hfCenter : Subgroup.center (Matrix.SpecialLinearGroup n R) ≤
      Subgroup.comap f (Subgroup.center (Matrix.SpecialLinearGroup n S)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hfSurj y
    simpa only [map_mul] using congrArg f ((Subgroup.mem_center_iff.mp hx) z)
  have hgCenter : Subgroup.center (Matrix.SpecialLinearGroup n S) ≤
      Subgroup.comap g (Subgroup.center (Matrix.SpecialLinearGroup n R)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hgSurj y
    simpa only [map_mul] using congrArg g ((Subgroup.mem_center_iff.mp hx) z)
  let qf := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n R))
    (Subgroup.center (Matrix.SpecialLinearGroup n S)) f hfCenter
  let qg := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n S))
    (Subgroup.center (Matrix.SpecialLinearGroup n R)) g hgCenter
  have hqgf (x : Matrix.ProjectiveSpecialLinearGroup n R) : qg (qf x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hgf]
  have hqfg (x : Matrix.ProjectiveSpecialLinearGroup n S) : qf (qg x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hfg]
  exact MulEquiv.ofBijective qf ⟨
    fun x y hxy ↦ by rw [← hqgf x, ← hqgf y, hxy],
    fun y ↦ ⟨qg y, hqfg y⟩⟩

private noncomputable def dicksonWild_projGenLinGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjGenLinGroup n R ≃* Matrix.ProjGenLinGroup n S := by
  let f := Matrix.ProjGenLinGroup.map (n := n) e.toRingHom
  let g := Matrix.ProjGenLinGroup.map (n := n) e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (Matrix.GeneralLinearGroup.map e.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.symm_apply_apply (A i k)
    rw [hA]
    rfl
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.toRingHom
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.apply_symm_apply (A i k)
    rw [hA]
    rfl

private lemma dicksonWild_exists_smul_eq_infty {F : Type*} [Field F] [DecidableEq F]
    (c : OnePoint F) : ∃ T : GL (Fin 2) F,
      (T • c : OnePoint F) = (OnePoint.infty : OnePoint F) := by
  classical
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe z =>
    let m : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, -z]
    have hdet : m.det ≠ 0 := by simp [m, Matrix.det_fin_two]
    let T := Matrix.GeneralLinearGroup.mkOfDetNeZero m hdet
    refine ⟨T, ?_⟩
    rw [OnePoint.smul_some_eq_ite]
    simp [T, m]

private lemma dicksonWild_isParabolic_of_commute_isParabolic
    {F : Type*} [Field F] [NeZero (2 : F)]
    (A B : GL (Fin 2) F) (hB : B.IsParabolic) (hcomm : A * B = B * A)
    (hA : Matrix.ProjGenLinGroup.mk A ≠ 1) : A.IsParabolic := by
  classical
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty B.parabolicFixedPoint
  let C : GL (Fin 2) F := T * B * T⁻¹
  let D : GL (Fin 2) F := T * A * T⁻¹
  have hCpar : C.IsParabolic :=
    (Matrix.GeneralLinearGroup.isParabolic_conj_iff T B).2 hB
  have hTinv : T⁻¹ • (OnePoint.infty : OnePoint F) = B.parabolicFixedPoint := by
    rw [← hT, ← mul_smul]
    simp
  have hCfix : C • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    change (T * B * T⁻¹) • (OnePoint.infty : OnePoint F) = OnePoint.infty
    rw [mul_smul, mul_smul, hTinv, (hB.smul_eq_self_iff).2 rfl, hT]
  have hC10 : (C : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp hCfix
  have hCshape : (C : Matrix (Fin 2) (Fin 2) F) 0 0 = C 1 1 ∧
      (C : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 :=
    (Matrix.isParabolic_iff_of_upperTriangular hC10).mp hCpar
  have hDC : D * C = C * D := by
    dsimp [C, D]
    calc
      (T * A * T⁻¹) * (T * B * T⁻¹) = T * (A * B) * T⁻¹ := by group
      _ = T * (B * A) * T⁻¹ := by rw [hcomm]
      _ = (T * B * T⁻¹) * (T * A * T⁻¹) := by group
  have hentry11 := congrArg
    (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 1) hDC
  have hentry11' : D 1 0 * C 0 1 + D 1 1 * C 1 1 =
      C 1 0 * D 0 1 + C 1 1 * D 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hentry11
  have hD10 : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [hC10, zero_mul, zero_add] at hentry11'
    have hprod : D 1 0 * C 0 1 = 0 := by
      linear_combination hentry11'
    exact (mul_eq_zero.mp hprod).resolve_right hCshape.2
  have hentry01 := congrArg
    (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hDC
  have hentry01' : D 0 0 * C 0 1 + D 0 1 * C 1 1 =
      C 0 0 * D 0 1 + C 0 1 * D 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hentry01
  have hDdiag : (D : Matrix (Fin 2) (Fin 2) F) 0 0 = D 1 1 := by
    rw [hCshape.1] at hentry01'
    apply (sub_eq_zero.mp ?_)
    apply (mul_eq_zero.mp ?_).resolve_right hCshape.2
    linear_combination hentry01'
  have hDpar : D.IsParabolic := by
    apply (Matrix.isParabolic_iff_of_upperTriangular hD10).2
    refine ⟨hDdiag, ?_⟩
    intro hD01
    apply hA
    have hDone : Matrix.ProjGenLinGroup.mk D = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨D 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, hD10, hD01, hDdiag]
    calc
      Matrix.ProjGenLinGroup.mk A =
          (Matrix.ProjGenLinGroup.mk T)⁻¹ * Matrix.ProjGenLinGroup.mk D *
            Matrix.ProjGenLinGroup.mk T := by
        dsimp [D]
        simp only [map_mul, map_inv]
        group
      _ = 1 := by rw [hDone]; simp
  exact (Matrix.GeneralLinearGroup.isParabolic_conj_iff T A).mp hDpar

/-- An element of `PGL₂` whose order is the odd characteristic has a unique fixed point on
the projective line. -/
private lemma dicksonWild_existsUnique_fixedPoint_of_orderOf_eq_char
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) (hg : orderOf g = p) :
    ∃! x : Projectivization F (Fin 2 → F), g • x = x := by
  classical
  have hpgt : 2 < p := Fact.out
  have htwo : (2 : F) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff F p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    omega
  let _ : NeZero (2 : F) := ⟨htwo⟩
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hparabolic := dicksonWild_lift_isParabolic_of_order_eq_char A hg
  let c : OnePoint F := A.parabolicFixedPoint
  let x : Projectivization F (Fin 2 → F) := OnePoint.equivProjectivization F c
  refine ⟨x, ?_, ?_⟩
  · change A • (OnePoint.equivProjectivization F c) =
      OnePoint.equivProjectivization F c
    rw [← OnePoint.equivProjectivization_smul]
    exact congrArg (OnePoint.equivProjectivization F)
      ((hparabolic.smul_eq_self_iff).2 rfl)
  · intro y hy
    change A • y = y at hy
    have hc : A • (OnePoint.equivProjectivization F).symm y =
        (OnePoint.equivProjectivization F).symm y := by
      apply (OnePoint.equivProjectivization F).injective
      rw [OnePoint.equivProjectivization_smul]
      simpa using hy
    have hcy : (OnePoint.equivProjectivization F).symm y = c := by
      exact (hparabolic.smul_eq_self_iff.mp hc)
    change y = OnePoint.equivProjectivization F c
    rw [← hcy, Equiv.apply_symm_apply]

private lemma dicksonWild_mk_eq_one_of_toLin_eq_smul {F : Type*} [Field F]
    (A : GL (Fin 2) F) (a : F)
    (h : (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) = a • 1) :
    Matrix.ProjGenLinGroup.mk A = 1 := by
  have hmatrix : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a := by
    ext i j
    have hv := LinearMap.congr_fun h (Pi.single j 1)
    by_cases hij : i = j
    · subst j
      simpa [Matrix.GeneralLinearGroup.toLin_apply] using congrFun hv i
    · simpa [Matrix.GeneralLinearGroup.toLin_apply, hij] using congrFun hv i
  have ha : a ≠ 0 := by
    intro ha
    apply A.det_ne_zero
    rw [hmatrix, ha]
    simp
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨Units.mk0 a ha, by ext i j; simp [hmatrix]⟩

private lemma dicksonWild_exists_two_eigenvalues
    {F V : Type*} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] (f : Module.End F V)
    (hf : f.IsSemisimple) (hnonscalar : ∀ a : F, f ≠ a • 1) :
    ∃ a b : F, a ≠ b ∧ f.HasEigenvalue a ∧ f.HasEigenvalue b := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue f
  by_cases hex : ∃ b : F, b ≠ a ∧ f.HasEigenvalue b
  · obtain ⟨b, hba, hb⟩ := hex
    exact ⟨a, b, hba.symm, ha, hb⟩
  · push Not at hex
    have hea : f.eigenspace a = ⊤ := by
      rw [← hf.iSup_eigenspace_eq_top]
      apply le_antisymm (le_iSup (fun b : F => f.eigenspace b) a)
      refine iSup_le fun b => ?_
      by_cases hba : b = a
      · subst b
        exact le_rfl
      · have hb : ¬f.HasEigenvalue b := hex b hba
        have : f.eigenspace b = ⊥ :=
          not_ne_iff.mp (Module.End.hasEigenvalue_iff.not.mp hb)
        simp [this]
    exfalso
    apply hnonscalar a
    rw [← sub_eq_zero]
    have hker : (f - a • 1).ker = ⊤ := by
      simpa only [Module.End.eigenspace_def] using hea
    exact LinearMap.ker_eq_top.mp hker

private lemma dicksonWild_finrank_eigenspace_eq_one
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (f : Module.End F V) (hdim : Module.finrank F V = 2)
    (hnonscalar : ∀ a : F, f ≠ a • 1) {a : F} (ha : f.HasEigenvalue a) :
    Module.finrank F (f.eigenspace a) = 1 := by
  have hge : 1 ≤ Module.finrank F (f.eigenspace a) :=
    Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp ha)
  have hle : Module.finrank F (f.eigenspace a) ≤ 2 :=
    hdim ▸ Submodule.finrank_le (f.eigenspace a)
  have hne : Module.finrank F (f.eigenspace a) ≠ 2 := by
    intro heq
    have htop : f.eigenspace a = ⊤ :=
      Submodule.eq_top_of_finrank_eq (heq.trans hdim.symm)
    apply hnonscalar a
    rw [← sub_eq_zero]
    have hker : (f - a • 1).ker = ⊤ := by
      simpa only [Module.End.eigenspace_def] using htop
    exact LinearMap.ker_eq_top.mp hker
  omega

private lemma dicksonWild_fixed_hasEigenvector {F : Type*} [Field F]
    (A : GL (Fin 2) F)
    (x : MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A)) :
    ∃ a : F, Module.End.HasEigenvector
      (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) a x.1.rep := by
  have hp := MulAction.mem_fixedBy.mp x.2
  rw [← Projectivization.mk_rep x.1] at hp
  rw [Projectivization.PGL.mk_smul_mk] at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hp
  refine ⟨a, Module.End.hasEigenvector_iff.mpr ⟨?_, x.1.rep_nonzero⟩⟩
  rw [Module.End.mem_eigenspace_iff]
  simpa [Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
    Matrix.smul_eq_mulVec] using ha.symm

private lemma dicksonWild_card_fixedBy_mk {F : Type*} [Field F] [IsAlgClosed F]
    (A : GL (Fin 2) F) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hsemi : Module.End.IsSemisimple
      (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F))) :
    Nat.card (MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A)) = 2 := by
  let f : Module.End F (Fin 2 → F) := Matrix.GeneralLinearGroup.toLin A
  have hnonscalar : ∀ a : F, f ≠ a • 1 := fun a ha =>
    hne (dicksonWild_mk_eq_one_of_toLin_eq_smul A a ha)
  let E := {a : F // f.HasEigenvalue a}
  let ev : MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) → E := fun x =>
    ⟨Classical.choose (dicksonWild_fixed_hasEigenvector A x),
      Module.End.hasEigenvalue_of_hasEigenvector
        (Classical.choose_spec (dicksonWild_fixed_hasEigenvector A x))⟩
  have hev (x) : f.HasEigenvector (ev x).1 x.1.rep := by
    exact Classical.choose_spec (dicksonWild_fixed_hasEigenvector A x)
  have hinj : Function.Injective ev := by
    intro x y hxy
    apply Subtype.ext
    apply Projectivization.submodule_injective
    have hxle : x.1.submodule ≤ f.eigenspace (ev x).1 := by
      rw [← Projectivization.mk_rep x.1, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact (Module.End.hasEigenvector_iff.mp (hev x)).1
    have hyle : y.1.submodule ≤ f.eigenspace (ev y).1 := by
      rw [← Projectivization.mk_rep y.1, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact (Module.End.hasEigenvector_iff.mp (hev y)).1
    have hxeq : x.1.submodule = f.eigenspace (ev x).1 :=
      Submodule.eq_of_le_of_finrank_eq hxle <| by
        rw [Projectivization.finrank_submodule]
        exact (dicksonWild_finrank_eigenspace_eq_one f (Module.finrank_fin_fun F)
          hnonscalar (ev x).2).symm
    have hyeq : y.1.submodule = f.eigenspace (ev y).1 :=
      Submodule.eq_of_le_of_finrank_eq hyle <| by
        rw [Projectivization.finrank_submodule]
        exact (dicksonWild_finrank_eigenspace_eq_one f (Module.finrank_fin_fun F)
          hnonscalar (ev y).2).symm
    exact hxeq.trans <| (congrArg (fun z : E => f.eigenspace z.1) hxy).trans hyeq.symm
  let vec : E → Fin 2 → F := fun a =>
    Classical.choose (Module.End.HasEigenvalue.exists_hasEigenvector a.2)
  have hvec (a : E) : f.HasEigenvector a.1 (vec a) :=
    Classical.choose_spec (Module.End.HasEigenvalue.exists_hasEigenvector a.2)
  have hlin : LinearIndependent F vec :=
    f.eigenvectors_linearIndependent {a : F | f.HasEigenvalue a} vec hvec
  let _ : Finite E := hlin.finite
  let _ : Finite (MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A)) := Finite.of_injective ev hinj
  let _ := Fintype.ofFinite E
  have hE : Nat.card E ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Module.finrank_fin_fun] using hlin.fintype_card_le_finrank
  have hle := Nat.card_le_card_of_injective ev hinj
  obtain ⟨a, b, hab, ha, hb⟩ :=
    dicksonWild_exists_two_eigenvalues f hsemi hnonscalar
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  obtain ⟨w, hw⟩ := hb.exists_hasEigenvector
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hv.2
    apply (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
    simpa [f, ha0] using hv.apply_eq_smul
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hw.2
    apply (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
    simpa [f, hb0] using hw.apply_eq_smul
  have vfix : Projectivization.mk F v hv.2 ∈
      MulAction.fixedBy (Projectivization F (Fin 2 → F))
        (Matrix.ProjGenLinGroup.mk A) := by
    rw [MulAction.mem_fixedBy, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 a ha0, by
      simpa [f, Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
        Matrix.smul_eq_mulVec] using hv.apply_eq_smul.symm⟩
  have wfix : Projectivization.mk F w hw.2 ∈
      MulAction.fixedBy (Projectivization F (Fin 2 → F))
        (Matrix.ProjGenLinGroup.mk A) := by
    rw [MulAction.mem_fixedBy, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 b hb0, by
      simpa [f, Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
        Matrix.smul_eq_mulVec] using hw.apply_eq_smul.symm⟩
  let xv : MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) := ⟨Projectivization.mk F v hv.2, vfix⟩
  let xw : MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) := ⟨Projectivization.mk F w hw.2, wfix⟩
  have hxvw : xv ≠ xw := by
    intro heq
    have hp : Projectivization.mk F v hv.2 =
        Projectivization.mk F w hw.2 := congrArg Subtype.val heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hp
    have hcval : (c : F) • w = v := by simpa [Units.smul_def] using hc
    have hscalar : (c : F) * b = a * (c : F) :=
      (smul_left_injective F hw.2) <| by
        calc
          ((c : F) * b) • w = (c : F) • f w := by rw [hw.apply_eq_smul, mul_smul]
          _ = f ((c : F) • w) := (f.map_smul (c : F) w).symm
          _ = f v := by rw [hcval]
          _ = a • v := hv.apply_eq_smul
          _ = (a * (c : F)) • w := by rw [← hcval, mul_smul]
    apply hab
    apply (mul_left_cancel₀ c.ne_zero)
    calc
      (c : F) * a = a * c := mul_comm _ _
      _ = (c : F) * b := hscalar.symm
  let pair : Fin 2 → MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) := ![xv, xw]
  have hpair : Function.Injective pair := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pair]
  have hge := Nat.card_le_card_of_injective pair hpair
  simp only [Nat.card_fin] at hge
  omega

private lemma dicksonWild_lift_isSemisimple
    {p : ℕ} [Fact p.Prime] (A : GL (Fin 2) (K p)) (m : ℕ)
    (hm : (Matrix.ProjGenLinGroup.mk A) ^ m = 1) (hpm : ¬p ∣ m) :
    Module.End.IsSemisimple
      (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End (K p) (Fin 2 → K p)) := by
  have hcenter : A ^ m ∈ Subgroup.center (GL (Fin 2) (K p)) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    simpa only [map_pow] using hm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  let f : Module.End (K p) (Fin 2 → K p) :=
    (Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup (K p) (Fin 2 → K p))
  change f.IsSemisimple
  have hpow : f ^ m = algebraMap (K p) (Module.End (K p) (Fin 2 → K p)) u.1 := by
    apply LinearMap.ext
    intro v
    funext i
    change ((↑((Matrix.GeneralLinearGroup.toLin A) ^ m) :
      Module.End (K p) (Fin 2 → K p)) v) i = _
    rw [← map_pow, ← hu]
    simp
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C u.1
      ((CharP.cast_eq_zero_iff (K p) p m).not.mpr hpm) u.ne_zero).squarefree
  simp [hpow]

private lemma dicksonWild_card_fixedBy_of_not_dvd_order
    {p : ℕ} [Fact p.Prime] (g : PGL p) (hg : g ≠ 1)
    (hpg : ¬p ∣ orderOf g) :
    Nat.card (MulAction.fixedBy (Projectivization (K p) (Fin 2 → K p)) g) = 2 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  apply dicksonWild_card_fixedBy_mk A hg
  exact dicksonWild_lift_isSemisimple A (orderOf (Matrix.ProjGenLinGroup.mk A))
    (pow_orderOf_eq_one _) hpg

private def dicksonWildExceptional (G X : Type*) [Group G] [MulAction G X] :=
  {x : X // ∃ g : G, g ≠ 1 ∧ g • x = x}

private instance dicksonWildExceptionalAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (dicksonWildExceptional G X) where
  smul g x := ⟨g • x.1, by
    obtain ⟨h, hh, hx⟩ := x.2
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · intro hgh
      apply hh
      calc
        h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [hgh]; simp
    · simp only [mul_smul, inv_smul_smul, hx]⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

private def dicksonWild_fixedByExceptionalEquiv
    {G X : Type*} [Group G] [MulAction G X] (g : G) (hg : g ≠ 1) :
    MulAction.fixedBy (dicksonWildExceptional G X) g ≃ MulAction.fixedBy X g where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, ⟨g, hg, x.2⟩⟩, Subtype.ext x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

private lemma dicksonWild_card_stabilizer_eq_of_quotient_eq
    {G X : Type*} [Group G] [MulAction G X] (u v : X)
    (huv : Quotient.mk'' u =
      (Quotient.mk'' v : MulAction.orbitRel.Quotient G X)) :
    Nat.card (MulAction.stabilizer G u) = Nat.card (MulAction.stabilizer G v) := by
  obtain ⟨g, hg⟩ := Quotient.exact huv
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (MulAction.stabilizer G v)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

private theorem dicksonWildExceptional_finite
    {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (hfixed : ∀ g : G, g ≠ 1 →
      Nat.card (MulAction.fixedBy X g) = 1 ∨
        Nat.card (MulAction.fixedBy X g) = 2) :
    Finite (dicksonWildExceptional G X) := by
  let NG := {g : G // g ≠ 1}
  let Y := Σ g : NG, MulAction.fixedBy X g.1
  let _ (g : NG) : Finite (MulAction.fixedBy X g.1) :=
    Nat.finite_of_card_ne_zero <| by
      rcases hfixed g.1 g.2 with h | h <;> rw [h] <;> decide
  let _ : Finite Y := inferInstance
  let f : dicksonWildExceptional G X → Y := fun x =>
    ⟨⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩,
      ⟨x.1, (Classical.choose_spec x.2).2⟩⟩
  exact Finite.of_injective f fun x y hxy => by
    apply Subtype.ext
    exact congrArg (fun z : Y => z.2.1) hxy

private lemma dicksonWild_two_mul_card_le_orbits_mul_card
    (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
    (hnontrivial : ∀ x : X, Nontrivial (MulAction.stabilizer G x)) :
    2 * Nat.card X ≤
      Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  let _ : (x : X) → Fintype (MulAction.stabilizer G x) :=
    fun x => Fintype.ofFinite (MulAction.stabilizer G x)
  simp only [Nat.card_eq_fintype_card]
  rw [MulAction.card_eq_sum_card_group_div_card_stabilizer G X]
  rw [Finset.mul_sum]
  calc
    ∑ ω : MulAction.orbitRel.Quotient G X,
        2 * (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) ≤
        ∑ _ω : MulAction.orbitRel.Quotient G X, Fintype.card G := by
      apply Finset.sum_le_sum
      intro ω _
      have he : 2 ≤ Fintype.card (MulAction.stabilizer G ω.out) := by
        have := Fintype.one_lt_card_iff_nontrivial.mpr (hnontrivial ω.out)
        omega
      have hdvd : Fintype.card (MulAction.stabilizer G ω.out) ∣ Fintype.card G := by
        simpa only [Nat.card_eq_fintype_card] using
          Subgroup.card_subgroup_dvd_card (MulAction.stabilizer G ω.out)
      calc
        2 * (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) ≤
            Fintype.card (MulAction.stabilizer G ω.out) *
              (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) :=
          Nat.mul_le_mul_right _ he
        _ = Fintype.card G := by
          rw [mul_comm, Nat.div_mul_cancel hdvd]
    _ = Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G := by simp

/-- **Elements of $\mathrm{PGL}_2$ of order divisible by the characteristic.** Let $p$ be an odd
prime and let $F$ be a field of characteristic $p$. If an element $g$ of $\mathrm{PGL}_2(F)$ has
finite order and $p$ divides the order of $g$, then the order of $g$ is $p$. -/
theorem orderOf_eq_char_of_char_dvd
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) (hfinite : orderOf g ≠ 0)
    (hdiv : p ∣ orderOf g) : orderOf g = p := by
  let k := orderOf g / p
  have hpower : orderOf (g ^ k) = p := by
    exact orderOf_pow_orderOf_div hfinite hdiv
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  let B : GL (Fin 2) F := A ^ k
  have hBpar : B.IsParabolic := by
    apply dicksonWild_lift_isParabolic_of_order_eq_char B
    simpa [B] using hpower
  have hpower_ne : (Matrix.ProjGenLinGroup.mk A) ^ k ≠ 1 :=
    (orderOf_eq_prime_iff.mp hpower).2
  have hAne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    intro hA
    apply hpower_ne
    rw [hA]
    simp
  have htwo : (2 : F) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff F p 2).not.mpr
    intro hpdiv
    have hpgt : 2 < p := Fact.out
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    omega
  let _ : NeZero (2 : F) := ⟨htwo⟩
  have hApar : A.IsParabolic := by
    apply dicksonWild_isParabolic_of_commute_isParabolic A B hBpar
    · exact (Commute.self_pow A k).eq
    · exact hAne
  exact dicksonWild_orderOf_mk_eq_char_of_isParabolic A hApar

private lemma dicksonWild_orderOf_coe_eq_char_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hP : IsPGroup p P)
    (g : P) (hg : g ≠ 1) :
    orderOf (g : Matrix.ProjGenLinGroup (Fin 2) F) = p := by
  obtain ⟨k, hkorder⟩ := (IsPGroup.iff_orderOf.mp hP) g
  have hk : k ≠ 0 := by
    intro hk
    subst k
    norm_num at hkorder
    exact hg hkorder
  have horder : orderOf (g : Matrix.ProjGenLinGroup (Fin 2) F) = p ^ k := by
    rw [Subgroup.orderOf_coe]
    exact hkorder
  apply orderOf_eq_char_of_char_dvd (g : Matrix.ProjGenLinGroup (Fin 2) F)
  · rw [horder]
    exact pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero
  · rw [horder]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact ⟨p ^ k, by simp [pow_succ, mul_comm]⟩

private lemma dicksonWild_existsUnique_fixedPoint_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) [Finite P]
    (hP : IsPGroup p P) (hPne : P ≠ ⊥) :
    ∃! x : Projectivization F (Fin 2 → F),
      ∀ g : P, (g : Matrix.ProjGenLinGroup (Fin 2) F) • x = x := by
  let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  let _ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  obtain ⟨k, hkorder⟩ := (IsPGroup.iff_orderOf.mp hP) z.1
  have hk : k ≠ 0 := by
    intro hk
    subst k
    norm_num at hkorder
    exact hz hkorder
  have hpdiv : p ∣ p ^ k := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact ⟨p ^ k, by simp [pow_succ, mul_comm]⟩
  let zG : Matrix.ProjGenLinGroup (Fin 2) F := z.1
  have hzGorder : orderOf zG = p ^ k := by
    change orderOf ((z.1 : P) : Matrix.ProjGenLinGroup (Fin 2) F) = p ^ k
    rw [Subgroup.orderOf_coe]
    exact hkorder
  have hzorder : orderOf zG = p := by
    apply orderOf_eq_char_of_char_dvd zG
    · rw [hzGorder]
      exact pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero
    · rwa [hzGorder]
  obtain ⟨x, hzx, hxunique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_orderOf_eq_char zG hzorder
  refine ⟨x, ?_, ?_⟩
  · intro g
    apply hxunique
    calc
      zG • ((g : Matrix.ProjGenLinGroup (Fin 2) F) • x) =
          (zG * g) • x := (mul_smul _ _ _).symm
      _ = (g * zG) • x := by
        congr 1
        simpa [zG] using congrArg
          (fun u : P ↦ (u : Matrix.ProjGenLinGroup (Fin 2) F))
          (Subgroup.mem_center_iff.mp z.2 g).symm
      _ = (g : Matrix.ProjGenLinGroup (Fin 2) F) • (zG • x) := mul_smul _ _ _
      _ = (g : Matrix.ProjGenLinGroup (Fin 2) F) • x := by rw [hzx]
  · intro y hy
    apply hxunique y
    exact hy z.1

private lemma dicksonWild_commute_of_common_fixed_order_char
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (x : Projectivization F (Fin 2 → F))
    (g h : Matrix.ProjGenLinGroup (Fin 2) F)
    (hgfix : g • x = x) (hhfix : h • x = x)
    (hgorder : g ≠ 1 → orderOf g = p) (hhorder : h ≠ 1 → orderOf h = p) :
    g * h = h * g := by
  classical
  let c : OnePoint F := (OnePoint.equivProjectivization F).symm x
  have hc : OnePoint.equivProjectivization F c = x := Equiv.apply_symm_apply _ _
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  have hTinv : T⁻¹ • (OnePoint.infty : OnePoint F) = c := by
    rw [← hT, ← mul_smul]
    simp
  have hshape (s : Matrix.ProjGenLinGroup (Fin 2) F) (A : GL (Fin 2) F)
      (hA : Matrix.ProjGenLinGroup.mk A = s) (hsfix : s • x = x)
      (hsorder : s ≠ 1 → orderOf s = p) :
      let D : GL (Fin 2) F := T * A * T⁻¹
      D 1 0 = 0 ∧ D 0 0 = D 1 1 := by
    have hAc : A • c = c := by
      apply (OnePoint.equivProjectivization F).injective
      rw [OnePoint.equivProjectivization_smul, hc]
      change Matrix.ProjGenLinGroup.mk A • x = x
      rwa [hA]
    let D : GL (Fin 2) F := T * A * T⁻¹
    have hDfix : D • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
      change (T * A * T⁻¹) • (OnePoint.infty : OnePoint F) = OnePoint.infty
      rw [mul_smul, mul_smul, hTinv, hAc, hT]
    have hD10 : D 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hDfix
    refine ⟨hD10, ?_⟩
    by_cases hs : s = 1
    · have hDone : Matrix.ProjGenLinGroup.mk D = 1 := by
        dsimp [D]
        rw [map_mul, map_mul, map_inv, hA, hs]
        simp
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hDone
      obtain ⟨a, ha⟩ := hDone
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F ↦ M 0 0) ha
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F ↦ M 1 1) ha
      change D 0 0 = D 1 1
      simpa [Matrix.scalar_apply] using h00.symm.trans h11
    · have hAorder : orderOf (Matrix.ProjGenLinGroup.mk A) = p := by
        rw [hA]
        exact hsorder hs
      have hApar := dicksonWild_lift_isParabolic_of_order_eq_char A hAorder
      have hDpar : D.IsParabolic :=
        (Matrix.GeneralLinearGroup.isParabolic_conj_iff T A).2 hApar
      exact (Matrix.isParabolic_iff_of_upperTriangular hD10).mp hDpar |>.1
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  let D : GL (Fin 2) F := T * A * T⁻¹
  let E : GL (Fin 2) F := T * B * T⁻¹
  have hD := hshape g A hA hgfix hgorder
  have hE := hshape h B hB hhfix hhorder
  change D 1 0 = 0 ∧ D 0 0 = D 1 1 at hD
  change E 1 0 = 0 ∧ E 0 0 = E 1 1 at hE
  have hDE : D * E = E * D := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hAB : A * B = B * A := by
    calc
      A * B = T⁻¹ * (D * E) * T := by dsimp [D, E]; group
      _ = T⁻¹ * (E * D) * T := by rw [hDE]
      _ = B * A := by dsimp [D, E]; group
  have hmk := congrArg Matrix.ProjGenLinGroup.mk hAB
  simpa only [map_mul, hA, hB] using hmk

private lemma dicksonWild_commute_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) [Finite P]
    (hP : IsPGroup p P) (hPne : P ≠ ⊥) :
    ∀ g h : P, g * h = h * g := by
  classical
  obtain ⟨x, hx, -⟩ := dicksonWild_existsUnique_fixedPoint_of_isPGroup P hP hPne
  let c : OnePoint F := (OnePoint.equivProjectivization F).symm x
  have hc : OnePoint.equivProjectivization F c = x := Equiv.apply_symm_apply _ _
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  have hTinv : T⁻¹ • (OnePoint.infty : OnePoint F) = c := by
    rw [← hT, ← mul_smul]
    simp
  have hshape (g : P) (A : GL (Fin 2) F)
      (hA : Matrix.ProjGenLinGroup.mk A = (g : Matrix.ProjGenLinGroup (Fin 2) F)) :
      let D : GL (Fin 2) F := T * A * T⁻¹
      D 1 0 = 0 ∧ D 0 0 = D 1 1 := by
    have hAc : A • c = c := by
      apply (OnePoint.equivProjectivization F).injective
      rw [OnePoint.equivProjectivization_smul, hc]
      change Matrix.ProjGenLinGroup.mk A • x = x
      rw [hA]
      exact hx g
    let D : GL (Fin 2) F := T * A * T⁻¹
    have hDfix : D • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
      change (T * A * T⁻¹) • (OnePoint.infty : OnePoint F) = OnePoint.infty
      rw [mul_smul, mul_smul, hTinv, hAc, hT]
    have hD10 : D 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hDfix
    refine ⟨hD10, ?_⟩
    by_cases hg : g = 1
    · have hDone : Matrix.ProjGenLinGroup.mk D = 1 := by
        dsimp [D]
        rw [map_mul, map_mul, map_inv, hA, hg]
        simp
      rw [Matrix.ProjGenLinGroup.mk_eq_one,
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hDone
      obtain ⟨a, ha⟩ := hDone
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F ↦ M 0 0) ha
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F ↦ M 1 1) ha
      change D 0 0 = D 1 1
      simpa [Matrix.scalar_apply] using h00.symm.trans h11
    · have hAorder : orderOf (Matrix.ProjGenLinGroup.mk A) = p := by
        rw [hA]
        exact dicksonWild_orderOf_coe_eq_char_of_isPGroup P hP g hg
      have hApar := dicksonWild_lift_isParabolic_of_order_eq_char A hAorder
      have hDpar : D.IsParabolic :=
        (Matrix.GeneralLinearGroup.isParabolic_conj_iff T A).2 hApar
      exact (Matrix.isParabolic_iff_of_upperTriangular hD10).mp hDpar |>.1
  intro g h
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (g : Matrix.ProjGenLinGroup (Fin 2) F)
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective
    (h : Matrix.ProjGenLinGroup (Fin 2) F)
  let D : GL (Fin 2) F := T * A * T⁻¹
  let E : GL (Fin 2) F := T * B * T⁻¹
  have hD := hshape g A hA
  have hE := hshape h B hB
  change D 1 0 = 0 ∧ D 0 0 = D 1 1 at hD
  change E 1 0 = 0 ∧ E 0 0 = E 1 1 at hE
  have hDE : D * E = E * D := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hAB : A * B = B * A := by
    calc
      A * B = T⁻¹ * (D * E) * T := by dsimp [D, E]; group
      _ = T⁻¹ * (E * D) * T := by rw [hDE]
      _ = B * A := by dsimp [D, E]; group
  apply Subtype.ext
  change (g : Matrix.ProjGenLinGroup (Fin 2) F) * h = h * g
  have hmk := congrArg Matrix.ProjGenLinGroup.mk hAB
  simpa only [map_mul, hA, hB] using hmk

private lemma dicksonWild_isomorphic_vector_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)] {F : Type*} [Field F] [CharP F p]
    (P : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) [Finite P]
    (hP : IsPGroup p P) (hPne : P ≠ ⊥) :
    ∃ m : ℕ, m ≥ 1 ∧ Nonempty (P ≃* Multiplicative (Fin m → ZMod p)) := by
  let _ : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  have hcomm := dicksonWild_commute_of_isPGroup P hP hPne
  let _ : IsMulCommutative P := ⟨⟨hcomm⟩⟩
  let _ : CommGroup P := IsMulCommutative.instCommGroup
  have horder (g : P) (hg : g ≠ 1) : orderOf g = p := by
    have h := dicksonWild_orderOf_coe_eq_char_of_isPGroup P hP g hg
    rwa [Subgroup.orderOf_coe] at h
  have hexp (g : P) : g ^ p = 1 := by
    by_cases hg : g = 1
    · rw [hg]
      simp
    · exact (orderOf_eq_iff (Fact.out : Nat.Prime p).pos).mp (horder g hg) |>.1
  have haddexp (g : Additive P) : p • g = 0 := by
    change g.toMul ^ p = 1
    exact hexp g.toMul
  let moduleP : Module (ZMod p) (Additive P) := AddCommGroup.zmodModule haddexp
  let freeP : @Module.Free (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Free.of_divisionRing (ZMod p) (Additive P) _ _ moduleP
  let finiteP : @Module.Finite (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Finite.of_finite (ZMod p) (Additive P) _ _ moduleP inferInstance
  let torsionP : @Module.IsTorsionFree (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Free.instIsTorsionFree (ZMod p) (Additive P) _ _ moduleP freeP
  let m := @Module.finrank (ZMod p) (Additive P) _ _ moduleP
  have hm : m ≥ 1 := by
    exact (@Module.finrank_pos_iff (ZMod p) (Additive P) _ _ moduleP _ finiteP _
      torsionP).mpr inferInstance
  refine ⟨m, hm, ?_⟩
  let e : Additive P ≃ₗ[ZMod p] (Fin m → ZMod p) :=
    (@Module.finBasis (ZMod p) (Additive P) _ _ moduleP freeP _ finiteP).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin m))
  exact ⟨(MulEquiv.multiplicativeAdditive P).symm.trans e.toAddEquiv.toMultiplicative⟩

private lemma dicksonWild_frobenius_case_of_isPGroup
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hP : IsPGroup p G) (hGne : G ≠ ⊥) :
    ∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := dicksonWild_isomorphic_vector_of_isPGroup G hP hGne
  let V := Multiplicative (Fin m → ZMod p)
  let C := Multiplicative (ZMod 1)
  let φ : C →* MulAut V := 1
  refine ⟨m, 1, hm, by simp, by simp, φ, ?_, ?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim a b
  · intro c hc
    exact (hc (Subsingleton.elim c 1)).elim
  · refine ⟨e.trans ?_⟩
    change V ≃* V ⋊[(1 : C →* MulAut V)] C
    exact (SemidirectProduct.mulEquivProd.trans MulEquiv.prodUnique).symm

namespace DicksonWildAffine

private def unitAction (F : Type*) [Field F] : Fˣ →* MulAut (Multiplicative F) where
  toFun u := (DistribMulAction.toAddEquiv F u).toMultiplicative
  map_one' := by
    ext x
    change (1 : F) * x.toAdd = x.toAdd
    simp
  map_mul' u v := by
    ext x
    change ((u * v : Fˣ) : F) * x.toAdd = (u : F) * ((v : F) * x.toAdd)
    simp [mul_assoc]

private abbrev Aff (F : Type*) [Field F] :=
  Multiplicative F ⋊[unitAction F] Fˣ

private lemma translation_conj_left {F : Type*} [Field F]
    (s : F) (h : Aff F) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd =
      h.left.toAdd + (1 - (h.right : F)) * s := by
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.inv_left]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
    MulAut.one_apply, one_mul, inv_one, map_inv, toAdd_mul, toAdd_ofAdd,
    toAdd_inv]
  have hact : (((unitAction F) h.right) (Multiplicative.ofAdd s)).toAdd =
      (h.right : F) * s := rfl
  rw [hact]
  ring

private lemma cyclic_translation_conj_left_eq_zero {F : Type*} [Field F]
    {H : Subgroup (Aff F)} (C : Subgroup H) (c : C)
    (hc : ∀ k : C, k ∈ Subgroup.zpowers c) (s : F)
    (hc0 : ((SemidirectProduct.inl (Multiplicative.ofAdd s) * c.1.1 *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd = 0) :
    ∀ k : C, ((SemidirectProduct.inl (Multiplicative.ofAdd s) * k.1.1 *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd = 0 := by
  let T : Aff F := SemidirectProduct.inl (Multiplicative.ofAdd s)
  have hbase : T * c.1.1 * T⁻¹ = SemidirectProduct.inr (c.1.1 : Aff F).right := by
    apply SemidirectProduct.ext
    · apply Multiplicative.ext
      exact hc0
    · simp [T, SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  intro k
  have hk := hc k
  rw [Subgroup.mem_zpowers_iff] at hk
  obtain ⟨z, hz⟩ := hk
  have hkAff : (k.1.1 : Aff F) = (c.1.1 : Aff F) ^ z := by
    exact congrArg (fun y : C ↦ (y.1.1 : Aff F)) hz.symm
  have heq : T * k.1.1 * T⁻¹ =
      SemidirectProduct.inr ((c.1.1 : Aff F).right ^ z) := by
    calc
      T * k.1.1 * T⁻¹ = T * (c.1.1 : Aff F) ^ z * T⁻¹ := by rw [hkAff]
      _ = (T * c.1.1 * T⁻¹) ^ z := by
        change (MulAut.conj T) ((c.1.1 : Aff F) ^ z) =
          (MulAut.conj T (c.1.1 : Aff F)) ^ z
        rw [map_zpow]
      _ = (SemidirectProduct.inr (c.1.1 : Aff F).right) ^ z := by rw [hbase]
      _ = SemidirectProduct.inr ((c.1.1 : Aff F).right ^ z) := by
        rw [map_zpow]
  change (T * k.1.1 * T⁻¹).left.toAdd = 0
  rw [heq]
  rfl

private noncomputable def infinity (F : Type*) [Field F] :
    Projectivization F (Fin 2 → F) := by
  classical
  exact OnePoint.equivProjectivization F OnePoint.infty

private noncomputable def borel (F : Type*) [Field F] :
    Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := by
  classical
  exact MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) (infinity F)

private noncomputable def lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) : GL (Fin 2) F :=
  Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)

private lemma mk_lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk (lift g) = g :=
  Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective g)

private lemma lift_lowerLeft_eq_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  classical
  have hg : g.1 • infinity F = infinity F :=
    MulAction.mem_stabilizer_iff.mp g.2
  have hA : lift g.1 • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply (OnePoint.equivProjectivization F).injective
    rw [OnePoint.equivProjectivization_smul]
    rw [← mk_lift g.1] at hg
    simpa [infinity] using hg
  exact OnePoint.smul_infty_eq_self_iff.mp hA

private lemma lift_lowerRight_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

private lemma lift_upperLeft_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

private noncomputable def lambda {F : Type*} [Field F] (g : borel F) : Fˣ :=
  Units.mk0 ((lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 / lift g.1 1 1)
    (div_ne_zero (lift_upperLeft_ne_zero g) (lift_lowerRight_ne_zero g))

private noncomputable def gamma {F : Type*} [Field F] (g : borel F) : F :=
  (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 1 / lift g.1 1 1

private lemma ratios_eq_of_mk_eq {F : Type*} [Field F] (A B : GL (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0)
    (hB11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    (A 0 0 / A 1 1 = B 0 0 / B 1 1) ∧
      (A 0 1 / A 1 1 = B 0 1 / B 1 1) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hentry (i j : Fin 2) : A i j * (u : F) = B i j := by
    have hij := congrArg (fun M : GL (Fin 2) F ↦
      (M : Matrix (Fin 2) (Fin 2) F) i j) hu
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] using hij
  constructor
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 0]
    ring
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 1]
    ring

private lemma lambda_mul {F : Type*} [Field F] (g h : borel F) :
    lambda (g * h) = lambda g * lambda h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  apply Units.ext
  change C 0 0 / C 1 1 = (A 0 0 / A 1 1) * (B 0 0 / B 1 1)
  rw [hrat.1]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g,
    show B 1 0 = 0 by exact lift_lowerLeft_eq_zero h]
  simp only [zero_mul, zero_add]
  field_simp [lift_lowerRight_ne_zero g, lift_lowerRight_ne_zero h]
  ring

private lemma gamma_mul {F : Type*} [Field F] (g h : borel F) :
    gamma (g * h) = gamma g + (lambda g : F) * gamma h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  change C 0 1 / C 1 1 = A 0 1 / A 1 1 + (A 0 0 / A 1 1) * (B 0 1 / B 1 1)
  rw [hrat.2]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g]
  simp only [zero_mul, zero_add]
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  have hB11 : B 1 1 ≠ 0 := lift_lowerRight_ne_zero h
  field_simp [hA11, hB11]
  ring

private lemma lambda_one {F : Type*} [Field F] : lambda (1 : borel F) = 1 := by
  have h := lambda_mul (1 : borel F) 1
  rw [one_mul] at h
  calc
    lambda (1 : borel F) = (lambda (1 : borel F))⁻¹ *
        (lambda (1 : borel F) * lambda (1 : borel F)) := by group
    _ = (lambda (1 : borel F))⁻¹ * lambda (1 : borel F) := by rw [← h]
    _ = 1 := by simp

private lemma gamma_one {F : Type*} [Field F] : gamma (1 : borel F) = 0 := by
  have h := gamma_mul (1 : borel F) 1
  rw [one_mul, lambda_one] at h
  simp only [Units.val_one, one_mul] at h
  linear_combination -h

private noncomputable def toAff {F : Type*} [Field F] : borel F →* Aff F where
  toFun g := ⟨Multiplicative.ofAdd (gamma g), lambda g⟩
  map_one' := by
    ext
    · exact gamma_one (F := F)
    · exact congrArg Units.val (lambda_one (F := F))
  map_mul' g h := by
    ext
    · exact gamma_mul g h
    · exact congrArg Units.val (lambda_mul g h)

private noncomputable def affineGL {F : Type*} [Field F] (a : F) (u : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : F), a; 0, 1] (by
    simp [Matrix.det_fin_two, Units.ne_zero])

private lemma affineGL_mul {F : Type*} [Field F] (a b : F) (u v : Fˣ) :
    affineGL a u * affineGL b v = affineGL (a + (u : F) * b) (u * v) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [affineGL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private lemma affineGL_inv_zero {F : Type*} [Field F] (u : Fˣ) :
    (affineGL 0 u)⁻¹ = affineGL 0 u⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  rw [affineGL_mul]
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [affineGL]

private lemma affineGL_conj {F : Type*} [Field F] (a : F) (r u : Fˣ) :
    affineGL 0 r * affineGL a u * (affineGL 0 r)⁻¹ =
      affineGL ((r : F) * a) u := by
  rw [affineGL_inv_zero, affineGL_mul, affineGL_mul]
  simp [mul_assoc, mul_comm]

private lemma affineGL_inv_translation {F : Type*} [Field F] (s : F) :
    (affineGL s 1)⁻¹ = affineGL (-s) 1 := by
  apply inv_eq_of_mul_eq_one_left
  rw [affineGL_mul]
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [affineGL]

private lemma affineGL_inv {F : Type*} [Field F] (a : F) (u : Fˣ) :
    (affineGL a u)⁻¹ = affineGL (-((u : F)⁻¹ * a)) u⁻¹ := by
  apply inv_eq_of_mul_eq_one_left
  rw [affineGL_mul]
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [affineGL]

private lemma affineGL_conj_lowerLeft {F : Type*} [Field F]
    (a : F) (u : Fˣ) (A : GL (Fin 2) F) :
    ((affineGL a u * A * (affineGL a u)⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = A 1 0 * (u : F)⁻¹ := by
  rw [affineGL_inv]
  simp [affineGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private lemma affineGL_translation_conj {F : Type*} [Field F]
    (s a : F) (u : Fˣ) :
    affineGL s 1 * affineGL a u * (affineGL s 1)⁻¹ =
      affineGL (a + (1 - (u : F)) * s) u := by
  rw [affineGL_inv_translation, affineGL_mul, affineGL_mul]
  simp only [one_mul, Units.val_one, mul_one]
  congr 1
  ring

private lemma affineGL_map_subfield {F : Type*} [Field F] (M : Subfield F)
    (a : M) (u : Mˣ) :
    Matrix.GeneralLinearGroup.map M.subtype (affineGL (F := M) a u) =
      affineGL (F := F) a.1 (Units.map M.subtype.toMonoidHom u) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [affineGL]

private lemma mk_affineGL_gamma_lambda {F : Type*} [Field F] (g : borel F) :
    Matrix.ProjGenLinGroup.mk (affineGL (gamma g) (lambda g)) = g.1 := by
  classical
  let A := lift g.1
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  let u : Fˣ := Units.mk0 (A 1 1)⁻¹ (inv_ne_zero hA11)
  rw [← mk_lift g.1]
  symm
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  have hu : A * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      affineGL (gamma g) (lambda g) := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, affineGL, u,
        gamma, lambda, A, lift_lowerLeft_eq_zero g, hA11, div_eq_mul_inv]
  exact hu

private lemma toAff_injective {F : Type*} [Field F] : Function.Injective (toAff (F := F)) := by
  intro g h heq
  apply Subtype.ext
  rw [← mk_affineGL_gamma_lambda g, ← mk_affineGL_gamma_lambda h]
  have hgamma := congrArg (fun z : Aff F ↦ z.left.toAdd) heq
  have hlambda := congrArg (fun z : Aff F ↦ z.right) heq
  change gamma g = gamma h at hgamma
  change lambda g = lambda h at hlambda
  rw [hgamma, hlambda]

private lemma toAff_surjective {F : Type*} [Field F] : Function.Surjective (toAff (F := F)) := by
  classical
  rintro ⟨a, u⟩
  let M := affineGL a.toAdd u
  have hMfix : M • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply OnePoint.smul_infty_eq_self_iff.mpr
    simp [M, affineGL]
  have hmem : Matrix.ProjGenLinGroup.mk M ∈ borel F := by
    apply MulAction.mem_stabilizer_iff.mpr
    have h := congrArg (OnePoint.equivProjectivization F) hMfix
    rw [OnePoint.equivProjectivization_smul] at h
    simpa [infinity] using h
  let g : borel F := ⟨Matrix.ProjGenLinGroup.mk M, hmem⟩
  refine ⟨g, ?_⟩
  have hmk : Matrix.ProjGenLinGroup.mk (lift g.1) = Matrix.ProjGenLinGroup.mk M := by
    exact mk_lift g.1
  have hM11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    simp [M, affineGL]
  have hrat := ratios_eq_of_mk_eq (lift g.1) M hmk
    (lift_lowerRight_ne_zero g) hM11
  apply SemidirectProduct.ext
  · change gamma g = a.toAdd
    rw [show gamma g = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 1 /
      lift g.1 1 1 by rfl, hrat.2]
    simp [M, affineGL]
  · apply Units.ext
    change (lambda g : F) = (u : F)
    rw [show (lambda g : F) = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 /
      lift g.1 1 1 by rfl, hrat.1]
    simp [M, affineGL]

private noncomputable def borelMulEquivAffine {F : Type*} [Field F] : borel F ≃* Aff F :=
  MulEquiv.ofBijective toAff ⟨toAff_injective, toAff_surjective⟩

private def rightRestrict {F : Type*} [Field F] (H : Subgroup (Aff F)) : H →* Fˣ :=
  SemidirectProduct.rightHom.comp H.subtype

private lemma kernel_isPGroup {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F)) :
    IsPGroup p (rightRestrict H).ker := by
  rw [IsPGroup.iff_orderOf]
  intro z
  by_cases hz : z = 1
  · exact ⟨0, by simp [hz]⟩
  · refine ⟨1, ?_⟩
    rw [pow_one]
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      apply Subtype.ext
      let a : Multiplicative F := (z.1.1 : Aff F).left
      have hright : (z.1.1 : Aff F).right = 1 := z.2
      have heq : (z.1.1 : Aff F) = SemidirectProduct.inl a := by
        apply SemidirectProduct.ext
        · rfl
        · exact hright
      rw [Subgroup.coe_pow, Subgroup.coe_pow, heq]
      rw [show (SemidirectProduct.inl a : Aff F) ^ p =
        SemidirectProduct.inl (a ^ p) by
          exact (map_pow (SemidirectProduct.inl : Multiplicative F →* Aff F) a p).symm]
      change SemidirectProduct.inl (a ^ p) = (1 : Aff F)
      apply SemidirectProduct.ext
      · change p • a.toAdd = 0
        simp [nsmul_eq_mul]
      · change (1 : Fˣ) = 1
        rfl
    · exact hz

private lemma units_orderOf_ne_char {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (u : Fˣ) : orderOf u ≠ p := by
  intro hu
  have hup : u ^ p = 1 := (orderOf_eq_prime_iff.mp hu).1
  have hval : (u : F) ^ p = 1 := congrArg Units.val hup
  have hsub : ((u : F) - 1) ^ p = 0 := by
    rw [sub_pow_char, hval]
    simp
  have huval : (u : F) = 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp hsub)
  have huone : u = 1 := Units.ext huval
  rw [huone, orderOf_one] at hu
  exact (Fact.out : p.Prime).ne_one hu.symm

private lemma range_card_coprime_char {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F)) [Finite H] :
    Nat.Coprime p (Nat.card (rightRestrict H).range) := by
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hp
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hp
  exact units_orderOf_ne_char (u : Fˣ) (by rwa [Subgroup.orderOf_coe])

private lemma kernel_card_coprime_index {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F)) [Finite H] :
    Nat.Coprime (Nat.card (rightRestrict H).ker) (rightRestrict H).ker.index := by
  let _ : Finite (rightRestrict H).ker := Finite.of_injective
    (fun z : (rightRestrict H).ker ↦ (z.1 : H)) Subtype.val_injective
  obtain ⟨m, hm⟩ := (kernel_isPGroup H).exists_card_eq
  rw [Subgroup.index_ker, hm]
  cases m with
  | zero => simp
  | succ m =>
    rw [Nat.coprime_pow_left_iff (Nat.succ_pos m)]
    exact range_card_coprime_char H

private lemma exists_cyclic_complement {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F)) [Finite H] :
    ∃ K : Subgroup H, (rightRestrict H).ker.IsComplement' K ∧
      Function.Injective ((rightRestrict H).domRestrict K) ∧ IsCyclic K := by
  let _ : (rightRestrict H).ker.Normal := MonoidHom.normal_ker (rightRestrict H)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (kernel_card_coprime_index H)
  have hinj : Function.Injective ((rightRestrict H).domRestrict K) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Subtype.ext
    have hkN : (k.1 : H) ∈ (rightRestrict H).ker := hk
    have hkbot : (k.1 : H) ∈ (⊥ : Subgroup H) := hK.disjoint.le_bot ⟨hkN, k.2⟩
    exact hkbot
  let fK := (rightRestrict H).domRestrict K
  let C : Subgroup Fˣ := fK.range
  let e : K ≃* C := MulEquiv.ofBijective fK.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hinj, fK.rangeRestrict_surjective⟩
  let _ : Finite C := Finite.of_surjective e e.surjective
  let _ : IsCyclic C := isCyclic_subgroup_units C
  exact ⟨K, hK, hinj, (e.isCyclic).mpr inferInstance⟩

private lemma elementaryAbelian_mulEquiv_fun {p : ℕ} [Fact p.Prime]
    (P : Type*) [Group P] [Finite P] [Nontrivial P]
    (hcomm : ∀ g h : P, g * h = h * g)
    (horder : ∀ g : P, g ≠ 1 → orderOf g = p) :
    ∃ m : ℕ, m ≥ 1 ∧ Nonempty (P ≃* Multiplicative (Fin m → ZMod p)) := by
  let _ : IsMulCommutative P := ⟨⟨hcomm⟩⟩
  let _ : CommGroup P := IsMulCommutative.instCommGroup
  have hexp (g : P) : g ^ p = 1 := by
    by_cases hg : g = 1
    · rw [hg]
      simp
    · exact (orderOf_eq_iff (Fact.out : p.Prime).pos).mp (horder g hg) |>.1
  have haddexp (g : Additive P) : p • g = 0 := by
    change g.toMul ^ p = 1
    exact hexp g.toMul
  let moduleP : Module (ZMod p) (Additive P) := AddCommGroup.zmodModule haddexp
  let freeP : @Module.Free (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Free.of_divisionRing (ZMod p) (Additive P) _ _ moduleP
  let finiteP : @Module.Finite (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Finite.of_finite (ZMod p) (Additive P) _ _ moduleP inferInstance
  let torsionP : @Module.IsTorsionFree (ZMod p) (Additive P) _ _ moduleP :=
    @Module.Free.instIsTorsionFree (ZMod p) (Additive P) _ _ moduleP freeP
  let m := @Module.finrank (ZMod p) (Additive P) _ _ moduleP
  have hm : m ≥ 1 := by
    exact (@Module.finrank_pos_iff (ZMod p) (Additive P) _ _ moduleP _ finiteP _
      torsionP).mpr inferInstance
  refine ⟨m, hm, ?_⟩
  let e : Additive P ≃ₗ[ZMod p] (Fin m → ZMod p) :=
    (@Module.finBasis (ZMod p) (Additive P) _ _ moduleP freeP _ finiteP).repr.trans
      (Finsupp.linearEquivFunOnFinite (ZMod p) (ZMod p) (Fin m))
  exact ⟨(MulEquiv.multiplicativeAdditive P).symm.trans e.toAddEquiv.toMultiplicative⟩

private def kernelLeft {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    (rightRestrict H).ker →* Multiplicative F where
  toFun z := (z.1.1 : Aff F).left
  map_one' := rfl
  map_mul' x y := by
    change (x.1.1 * y.1.1 : Aff F).left =
      (x.1.1 : Aff F).left * (y.1.1 : Aff F).left
    rw [SemidirectProduct.mul_left]
    have hx : (x.1.1 : Aff F).right = 1 := x.2
    simp [hx, unitAction]

private lemma kernelLeft_injective {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    Function.Injective (kernelLeft H) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact hxy
  · exact x.2.trans y.2.symm

private def kernelGamma {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    Additive (rightRestrict H).ker →+ F :=
  (AddEquiv.additiveMultiplicative F).toAddMonoidHom.comp
    (kernelLeft H).toAdditive

private def translationAddSubgroup {F : Type*} [Field F]
    (H : Subgroup (Aff F)) : AddSubgroup F :=
  (kernelGamma H).range

private lemma kernelGamma_injective {F : Type*} [Field F]
    (H : Subgroup (Aff F)) : Function.Injective (kernelGamma H) := by
  intro x y hxy
  apply Additive.ext
  apply kernelLeft_injective H
  apply Multiplicative.ext
  exact hxy

private lemma translationAddSubgroup_card {F : Type*} [Field F]
    (H : Subgroup (Aff F)) :
    Nat.card (translationAddSubgroup H) = Nat.card (rightRestrict H).ker := by
  calc
    Nat.card (translationAddSubgroup H) =
        Nat.card (Additive (rightRestrict H).ker) :=
      Nat.card_congr (AddMonoidHom.ofInjective (kernelGamma_injective H)).symm.toEquiv
    _ = Nat.card (rightRestrict H).ker := rfl

private noncomputable def multiplierSubfield {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] : Subfield F where
  carrier := {a | ∀ x ∈ Γ, a * x ∈ Γ}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact Γ.add_mem (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha _ (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact Γ.neg_mem (ha x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      simp
    · intro x hx
      let f : Γ → Γ := fun y ↦ ⟨a * y.1, ha y.1 y.2⟩
      have hf : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply mul_left_cancel₀ ha0
        exact congrArg Subtype.val hyz
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x, hx⟩
      have hyval : a * y.1 = x := congrArg Subtype.val hy
      rw [← hyval]
      simp [ha0, y.2]

private lemma multiplierSubfield_finite {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] (hΓ : Γ ≠ ⊥) :
    Finite (multiplierSubfield Γ) := by
  obtain ⟨γ, hγ⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have hγval : (γ : F) ≠ 0 := by
    intro h
    exact hγ (Subtype.ext h)
  let toΓ : multiplierSubfield Γ → Γ := fun a ↦
    ⟨a.1 * γ.1, a.2 γ.1 γ.2⟩
  apply Finite.of_injective toΓ
  intro a b hab
  apply Subtype.ext
  apply mul_right_cancel₀ hγval
  exact congrArg Subtype.val hab

private lemma multiplierSubfield_card_le {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] (hΓ : Γ ≠ ⊥) :
    Nat.card (multiplierSubfield Γ) ≤ Nat.card Γ := by
  obtain ⟨γ, hγ⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have hγval : (γ : F) ≠ 0 := by
    intro h
    exact hγ (Subtype.ext h)
  let toΓ : multiplierSubfield Γ → Γ := fun a ↦
    ⟨a.1 * γ.1, a.2 γ.1 γ.2⟩
  apply Nat.card_le_card_of_injective toΓ
  intro a b hab
  apply Subtype.ext
  apply mul_right_cancel₀ hγval
  exact congrArg Subtype.val hab

private noncomputable instance translationAddSubgroup_finite
    {F : Type*} [Field F] (H : Subgroup (Aff F)) [Finite H] :
    Finite (translationAddSubgroup H) :=
  Finite.of_surjective (kernelGamma H).rangeRestrict
    (kernelGamma H).rangeRestrict_surjective

private lemma rightRestrict_range_mem_multiplierSubfield {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H]
    (u : (rightRestrict H).range) :
    (u.1 : F) ∈ multiplierSubfield (translationAddSubgroup H) := by
  obtain ⟨h, hu⟩ := u.2
  rw [← hu]
  rintro x ⟨z, rfl⟩
  let w : (rightRestrict H).ker :=
    ⟨h * z.toMul.1 * h⁻¹, by
      change rightRestrict H (h * z.toMul.1 * h⁻¹) = 1
      rw [map_mul, map_mul, map_inv, z.toMul.2]
      simp⟩
  refine ⟨Additive.ofMul w, ?_⟩
  have hzright : (z.toMul.1.1 : Aff F).right = 1 := z.toMul.2
  change (((h.1 * z.toMul.1.1 * h.1⁻¹ : Aff F).left).toAdd) =
    (h.1 : Aff F).right * (z.toMul.1.1 : Aff F).left.toAdd
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul,
    SemidirectProduct.inv_left, map_inv, MulAut.inv_apply, MulAut.mul_apply,
    toAdd_mul, toAdd_inv]
  rw [hzright]
  dsimp [unitAction]
  simp only [AddEquiv.toMultiplicative_apply_apply,
    AddEquiv.toMultiplicative_apply_symm_apply,
    DistribMulAction.toAddEquiv_apply, DistribMulAction.toAddEquiv_symm_apply,
    toAdd_ofAdd, one_smul, Units.smul_def, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  change (h.1 : Aff F).left.toAdd +
      ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd +
        -(((h.1 : Aff F).right : F) *
          (((h.1 : Aff F).right : F)⁻¹ * (h.1 : Aff F).left.toAdd)) =
    ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd
  field_simp
  abel

private noncomputable def multiplierRangeHom {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    (rightRestrict H).range →* (multiplierSubfield (translationAddSubgroup H))ˣ where
  toFun u := Units.mk0
    (⟨(u.1 : F), rightRestrict_range_mem_multiplierSubfield H u⟩ :
      multiplierSubfield (translationAddSubgroup H)) (by
        intro h
        apply u.1.ne_zero
        exact congrArg Subtype.val h)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' _ _ := by
    apply Units.ext
    rfl

private noncomputable def multiplierRange {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    Subgroup (multiplierSubfield (translationAddSubgroup H))ˣ :=
  (multiplierRangeHom H).range

private lemma multiplierRangeHom_injective {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    Function.Injective (multiplierRangeHom H) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun z : (multiplierSubfield (translationAddSubgroup H))ˣ ↦
    (((z : multiplierSubfield (translationAddSubgroup H)) : F))) huv

private lemma multiplierRange_card {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    Nat.card (multiplierRange H) = Nat.card (rightRestrict H).range :=
  Nat.card_congr
    (MonoidHom.ofInjective (multiplierRangeHom_injective H)).symm.toEquiv

private lemma rightRestrict_range_card_add_one_le_multiplierSubfield
    {F : Type*} [Field F] (H : Subgroup (Aff F)) [Finite H]
    (hΓ : translationAddSubgroup H ≠ ⊥) :
    Nat.card (rightRestrict H).range + 1 ≤
      Nat.card (multiplierSubfield (translationAddSubgroup H)) := by
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite (multiplierSubfield (translationAddSubgroup H)) :=
    multiplierSubfield_finite (translationAddSubgroup H) hΓ
  let toM : Option (rightRestrict H).range →
      multiplierSubfield (translationAddSubgroup H)
    | none => 0
    | some u => ⟨u.1, rightRestrict_range_mem_multiplierSubfield H u⟩
  have htoM : Function.Injective toM := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            exfalso
            have h := congrArg Subtype.val hab
            exact b.1.ne_zero (by simpa [toM] using h.symm)
    | some a =>
        cases b with
        | none =>
            exfalso
            have h := congrArg Subtype.val hab
            simp [toM] at h
        | some b =>
            congr 1
            apply Subtype.ext
            apply Units.ext
            exact congrArg Subtype.val hab
  let _ : Fintype (rightRestrict H).range := Fintype.ofFinite _
  let _ : Fintype (multiplierSubfield (translationAddSubgroup H)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_option]
  exact Fintype.card_le_of_injective toM htoM

private lemma translationAddSubgroup_card_eq {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] (q t : ℕ)
    (hHcard : Nat.card H = q * t)
    (hrange : Nat.card (rightRestrict H).range = t) :
    Nat.card (translationAddSubgroup H) = q := by
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  have ht : 0 < t := by
    rw [← hrange]
    exact Nat.card_pos
  have hprod : Nat.card (rightRestrict H).ker *
      Nat.card (rightRestrict H).range = Nat.card H := by
    rw [← Subgroup.index_ker]
    exact (rightRestrict H).ker.card_mul_index
  rw [hrange, hHcard] at hprod
  rw [translationAddSubgroup_card]
  exact Nat.eq_of_mul_eq_mul_right ht hprod

private lemma multiplierSubfield_card_eq_pow
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    Nat.card (multiplierSubfield (translationAddSubgroup H)) = p ^ m := by
  let Γ := translationAddSubgroup H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hqone : 1 < p ^ m :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    omega
  let M := multiplierSubfield Γ
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨ell, -, hMpow⟩ := FiniteField.card M p
  have hMpow' : Nat.card M = p ^ (ell : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hMpow
  have hMle : Nat.card M ≤ p ^ m := by
    rw [← hΓcard]
    exact multiplierSubfield_card_le Γ hΓ
  have hellm : (ell : ℕ) ≤ m := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rwa [← hMpow']
  have htM : t + 1 ≤ Nat.card M := by
    have := rightRestrict_range_card_add_one_le_multiplierSubfield H hΓ
    rwa [hrange] at this
  have hell : (ell : ℕ) = m := by
    by_contra hne
    have hellsucc : (ell : ℕ) + 1 ≤ m := by omega
    have hpstep : p ^ ((ell : ℕ) + 1) ≤ p ^ m :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hellsucc
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      exact hpgt
    have hthree : 3 * Nat.card M ≤ p ^ m := by
      calc
        3 * Nat.card M = p ^ (ell : ℕ) * 3 := by rw [hMpow']; omega
        _ ≤ p ^ (ell : ℕ) * p := Nat.mul_le_mul_left _ hp3
        _ = p ^ ((ell : ℕ) + 1) := (pow_succ _ _).symm
        _ ≤ p ^ m := hpstep
    have hMpos : 0 < Nat.card M := Nat.card_pos
    omega
  rw [hMpow', hell]

private lemma multiplier_mul_bijective {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] (hΓ : Γ ≠ ⊥) (γ : Γ)
    (hγ : (γ : F) ≠ 0)
    (hcard : Nat.card (multiplierSubfield Γ) = Nat.card Γ) :
    Function.Bijective (fun a : multiplierSubfield Γ ↦
      (⟨a.1 * γ.1, a.2 γ.1 γ.2⟩ : Γ)) := by
  let _ : Finite (multiplierSubfield Γ) := multiplierSubfield_finite Γ hΓ
  let _ : Fintype Γ := Fintype.ofFinite Γ
  let _ : Fintype (multiplierSubfield Γ) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro a b hab
    apply Subtype.ext
    apply mul_right_cancel₀ hγ
    exact congrArg Subtype.val hab
  · simpa only [← Nat.card_eq_fintype_card] using hcard

private lemma exists_translation_conj_left_mem
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] :
    ∃ s : F, ∀ h : H,
      ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd ∈
        translationAddSubgroup H := by
  classical
  obtain ⟨C, hcomp, hinj, hcyclic⟩ := exists_cyclic_complement H
  let _ : (rightRestrict H).ker.Normal := MonoidHom.normal_ker (rightRestrict H)
  let _ : IsCyclic C := hcyclic
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  let E := SemidirectProduct.mulEquivSubgroup hcomp
  have finish (s : F) (hC0 : ∀ k : C,
      ((SemidirectProduct.inl (Multiplicative.ofAdd s) * k.1.1 *
        (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd = 0) :
      ∀ h : H,
        ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
          (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd ∈
          translationAddSubgroup H := by
    intro h
    let x := E.symm h
    let n := x.left
    let k := x.right
    let T : Aff F := SemidirectProduct.inl (Multiplicative.ofAdd s)
    have hdecomp : (h.1 : Aff F) = n.1.1 * k.1.1 := by
      have he := E.apply_symm_apply h
      rw [SemidirectProduct.mulEquivSubgroup_apply] at he
      exact congrArg (fun z : H ↦ (z.1 : Aff F)) he.symm
    have hnright : (n.1.1 : Aff F).right = 1 := n.2
    have hnconj : (T * n.1.1 * T⁻¹).left.toAdd = (n.1.1 : Aff F).left.toAdd := by
      rw [translation_conj_left]
      rw [hnright]
      simp
    have hkconj : (T * k.1.1 * T⁻¹).left.toAdd = 0 := hC0 k
    have hkleft : (T * k.1.1 * T⁻¹).left = 1 := by
      apply Multiplicative.ext
      exact hkconj
    have hconj : T * h.1 * T⁻¹ =
        (T * n.1.1 * T⁻¹) * (T * k.1.1 * T⁻¹) := by
      rw [hdecomp]
      group
    have hleft : (T * h.1 * T⁻¹).left.toAdd =
        (n.1.1 : Aff F).left.toAdd := by
      rw [hconj, SemidirectProduct.mul_left]
      simp only [toAdd_mul]
      rw [hnconj, hkleft]
      simp
    rw [hleft]
    exact ⟨Additive.ofMul n, rfl⟩
  by_cases hc1 : c = 1
  · refine ⟨0, finish 0 ?_⟩
    apply cyclic_translation_conj_left_eq_zero C c hc 0
    rw [hc1]
    simp
  · have hcright : (c.1.1 : Aff F).right ≠ 1 := by
      intro hright
      apply hc1
      apply hinj
      exact hright
    have hden : ((c.1.1 : Aff F).right : F) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hcright
      exact Units.ext h
    let s := (c.1.1 : Aff F).left.toAdd /
      (((c.1.1 : Aff F).right : F) - 1)
    refine ⟨s, finish s ?_⟩
    apply cyclic_translation_conj_left_eq_zero C c hc s
    rw [translation_conj_left]
    dsimp [s]
    field_simp [hden]
    ring

private lemma exists_affine_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (s : F) (γ : translationAddSubgroup H)
      (coord : H → multiplierSubfield (translationAddSubgroup H) × multiplierRange H),
      (γ : F) ≠ 0 ∧ Function.Bijective coord ∧
      ∀ h : H,
        (((coord h).1 : multiplierSubfield (translationAddSubgroup H)) : F) * γ.1 =
          ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
            (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd ∧
        (((((coord h).2.1 :
          (multiplierSubfield (translationAddSubgroup H))ˣ) :
            multiplierSubfield (translationAddSubgroup H)) : F)) =
          ((h.1 : Aff F).right : F) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    have hqone : 1 < p ^ m :=
      one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    omega
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite L := Finite.of_surjective (multiplierRangeHom H).rangeRestrict
    (multiplierRangeHom H).rangeRestrict_surjective
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  obtain ⟨γ, hγ⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have hγval : (γ : F) ≠ 0 := by
    intro h
    exact hγ (Subtype.ext h)
  let toΓ : M → Γ := fun a ↦ ⟨a.1 * γ.1, a.2 γ.1 γ.2⟩
  have htoΓ : Function.Bijective toΓ :=
    multiplier_mul_bijective Γ hΓ γ hγval (hMcard.trans hΓcard.symm)
  let eΓ : M ≃ Γ := Equiv.ofBijective toΓ htoΓ
  obtain ⟨s, hs⟩ := exists_translation_conj_left_mem H
  let normLeft (h : H) : Γ := ⟨
    ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd,
    hs h⟩
  let rangeCoord (h : H) : (rightRestrict H).range :=
    ⟨rightRestrict H h, ⟨h, rfl⟩⟩
  let coord : H → M × L := fun h ↦
    (eΓ.symm (normLeft h),
      ⟨multiplierRangeHom H (rangeCoord h), ⟨rangeCoord h, rfl⟩⟩)
  have hcoordInj : Function.Injective coord := by
    intro h k hhk
    have hleftCoord := congrArg Prod.fst hhk
    have hrightCoord := congrArg Prod.snd hhk
    have hnorm : normLeft h = normLeft k := eΓ.symm.injective hleftCoord
    have hrangeCoord : rangeCoord h = rangeCoord k := by
      apply multiplierRangeHom_injective H
      exact congrArg Subtype.val hrightCoord
    have hright : (h.1 : Aff F).right = (k.1 : Aff F).right :=
      congrArg (fun u : (rightRestrict H).range ↦ u.1) hrangeCoord
    let T : Aff F := SemidirectProduct.inl (Multiplicative.ofAdd s)
    have hconj : T * h.1 * T⁻¹ = T * k.1 * T⁻¹ := by
      apply SemidirectProduct.ext
      · exact Multiplicative.ext (congrArg Subtype.val hnorm)
      · simp [T, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hright]
    apply Subtype.ext
    exact (MulAut.conj T).injective hconj
  have hcoord : Function.Bijective coord := by
    let _ : Fintype H := Fintype.ofFinite H
    let _ : Fintype M := Fintype.ofFinite M
    let _ : Fintype L := Fintype.ofFinite L
    apply (Fintype.bijective_iff_injective_and_card coord).2
    refine ⟨hcoordInj, ?_⟩
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod, hHcard, hMcard,
      hLcard]
  refine ⟨s, γ, coord, hγval, hcoord, ?_⟩
  intro h
  constructor
  · have he := eΓ.apply_symm_apply (normLeft h)
    exact congrArg Subtype.val he
  · rfl

private lemma exists_affine_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield F) (c : GL (Fin 2) F) (L : Subgroup Mˣ)
      (coord : H → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Bijective coord ∧
      (∀ A : GL (Fin 2) F, A 1 0 ≠ 0 →
        ((c * A * c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) ∧
      ∀ h : H,
        c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
          Matrix.GeneralLinearGroup.map M.subtype
            (affineGL (coord h).1 (coord h).2.1) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  obtain ⟨s, γ, coord, hγ, hcoord, hform⟩ :=
    exists_affine_normal_form H m t hm hHcard hrange hsandwich
  let r : Fˣ := Units.mk0 (γ.1)⁻¹ (inv_ne_zero hγ)
  let T : GL (Fin 2) F := affineGL s 1
  let D : GL (Fin 2) F := affineGL 0 r
  let c : GL (Fin 2) F := D * T
  have hMfinite : Finite M := by
    apply multiplierSubfield_finite Γ
    intro hbot
    apply hγ
    have hmem : (γ : F) ∈ Γ := γ.2
    rw [hbot] at hmem
    exact hmem
  let _ : Finite M := hMfinite
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  refine ⟨M, c, L, coord, hMfinite, hMcard, hLcard, hcoord, ?_, ?_⟩
  · intro A hA
    have hcshape : c = affineGL ((r : F) * s) r := by
      dsimp [c, D, T]
      rw [affineGL_mul]
      simp
    rw [hcshape, affineGL_conj_lowerLeft]
    exact mul_ne_zero hA (inv_ne_zero r.ne_zero)
  intro h
  have hformh := hform h
  rw [translation_conj_left] at hformh
  have hconj : c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
      D * (T * affineGL h.1.left.toAdd h.1.right * T⁻¹) * D⁻¹ := by
    dsimp [c]
    group
  rw [hconj]
  change D * (affineGL s 1 * affineGL h.1.left.toAdd h.1.right *
    (affineGL s 1)⁻¹) * D⁻¹ = _
  rw [affineGL_translation_conj]
  change affineGL 0 r *
      affineGL (h.1.left.toAdd + (1 - (h.1.right : F)) * s) h.1.right *
      (affineGL 0 r)⁻¹ = _
  rw [affineGL_conj, affineGL_map_subfield]
  congr 2
  · change (γ.1)⁻¹ *
        (h.1.left.toAdd + (1 - (h.1.right : F)) * s) = ((coord h).1 : F)
    rw [← hformh.1]
    field_simp
  · apply Units.ext
    exact hformh.2.symm

private lemma kernel_orderOf_eq_char {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F))
    (z : (rightRestrict H).ker) (hz : z ≠ 1) : orderOf z = p := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply kernelLeft_injective H
    rw [map_pow, map_one]
    change Multiplicative.ofAdd (p • (kernelLeft H z).toAdd) = 1
    simp [nsmul_eq_mul]
  · exact hz

private lemma kernel_mul_comm {F : Type*} [Field F] (H : Subgroup (Aff F))
    (x y : (rightRestrict H).ker) : x * y = y * x := by
  apply kernelLeft_injective H
  simp only [map_mul]
  exact mul_comm _ _

private lemma right_eq_one_of_commutes_translation {F : Type*} [Field F]
    {a b : Aff F} (hbRight : b.right = 1) (hb : b ≠ 1) (hcomm : a * b = b * a) :
    a.right = 1 := by
  have hleft := congrArg SemidirectProduct.left hcomm
  have hfield : a.left.toAdd + (a.right : F) * b.left.toAdd =
      b.left.toAdd + a.left.toAdd := by
    have := congrArg Multiplicative.toAdd hleft
    simpa [SemidirectProduct.mul_left, hbRight, unitAction, Units.smul_def,
      smul_eq_mul] using this
  have hb0 : b.left.toAdd ≠ 0 := by
    intro hbLeft
    apply hb
    apply SemidirectProduct.ext
    · have := congrArg Multiplicative.ofAdd hbLeft
      simpa using this
    · exact hbRight
  have hprod : ((a.right : F) - 1) * b.left.toAdd = 0 := by
    linear_combination hfield
  have ha : (a.right : F) = 1 := by
    rcases mul_eq_zero.mp hprod with ha | hbzero
    · exact sub_eq_zero.mp ha
    · exact (hb0 hbzero).elim
  exact Units.ext ha

private lemma complement_action_fixedPointFree {F : Type*} [Field F]
    (H : Subgroup (Aff F)) (K : Subgroup H)
    (hK : (rightRestrict H).ker.IsComplement' K) :
    ∀ k : K, k ≠ 1 → ∀ n : (rightRestrict H).ker, n ≠ 1 →
      ((rightRestrict H).ker.normalizerMonoidHom.comp
        (Subgroup.inclusion ((rightRestrict H).ker.normalizer_eq_top ▸ le_top)) k) n ≠ n := by
  intro k hk n hn hfix
  let N := (rightRestrict H).ker
  have hconj : (k.1 : H) * (n.1 : H) * (k.1 : H)⁻¹ = (n.1 : H) :=
    Subtype.ext_iff.mp hfix
  have hcommH : (k.1 : H) * (n.1 : H) = (n.1 : H) * (k.1 : H) := by
    calc
      (k.1 : H) * (n.1 : H) = ((k.1 : H) * (n.1 : H) * (k.1 : H)⁻¹) * k.1 := by group
      _ = (n.1 : H) * k.1 := by rw [hconj]
  have hnAff : (n.1.1 : Aff F) ≠ 1 := by
    intro h
    apply hn
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hkRight : (k.1.1 : Aff F).right = 1 := by
    apply right_eq_one_of_commutes_translation n.2 hnAff
    exact congrArg (fun z : H ↦ (z.1 : Aff F)) hcommH
  have hkN : (k.1 : H) ∈ N := hkRight
  have hkbot : (k.1 : H) ∈ (⊥ : Subgroup H) := hK.disjoint.le_bot ⟨hkN, k.2⟩
  apply hk
  apply Subtype.ext
  exact hkbot

private lemma complement_card_dvd_kernel_card_sub_one {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] (K : Subgroup H)
    (hK : (rightRestrict H).ker.IsComplement' K) :
    Nat.card K ∣ Nat.card (rightRestrict H).ker - 1 := by
  classical
  let N := (rightRestrict H).ker
  let φ : K →* MulAut N := N.normalizerMonoidHom.comp
    (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
  let _ : MulAction K N := MulAction.compHom N φ
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype N := Fintype.ofFinite N
  have hfixed (k : K) : Fintype.card (MulAction.fixedBy N k) =
      if k = 1 then Fintype.card N else 1 := by
    by_cases hk : k = 1
    · subst k
      simp only [ite_true]
      have hset : MulAction.fixedBy N (1 : K) = Set.univ := by
        ext n
        simp
      exact (Fintype.card_congr (Set.equivOfEq hset)).trans (by simp)
    · have hset : MulAction.fixedBy N k = {1} := by
        ext n
        rw [MulAction.mem_fixedBy, Set.mem_singleton_iff]
        constructor
        · intro hkn
          by_contra hn
          exact complement_action_fixedPointFree H K hK k hk n hn hkn
        · rintro rfl
          change φ k (1 : N) = 1
          exact map_one (φ k)
      simp only [hk, ite_false]
      exact (Fintype.card_congr (Set.equivOfEq hset)).trans (by simp)
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group K N
  rw [show (∑ k : K, Fintype.card (MulAction.fixedBy N k)) =
      ∑ k : K, if k = 1 then Fintype.card N else 1 by
        apply Finset.sum_congr rfl
        intro k _
        exact hfixed k] at hburn
  have hsum : (∑ k : K, if k = 1 then Fintype.card N else 1) =
      Fintype.card N + (Fintype.card K - 1) := by
    calc
      (∑ k : K, if k = 1 then Fintype.card N else 1) =
          (if (1 : K) = 1 then Fintype.card N else 1) +
            ∑ i ∈ ({1}ᶜ : Finset K), if i = 1 then Fintype.card N else 1 :=
        Fintype.sum_eq_add_sum_compl (1 : K) _
      _ = Fintype.card N + ∑ _i ∈ ({1}ᶜ : Finset K), 1 := by
        simp only [eq_self, ite_true]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : i ≠ 1 := by simpa using hi
        simp [hi1]
      _ = Fintype.card N + ({1}ᶜ : Finset K).card := by simp
      _ = Fintype.card N + (Fintype.card K - 1) := by
        rw [Finset.card_compl, Finset.card_singleton]
  rw [hsum] at hburn
  let r := Fintype.card (Quotient (MulAction.orbitRel K N))
  change Fintype.card N + (Fintype.card K - 1) = r * Fintype.card K at hburn
  refine ⟨r - 1, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hKpos : 0 < Fintype.card K := Fintype.card_pos
  have hNpos : 0 < Fintype.card N := Fintype.card_pos
  calc
    Fintype.card N - 1 = r * Fintype.card K - Fintype.card K := by omega
    _ = (r - 1) * Fintype.card K := by
      rw [Nat.sub_mul, one_mul]
    _ = Fintype.card K * (r - 1) := Nat.mul_comm _ _

private lemma card_coprime_char_of_injective_units {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] {C : Type*} [Group C] [Finite C]
    (f : C →* Fˣ) (hf : Function.Injective f) : Nat.Coprime (Nat.card C) p := by
  apply Nat.Coprime.symm
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hp
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hp
  apply units_orderOf_ne_char (f c)
  rw [orderOf_injective f hf]
  exact hc

private lemma finite_subgroup_affine_classification {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (H : Subgroup (Aff F)) [Finite H]
    (hpH : p ∣ Nat.card H) :
    ∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (H ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ]
        Multiplicative (ZMod t)) := by
  let N := (rightRestrict H).ker
  let _ : N.Normal := MonoidHom.normal_ker (rightRestrict H)
  obtain ⟨K, hK, hKinj, hKcyc⟩ := exists_cyclic_complement H
  have hKcop : Nat.Coprime (Nat.card K) p :=
    card_coprime_char_of_injective_units ((rightRestrict H).domRestrict K) hKinj
  have hpN : p ∣ Nat.card N := by
    have hpProd : p ∣ Nat.card N * Nat.card K := by
      rw [hK.card_mul_card]
      exact hpH
    exact (Fact.out : p.Prime).dvd_mul.mp hpProd |>.resolve_right
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hKcop.symm)
  let _ : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp
    ((Fact.out : p.Prime).one_lt.trans_le (Nat.le_of_dvd (Nat.card_pos) hpN))
  obtain ⟨m, hm, ⟨eN⟩⟩ := elementaryAbelian_mulEquiv_fun N
    (kernel_mul_comm H) (kernel_orderOf_eq_char H)
  let t := Nat.card K
  let φ₀ : K →* MulAut N := N.normalizerMonoidHom.comp
    (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
  let eK : Multiplicative (ZMod t) ≃* K := zmodCyclicMulEquiv hKcyc
  let φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)) :=
    (MulAut.congr eN).toMonoidHom.comp (φ₀.comp eK.toMonoidHom)
  have htCop : Nat.Coprime t p := hKcop
  have hcardN : Nat.card N = p ^ m :=
    (Nat.card_congr eN.toEquiv).trans (by simp)
  have htDiv : t ∣ p ^ m - 1 := by
    have hdiv := complement_card_dvd_kernel_card_sub_one H K hK
    change Nat.card K ∣ Nat.card N - 1 at hdiv
    rw [hcardN] at hdiv
    exact hdiv
  have hφInj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hc₀ : φ₀ (eK c) = 1 := by
      apply (MulAut.congr eN).injective
      rw [map_one]
      exact hc
    have hkc : eK c = 1 := by
      by_contra hkc
      obtain ⟨n, hn⟩ := exists_ne (1 : N)
      apply complement_action_fixedPointFree H K hK (eK c) hkc n hn
      rw [hc₀]
      rfl
    exact eK.injective (hkc.trans eK.map_one.symm)
  have hφFree : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v := by
    intro c hc v hv hfix
    have heK : eK c ≠ 1 := by
      intro h
      apply hc
      exact eK.injective (h.trans eK.map_one.symm)
    let n : N := eN.symm v
    have hn : n ≠ 1 := by
      intro h
      apply hv
      calc
        v = eN n := (eN.apply_symm_apply v).symm
        _ = 1 := by rw [h, map_one]
    apply complement_action_fixedPointFree H K hK (eK c) heK n hn
    apply eN.injective
    change eN (φ₀ (eK c) (eN.symm v)) = v at hfix
    exact hfix.trans (eN.apply_symm_apply v).symm
  refine ⟨m, t, hm, htCop, htDiv, φ, hφInj, hφFree, ?_⟩
  let eSD : N ⋊[φ₀] K ≃*
      (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t) :=
    SemidirectProduct.congr' eN eK.symm
  exact ⟨(SemidirectProduct.mulEquivSubgroup hK).symm.trans eSD⟩

private lemma card_quadraticFiber_le_two {F : Type*} [Field F] (c : F) :
    Nat.card {x : F // x ^ 2 = c} ≤ 2 := by
  let q : F[X] := Polynomial.X ^ 2 - Polynomial.C c
  have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
  have hfinite : (q.rootSet F).Finite := by
    exact Finset.finite_toSet _
  let _ : Fintype (q.rootSet F) := hfinite.fintype
  let toRoot : {x : F // x ^ 2 = c} → q.rootSet F := fun x => ⟨x.1, by
    rw [Polynomial.mem_rootSet_of_ne hq0]
    simp [q, x.2]⟩
  have hinj : Function.Injective toRoot := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : q.rootSet F ↦ z.1) hxy)
  calc
    Nat.card {x : F // x ^ 2 = c} ≤ Nat.card (q.rootSet F) :=
      Nat.card_le_card_of_injective toRoot hinj
    _ = (q.rootSet F).ncard := Nat.card_coe_set_eq _
    _ ≤ q.natDegree := Polynomial.ncard_rootSet_le q F
    _ = 2 := Polynomial.natDegree_X_pow_sub_C

private lemma card_le_mul_card_of_fiber_le {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (n : ℕ) (hfiber : ∀ b, Nat.card {a : A // f a = b} ≤ n) :
    Nat.card A ≤ n * Nat.card B := by
  let _ : Fintype B := Fintype.ofFinite B
  let _ (b : B) : Fintype {a : A // f a = b} := Fintype.ofFinite _
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
    _ ≤ ∑ _b : B, n := Finset.sum_le_sum fun b _ ↦ hfiber b
    _ = n * Nat.card B := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

private lemma card_fiber_eq_of_le_of_card_eq_mul
    {A B : Type*} [Finite A] [Finite B] (f : A → B) (n : ℕ)
    (hfiber : ∀ b, Nat.card {a : A // f a = b} ≤ n)
    (hcard : Nat.card A = n * Nat.card B) :
    ∀ b, Nat.card {a : A // f a = b} = n := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  let _ (b : B) : Fintype {a : A // f a = b} := Fintype.ofFinite _
  have hsum : Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
    calc
      Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ b : B, Nat.card {a : A // f a = b} := Nat.card_sigma
  intro b
  apply Nat.le_antisymm (hfiber b)
  by_contra hnot
  have hlt : Nat.card {a : A // f a = b} < n := Nat.lt_of_not_ge hnot
  have hsumlt : (∑ x : B, Nat.card {a : A // f a = x}) < ∑ _x : B, n := by
    apply Finset.sum_lt_sum
    · intro x _
      exact hfiber x
    · exact ⟨b, Finset.mem_univ b, hlt⟩
  rw [← hsum, hcard] at hsumlt
  simp [Nat.card_eq_fintype_card, Nat.mul_comm] at hsumlt

private lemma subgroup_eq_square_range_of_card
    {F : Type*} [Field F] [Finite F] (L : Subgroup Fˣ) (q t : ℕ)
    (hFcard : Nat.card F = q) (hLcard : Nat.card L = t)
    (hhalf : 2 * t = q - 1) :
    L = (powMonoidHom 2 : Fˣ →* Fˣ).range := by
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  rw [hLcard, IsCyclic.card_powMonoidHom_range, Nat.card_units, hFcard, ← hhalf]
  norm_num [show (2 : ℕ) = 2 * 1 by omega, Nat.gcd_mul_left,
    Nat.mul_div_cancel_left]

private lemma trace_mul_affineGL {F : Type*} [Field F]
    (S : GL (Fin 2) F) (a : F) (u : Fˣ) :
    Matrix.trace (((S * affineGL a u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) =
      (S : Matrix (Fin 2) (Fin 2) F) 0 0 * (u : F) +
        (S : Matrix (Fin 2) (Fin 2) F) 1 0 * a +
        (S : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, affineGL]
  ring

private lemma det_mul_affineGL {F : Type*} [Field F]
    (S : GL (Fin 2) F) (a : F) (u : Fˣ) :
    Matrix.det (((S * affineGL a u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) =
      Matrix.det (S : Matrix (Fin 2) (Fin 2) F) * (u : F) := by
  change Matrix.det ((S : Matrix (Fin 2) (Fin 2) F) *
    (affineGL a u : Matrix (Fin 2) (Fin 2) F)) = _
  rw [Matrix.det_mul]
  simp [affineGL, Matrix.det_fin_two]

private lemma card_parabolic_borel_fiber_le_two {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] (u : Fˣ) :
    Nat.card {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤ 2 := by
  classical
  let c : F := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) F) * (u : F)
  let toRoot : {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} →
      {x : F // x ^ 2 = c} := fun h ↦ ⟨
    Matrix.trace (((S * affineGL (gamma h.1.1) (lambda h.1.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)), by
      rw [h.2.1]
      have hdisc := h.2.2.2
      rw [Matrix.discr_fin_two, h.2.1] at hdisc
      have heq := sub_eq_zero.mp hdisc
      rw [det_mul_affineGL] at heq
      simpa [c, mul_assoc] using heq⟩
  have hinj : Function.Injective toRoot := by
    intro x y hxy
    have htrace := congrArg (fun z : {w : F // w ^ 2 = c} ↦ z.1) hxy
    change Matrix.trace (((S * affineGL (gamma x.1.1) (lambda x.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      Matrix.trace (((S * affineGL (gamma y.1.1) (lambda y.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) at htrace
    rw [trace_mul_affineGL, trace_mul_affineGL, x.2.1, y.2.1] at htrace
    have hgamma : gamma x.1.1 = gamma y.1.1 := by
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    apply Subtype.ext
    apply Subtype.ext
    apply toAff_injective
    apply SemidirectProduct.ext
    · exact hgamma
    · exact x.2.1.trans y.2.1.symm
  let q : F[X] := Polynomial.X ^ 2 - Polynomial.C c
  have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
  have hfinite : Set.Finite {x : F | x ^ 2 = c} := by
    apply (Finset.finite_toSet (q.map (algebraMap F F)).roots.toFinset).subset
    intro x hx
    rw [show (q.map (algebraMap F F)).roots.toFinset = q.rootSet F by rfl,
      Polynomial.mem_rootSet_of_ne hq0]
    change x ^ 2 = c at hx
    simpa [q] using sub_eq_zero.mpr hx
  let _ : Fintype {x : F // x ^ 2 = c} := hfinite.fintype
  exact (Nat.card_le_card_of_injective toRoot hinj).trans
    (card_quadraticFiber_le_two c)

private lemma card_parabolic_borel_le_twice_range {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] :
    Nat.card {h : H //
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤
      2 * Nat.card (SemidirectProduct.rightHom.comp
        (toAff.comp H.subtype)).range := by
  classical
  let rhoH : H →* Fˣ := SemidirectProduct.rightHom.comp (toAff.comp H.subtype)
  let E := {h : H //
    (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).IsParabolic}
  let toRange : E → rhoH.range := fun h ↦ ⟨rhoH h.1, ⟨h.1, rfl⟩⟩
  let _ : Finite rhoH.range := Finite.of_surjective rhoH.rangeRestrict
    rhoH.rangeRestrict_surjective
  have hfiber (u : rhoH.range) : Nat.card {h : E // toRange h = u} ≤ 2 := by
    let toFixed : {h : E // toRange h = u} →
        {h : H // lambda h.1 = u.1 ∧
          (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)).IsParabolic} := fun h ↦
      ⟨h.1.1, congrArg (fun z : rhoH.range ↦ z.1) h.2, h.1.2⟩
    have hinj : Function.Injective toFixed := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z ↦ z.1) hxy
    exact (Nat.card_le_card_of_injective toFixed hinj).trans
      (card_parabolic_borel_fiber_le_two S hS10 H u.1)
  simpa [E, rhoH] using card_le_mul_card_of_fiber_le toRange 2 hfiber

end DicksonWildAffine

private lemma dicksonWild_sylow_ne_bot_of_dvd_card
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    (P : Sylow p A) (hp : p ∣ Nat.card A) : (P : Subgroup A) ≠ ⊥ := by
  have hfac : 0 < (Nat.card A).factorization p :=
    (Fact.out : p.Prime).factorization_pos_of_dvd (Nat.card_pos.ne') hp
  have hcard : 1 < Nat.card (P : Subgroup A) := by
    rw [P.card_eq_multiplicity]
    exact Nat.one_lt_pow hfac.ne' (Fact.out : p.Prime).one_lt
  intro hbot
  rw [hbot] at hcard
  simp at hcard

private lemma dicksonWild_frobenius_case_of_normal_sylow
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G)
    (P : Sylow p G) (hPnormal : (P : Subgroup G).Normal) :
    ∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ]
        Multiplicative (ZMod t)) := by
  classical
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hPne : (P : Subgroup G) ≠ ⊥ := dicksonWild_sylow_ne_bot_of_dvd_card P hpG
  have hPbarNe : Pbar ≠ ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).not.mpr hPne
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  obtain ⟨x, hx, hxUnique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  have hGfix (g : G) : (g : PGL p) • x = x := by
    apply hxUnique
    intro z
    obtain ⟨zP, hzP, hzEq⟩ := z.2
    let z' : P := ⟨g⁻¹ * zP * g, hPnormal.conj_mem' zP hzP g⟩
    have hz' := hx ⟨G.subtype z', ⟨z', z'.2, rfl⟩⟩
    calc
      (z : PGL p) • ((g : PGL p) • x) =
          (G.subtype zP) • ((g : PGL p) • x) := by rw [hzEq]
      _ =
          (g : PGL p) • ((G.subtype z') • x) := by
            rw [← mul_smul, ← mul_smul]
            congr 1
            dsimp [z']
            group
      _ = (g : PGL p) • x := by rw [hz']
  let c : OnePoint (K p) := (OnePoint.equivProjectivization (K p)).symm x
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  let τ : PGL p := Matrix.ProjGenLinGroup.mk T
  have hτx : τ • x = DicksonWildAffine.infinity (K p) := by
    have hc : OnePoint.equivProjectivization (K p) c = x := Equiv.apply_symm_apply _ _
    rw [← hc]
    change Matrix.ProjGenLinGroup.mk T •
      OnePoint.equivProjectivization (K p) c =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    calc
      Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
          OnePoint.equivProjectivization (K p) (T • c) :=
        (OnePoint.equivProjectivization_smul (g := T) c).symm
      _ = OnePoint.equivProjectivization (K p) OnePoint.infty :=
        congrArg (OnePoint.equivProjectivization (K p)) hT
  let a : MulAut (PGL p) := MulAut.conj τ
  let Gc : Subgroup (PGL p) := Subgroup.map a.toMonoidHom G
  have hGcBorel : Gc ≤ DicksonWildAffine.borel (K p) := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := hz
    apply MulAction.mem_stabilizer_iff.mpr
    change (a (g : PGL p)) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p)
    rw [← hτx]
    change (τ * (g : PGL p) * τ⁻¹) • (τ • x) = τ • x
    rw [mul_smul, mul_smul]
    simp only [inv_smul_smul]
    rw [show g • x = x from hGfix ⟨g, hg⟩]
  let Gb : Subgroup (DicksonWildAffine.borel (K p)) :=
    Gc.subgroupOf (DicksonWildAffine.borel (K p))
  let Ga : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom Gb
  let eG : G ≃* Gc := a.subgroupMap G
  let eB : Gb ≃* Gc := Subgroup.subgroupOfEquivOfLe hGcBorel
  let eA : Gb ≃* Ga := DicksonWildAffine.borelMulEquivAffine.subgroupMap Gb
  let e : G ≃* Ga := eG.trans (eB.symm.trans eA)
  let _ : Finite Ga := Finite.of_surjective e e.surjective
  have hpGa : p ∣ Nat.card Ga := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpG
  obtain ⟨m, t, hm, htp, htdiv, φ, hφinj, hφfree, ⟨eGa⟩⟩ :=
    DicksonWildAffine.finite_subgroup_affine_classification Ga hpGa
  exact ⟨m, t, hm, htp, htdiv, φ, hφinj, hφfree, ⟨e.trans eGa⟩⟩

private lemma dicksonWild_normalizer_affine_equiv
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ H : Subgroup (DicksonWildAffine.Aff (K p)),
      Nonempty ((Subgroup.normalizer (P : Set G)) ≃* H) := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hPne : (P : Subgroup G) ≠ ⊥ :=
    dicksonWild_sylow_ne_bot_of_dvd_card P hpG
  have hPbarNe : Pbar ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).not.mpr hPne
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  obtain ⟨x, hx, hxUnique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  have hNfix (n : N) : (n.1 : PGL p) • x = x := by
    apply hxUnique
    intro z
    obtain ⟨zP, hzP, hzEq⟩ := z.2
    have hninv : (n.1 : G)⁻¹ ∈ N := N.inv_mem n.2
    have hz' : (n.1 : G)⁻¹ * zP * n.1 ∈ (P : Subgroup G) := by
      simpa using (Subgroup.mem_normalizer_iff.mp hninv zP).mp hzP
    let z' : P := ⟨(n.1 : G)⁻¹ * zP * n.1, hz'⟩
    have hzFix := hx ⟨G.subtype z', ⟨z', z'.2, rfl⟩⟩
    calc
      (z : PGL p) • ((n.1 : PGL p) • x) =
          (G.subtype zP) • ((n.1 : PGL p) • x) := by rw [hzEq]
      _ = (n.1 : PGL p) • ((G.subtype z') • x) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        dsimp [z']
        group
      _ = (n.1 : PGL p) • x := by rw [hzFix]
  let c : OnePoint (K p) := (OnePoint.equivProjectivization (K p)).symm x
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  let τ : PGL p := Matrix.ProjGenLinGroup.mk T
  have hτx : τ • x = DicksonWildAffine.infinity (K p) := by
    have hc : OnePoint.equivProjectivization (K p) c = x := Equiv.apply_symm_apply _ _
    rw [← hc]
    change Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    calc
      Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
          OnePoint.equivProjectivization (K p) (T • c) :=
        (OnePoint.equivProjectivization_smul (g := T) c).symm
      _ = OnePoint.equivProjectivization (K p) OnePoint.infty :=
        congrArg (OnePoint.equivProjectivization (K p)) hT
  let a : MulAut (PGL p) := MulAut.conj τ
  let nToPGL : N →* PGL p := a.toMonoidHom.comp (G.subtype.comp N.subtype)
  let Nc : Subgroup (PGL p) := Subgroup.map nToPGL ⊤
  have hNcBorel : Nc ≤ DicksonWildAffine.borel (K p) := by
    intro z hz
    obtain ⟨n, -, rfl⟩ := hz
    apply MulAction.mem_stabilizer_iff.mpr
    change (a (n.1 : PGL p)) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p)
    rw [← hτx]
    change (τ * (n.1 : PGL p) * τ⁻¹) • (τ • x) = τ • x
    rw [mul_smul, mul_smul]
    simp only [inv_smul_smul]
    rw [hNfix]
  let Nb : Subgroup (DicksonWildAffine.borel (K p)) :=
    Nc.subgroupOf (DicksonWildAffine.borel (K p))
  let H : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom Nb
  let eNc : N ≃* Nc := Subgroup.topEquiv.symm.trans
    (Subgroup.equivMapOfInjective ⊤ nToPGL
      (a.injective.comp (G.subtype_injective.comp N.subtype_injective)))
  let eB : Nb ≃* Nc := Subgroup.subgroupOfEquivOfLe hNcBorel
  let eH : Nb ≃* H := DicksonWildAffine.borelMulEquivAffine.subgroupMap Nb
  exact ⟨H, ⟨eNc.trans (eB.symm.trans eH)⟩⟩

private lemma dicksonWild_normalizer_order_data
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ m t : ℕ, 1 ≤ m ∧ Nat.Coprime t p ∧ t ∣ p ^ m - 1 ∧
      Nat.card (P : Subgroup G) = p ^ m ∧
      Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨H, ⟨e⟩⟩ := dicksonWild_normalizer_affine_equiv G hpG P
  let _ : Finite H := Finite.of_surjective e e.surjective
  let PN : Subgroup N := (P : Subgroup G).subgroupOf N
  have hPNcard : Nat.card PN = Nat.card (P : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  let r := (Nat.card G).factorization p
  have hr : 1 ≤ r :=
    (Fact.out : p.Prime).dvd_iff_one_le_factorization (Nat.card_pos.ne') |>.mp hpG
  have hPcard : Nat.card (P : Subgroup G) = p ^ r := P.card_eq_multiplicity
  have hpN : p ∣ Nat.card N := by
    apply (show p ∣ Nat.card PN by
      rw [hPNcard, hPcard]
      exact dvd_pow_self p (by omega)).trans
    exact PN.card_subgroup_dvd_card
  have hpH : p ∣ Nat.card H := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpN
  obtain ⟨m, t, hm, htp, htdiv, φ, -, -, ⟨eH⟩⟩ :=
    DicksonWildAffine.finite_subgroup_affine_classification H hpH
  have hcardH : Nat.card H = p ^ m * t := by
    have hcardV : Nat.card (Multiplicative (Fin m → ZMod p)) = p ^ m := by
      change Nat.card (Fin m → ZMod p) = p ^ m
      rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    have hcardC : Nat.card (Multiplicative (ZMod t)) = t := by
      change Nat.card (ZMod t) = t
      exact Nat.card_zmod t
    rw [Nat.card_congr eH.toEquiv]
    rw [Nat.card_congr SemidirectProduct.equivProd]
    rw [Nat.card_prod, hcardV, hcardC]
  have hcardN : Nat.card N = p ^ m * t := by
    rw [Nat.card_congr e.toEquiv]
    exact hcardH
  have hNdivG : Nat.card N ∣ Nat.card G := N.card_subgroup_dvd_card
  have hmle : m ≤ r := by
    apply ((Fact.out : p.Prime).pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp
    apply dvd_trans (show p ^ m ∣ Nat.card N by
      rw [hcardN]
      exact dvd_mul_right _ _) hNdivG
  have hrle : r ≤ m := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    apply (htp.symm.pow_left r).dvd_of_dvd_mul_right
    have hprN : p ^ r ∣ Nat.card N := by
      rw [← hPcard, ← hPNcard]
      exact PN.card_subgroup_dvd_card
    rwa [hcardN] at hprN
  have hmr : m = r := Nat.le_antisymm hmle hrle
  have hPcardM : Nat.card (P : Subgroup G) = p ^ m := by rw [hPcard, hmr]
  exact ⟨m, t, hm, htp, htdiv, hPcardM, hcardN⟩

private lemma dicksonWild_distinct_sylow_inf_eq_bot
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P Q : Sylow p G) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  classical
  by_contra hInf
  let R : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
  let _ : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hInf
  obtain ⟨z, hz⟩ := exists_ne (1 : R)
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  let Qbar : Subgroup (PGL p) := Subgroup.map G.subtype (Q : Subgroup G)
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let eQ : (Q : Subgroup G) ≃* Qbar :=
    Subgroup.equivMapOfInjective (Q : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  let _ : Finite Qbar := Finite.of_surjective eQ eQ.surjective
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hQbar : IsPGroup p Qbar := Q.isPGroup'.map G.subtype
  have hPbarNe : Pbar ≠ ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).not.mpr (by
        intro h
        have : R = ⊥ := by simp [R, h]
        exact hInf this)
  have hQbarNe : Qbar ≠ ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup G)
      G.subtype_injective).not.mpr (by
        intro h
        have : R = ⊥ := by simp [R, h]
        exact hInf this)
  obtain ⟨x, hx, -⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  obtain ⟨y, hy, -⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Qbar hQbar hQbarNe
  let zP : P := ⟨z.1, z.2.1⟩
  let zQ : Q := ⟨z.1, z.2.2⟩
  let zPbar : Pbar := eP zP
  let zQbar : Qbar := eQ zQ
  have hzPbar : zPbar ≠ 1 := by
    intro h
    have hzP : zP = 1 := eP.injective (h.trans eP.map_one.symm)
    apply hz
    apply Subtype.ext
    change z.1 = 1
    exact congrArg (fun u : P ↦ (u.1 : G)) hzP
  have hzQbar : zQbar ≠ 1 := by
    intro h
    have hzQ : zQ = 1 := eQ.injective (h.trans eQ.map_one.symm)
    apply hz
    apply Subtype.ext
    change z.1 = 1
    exact congrArg (fun u : Q ↦ (u.1 : G)) hzQ
  let zA : PGL p := G.subtype z.1
  have hzPcoe : (zPbar : PGL p) = zA := rfl
  have hzQcoe : (zQbar : PGL p) = zA := rfl
  have hzorder : orderOf zA = p := by
    rw [← hzPcoe]
    exact dicksonWild_orderOf_coe_eq_char_of_isPGroup Pbar hPbar zPbar hzPbar
  have hxy : x = y := by
    obtain ⟨u, -, hu⟩ := dicksonWild_existsUnique_fixedPoint_of_orderOf_eq_char zA hzorder
    have hzx : zA • x = x := by rw [← hzPcoe]; exact hx zPbar
    have hzy : zA • y = y := by rw [← hzQcoe]; exact hy zQbar
    exact (hu x hzx).trans (hu y hzy).symm
  have hcomm (a : P) (b : Q) : (a.1 : G) * (b.1 : G) = b.1 * a.1 := by
    apply G.subtype_injective
    let abar : Pbar := eP a
    let bbar : Qbar := eQ b
    have hafix : (a.1 : PGL p) • x = x := by
      change (abar : PGL p) • x = x
      exact hx abar
    have hbfix : (b.1 : PGL p) • x = x := by
      rw [hxy]
      change (bbar : PGL p) • y = y
      exact hy bbar
    apply dicksonWild_commute_of_common_fixed_order_char x
      (a.1 : PGL p) (b.1 : PGL p) hafix hbfix
    · intro ha
      have habar : abar ≠ 1 := by
        intro h
        apply ha
        change G.subtype a.1 = 1
        exact congrArg Subtype.val h
      exact dicksonWild_orderOf_coe_eq_char_of_isPGroup Pbar hPbar abar habar
    · intro hb
      have hbbar : bbar ≠ 1 := by
        intro h
        apply hb
        change G.subtype b.1 = 1
        exact congrArg Subtype.val h
      exact dicksonWild_orderOf_coe_eq_char_of_isPGroup Qbar hQbar bbar hbbar
  have hPnormQ : (P : Subgroup G) ≤ Subgroup.normalizer (Q : Subgroup G) := by
    apply le_trans (b := Subgroup.centralizer (Q : Set G))
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm ⟨a, ha⟩ ⟨b, hb⟩).symm
    · exact Subgroup.centralizer_le_normalizer _
  have hsupP : (P : Subgroup G) ⊔ (Q : Subgroup G) = P := by
    apply P.is_maximal'
    · exact P.isPGroup'.to_sup_of_normal_right' Q.isPGroup' hPnormQ
    · exact le_sup_left
  have hQP : (Q : Subgroup G) ≤ P := by
    rw [← hsupP]
    exact le_sup_right
  have hSubgroups : (P : Subgroup G) = Q := Q.is_maximal' P.isPGroup' hQP
  exact hPQ (Sylow.ext hSubgroups)

private lemma dicksonWild_card_dvd_of_fixedPointFree_action
    (C X : Type*) [Group C] [Finite C] [Finite X] [MulAction C X]
    (hfree : ∀ c : C, c ≠ 1 → ∀ x : X, c • x ≠ x) :
    Nat.card C ∣ Nat.card X := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  let _ : Fintype X := Fintype.ofFinite X
  have hfixed (c : C) : Fintype.card (MulAction.fixedBy X c) =
      if c = 1 then Fintype.card X else 0 := by
    by_cases hc : c = 1
    · subst c
      simp only [ite_true]
      have hset : MulAction.fixedBy X (1 : C) = Set.univ := by
        ext x
        simp
      exact (Fintype.card_congr (Set.equivOfEq hset)).trans (by simp)
    · have hset : MulAction.fixedBy X c = ∅ := by
        ext x
        rw [MulAction.mem_fixedBy, Set.mem_empty_iff_false, iff_false]
        exact hfree c hc x
      simp only [hc, ite_false]
      exact (Fintype.card_congr (Set.equivOfEq hset)).trans (by simp)
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group C X
  rw [show (∑ c : C, Fintype.card (MulAction.fixedBy X c)) =
      ∑ c : C, if c = 1 then Fintype.card X else 0 by
        apply Finset.sum_congr rfl
        intro c _
        exact hfixed c] at hburn
  have hsum : (∑ c : C, if c = 1 then Fintype.card X else 0) =
      Fintype.card X := by simp
  rw [hsum] at hburn
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel C X)), ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hburn.trans (Nat.mul_comm _ _)

private lemma dicksonWild_card_sylow_eq_one_add_mul_card
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G) :
    ∃ f : ℕ, Nat.card (Sylow p G) = 1 + f * Nat.card (P : Subgroup G) := by
  classical
  let X := {Q : Sylow p G // Q ≠ P}
  let actionX : MulAction P X := {
    smul a Q := ⟨(a.1 : G) • Q.1, by
      intro h
      have hPfix : (a.1 : G)⁻¹ • P = P := by
        apply Sylow.smul_eq_iff_mem_normalizer.mpr
        exact Subgroup.le_normalizer (P.inv_mem a.2)
      have h' := congrArg (fun R : Sylow p G ↦ (a.1 : G)⁻¹ • R) h
      apply Q.2
      simpa [hPfix] using h'⟩
    one_smul Q := by
      apply Subtype.ext
      change (1 : G) • Q.1 = Q.1
      exact one_smul G Q.1
    mul_smul a b Q := by
      apply Subtype.ext
      exact mul_smul (a.1 : G) (b.1 : G) Q.1 }
  let _ : MulAction P X := actionX
  have hfree : ∀ a : P, a ≠ 1 → ∀ Q : X, a • Q ≠ Q := by
    intro a ha Q hfix
    have hsmul : (a.1 : G) • Q.1 = Q.1 := congrArg Subtype.val hfix
    have haNorm : (a.1 : G) ∈ Subgroup.normalizer (Q.1 : Subgroup G) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hsmul
    have haInf : (a.1 : G) ∈ (P : Subgroup G) ⊓ Subgroup.normalizer (Q.1 : Subgroup G) :=
      ⟨a.2, haNorm⟩
    have hInfNormalizer := IsPGroup.inf_normalizer_sylow P.isPGroup' Q.1
    have haPQ : (a.1 : G) ∈ (P : Subgroup G) ⊓ (Q.1 : Subgroup G) := by
      rw [← hInfNormalizer]
      exact haInf
    rw [dicksonWild_distinct_sylow_inf_eq_bot G P Q.1 Q.2.symm] at haPQ
    apply ha
    apply Subtype.ext
    exact haPQ
  have hdivX : Nat.card P ∣ Nat.card X :=
    dicksonWild_card_dvd_of_fixedPointFree_action P X hfree
  obtain ⟨f, hf⟩ := hdivX
  refine ⟨f, ?_⟩
  have hcardX : Nat.card X = Nat.card (Sylow p G) - 1 := by
    let _ : Fintype (Sylow p G) := Fintype.ofFinite (Sylow p G)
    let _ : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl (fun Q : Sylow p G ↦ Q = P) |>.trans (by simp)
  rw [hcardX] at hf
  have hSylowOne : 1 ≤ Nat.card (Sylow p G) := Nat.card_pos
  calc
    Nat.card (Sylow p G) = (Nat.card (Sylow p G) - 1) + 1 :=
      (Nat.sub_add_cancel hSylowOne).symm
    _ = Nat.card P * f + 1 := by rw [hf]
    _ = 1 + f * Nat.card P := by simp [Nat.mul_comm, Nat.add_comm]

private lemma dicksonWild_exists_sylow_mem_of_pow_char_eq_one
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A]
    (g : A) (hg : g ^ p = 1) : ∃ P : Sylow p A, g ∈ P := by
  have hzp : IsPGroup p (Subgroup.zpowers g) := by
    rw [IsPGroup.iff_orderOf]
    intro h
    have hhpow : (h : A) ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
      rw [← hk]
      calc
        (g ^ k) ^ p = (g ^ k) ^ (p : ℤ) := by rw [zpow_natCast]
        _ = g ^ (k * p) := (zpow_mul g k p).symm
        _ = g ^ ((p : ℤ) * k) := by rw [mul_comm]
        _ = (g ^ (p : ℤ)) ^ k := zpow_mul g p k
        _ = 1 := by rw [zpow_natCast, hg]; simp
    have hdvd : orderOf h ∣ p := by
      have hdvd' := orderOf_dvd_of_pow_eq_one hhpow
      rwa [Subgroup.orderOf_coe] at hdvd'
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with hone | hp
    · exact ⟨0, by simp [hone]⟩
    · exact ⟨1, by simpa using hp⟩
  obtain ⟨P, hle⟩ := hzp.exists_le_sylow
  exact ⟨P, hle (Subgroup.mem_zpowers g)⟩

private lemma dicksonWild_orderOf_coe_eq_char_of_isPGroup_in_subgroup
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) {Q : Subgroup G} [Finite Q] (hQ : IsPGroup p Q)
    (g : Q) (hg : g ≠ 1) : orderOf (g.1 : PGL p) = p := by
  classical
  let Qbar : Subgroup (PGL p) := Subgroup.map G.subtype Q
  let eQ : Q ≃* Qbar := Subgroup.equivMapOfInjective Q G.subtype G.subtype_injective
  let _ : Finite Qbar := Finite.of_surjective eQ eQ.surjective
  have hQbar : IsPGroup p Qbar := hQ.map G.subtype
  let gbar : Qbar := eQ g
  have hgbar : gbar ≠ 1 := by
    intro h
    apply hg
    exact eQ.injective (h.trans eQ.map_one.symm)
  change orderOf (gbar : PGL p) = p
  exact dicksonWild_orderOf_coe_eq_char_of_isPGroup Qbar hQbar gbar hgbar

private lemma dicksonWild_sylow_eq_of_common_fixedPoint
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P Q : Sylow p G)
    (x : Projectivization (K p) (Fin 2 → K p))
    (hPfix : ∀ a : P, (a.1 : PGL p) • x = x)
    (hQfix : ∀ b : Q, (b.1 : PGL p) • x = x) : P = Q := by
  have hcomm (a : P) (b : Q) : (a.1 : G) * (b.1 : G) = b.1 * a.1 := by
    apply G.subtype_injective
    apply dicksonWild_commute_of_common_fixed_order_char x
      (a.1 : PGL p) (b.1 : PGL p) (hPfix a) (hQfix b)
    · intro ha
      have ha' : a ≠ 1 := by
        intro h
        apply ha
        exact congrArg (fun z : P ↦ (z.1 : PGL p)) h
      exact dicksonWild_orderOf_coe_eq_char_of_isPGroup_in_subgroup G
        P.isPGroup' a ha'
    · intro hb
      have hb' : b ≠ 1 := by
        intro h
        apply hb
        exact congrArg (fun z : Q ↦ (z.1 : PGL p)) h
      exact dicksonWild_orderOf_coe_eq_char_of_isPGroup_in_subgroup G
        Q.isPGroup' b hb'
  have hPnormQ : (P : Subgroup G) ≤ Subgroup.normalizer (Q : Subgroup G) := by
    apply le_trans (b := Subgroup.centralizer (Q : Set G))
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm ⟨a, ha⟩ ⟨b, hb⟩).symm
    · exact Subgroup.centralizer_le_normalizer _
  have hsupP : (P : Subgroup G) ⊔ (Q : Subgroup G) = P := by
    apply P.is_maximal'
    · exact P.isPGroup'.to_sup_of_normal_right' Q.isPGroup' hPnormQ
    · exact le_sup_left
  have hQP : (Q : Subgroup G) ≤ P := by
    rw [← hsupP]
    exact le_sup_right
  have hSubgroups : (P : Subgroup G) = Q := Q.is_maximal' P.isPGroup' hQP
  exact Sylow.ext hSubgroups

private lemma dicksonWild_mem_normalizer_iff_fixedPoint
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G)
    (x : Projectivization (K p) (Fin 2 → K p))
    (hPfix : ∀ a : P, (a.1 : PGL p) • x = x)
    (hPunique : ∀ y, (∀ a : P, (a.1 : PGL p) • y = y) → y = x)
    (g : G) :
    g ∈ Subgroup.normalizer (P : Set G) ↔ (g : PGL p) • x = x := by
  constructor
  · intro hg
    have hginvNorm : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.normalizer (P : Set G)).inv_mem hg
    apply hPunique
    intro a
    have hconj : g⁻¹ * (a.1 : G) * g ∈ (P : Subgroup G) := by
      simpa using
        ((Subgroup.mem_normalizer_iff.mp hginvNorm (a.1 : G)).mp a.2)
    let b : P := ⟨g⁻¹ * (a.1 : G) * g, hconj⟩
    change (a.1 : PGL p) • ((g : PGL p) • x) = (g : PGL p) • x
    calc
      (a.1 : PGL p) • ((g : PGL p) • x) =
          (g : PGL p) • ((b.1 : PGL p) • x) := by
            rw [← mul_smul, ← mul_smul]
            congr 1
            exact congrArg (fun z : G ↦ (z : PGL p))
              (show (a.1 : G) * g = g * (g⁻¹ * (a.1 : G) * g) by group)
      _ = (g : PGL p) • x := by rw [hPfix b]
  · intro hgfix
    let Q : Sylow p G := g • P
    have hQfix (b : Q) : (b.1 : PGL p) • x = x := by
      have hb : b.1 ∈ Subgroup.map (MulAut.conj g).toMonoidHom (P : Subgroup G) := by
        have hb' := b.2
        change b.1 ∈ ((g • P : Sylow p G) : Subgroup G) at hb'
        have hcoe : ((g • P : Sylow p G) : Subgroup G) =
            Subgroup.map (MulAut.conj g).toMonoidHom (P : Subgroup G) := by
          rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
          rfl
        rw [hcoe] at hb'
        exact hb'
      obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hb
      have hginvfix : ((g⁻¹ : G) : PGL p) • x = x := by
        calc
          ((g⁻¹ : G) : PGL p) • x =
              ((g⁻¹ : G) : PGL p) • ((g : PGL p) • x) :=
            congrArg (fun y ↦ ((g⁻¹ : G) : PGL p) • y) hgfix.symm
          _ = x := inv_smul_smul (g : PGL p) x
      have habG : g * a * g⁻¹ = b.1 := by
        change (MulAut.conj g) a = b.1 at hab
        rw [MulAut.conj_apply] at hab
        exact hab
      have habPGL : (b.1 : PGL p) =
          (g : PGL p) * (a : PGL p) * ((g⁻¹ : G) : PGL p) := by
        simpa using congrArg (fun z : G ↦ (z : PGL p)) habG.symm
      rw [habPGL, mul_smul, mul_smul, hginvfix, hPfix ⟨a, ha⟩, hgfix]
    have hQP : Q = P := dicksonWild_sylow_eq_of_common_fixedPoint G Q P x hQfix hPfix
    exact Sylow.smul_eq_iff_mem_normalizer.mp hQP

private lemma dicksonWild_normalizer_borel_coordinates
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ (a : MulAut (PGL p))
      (B : Subgroup (DicksonWildAffine.borel (K p)))
      (e : Subgroup.normalizer (P : Set G) ≃* B),
      (∀ n, ((e n).1 : PGL p) = a (n.1 : PGL p)) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        (DicksonWildAffine.lift (a (g : PGL p)) :
          Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hPbarNe : Pbar ≠ ⊥ := by
    change Subgroup.map G.subtype (P : Subgroup G) ≠ ⊥
    intro h
    apply dicksonWild_sylow_ne_bot_of_dvd_card P hpG
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).mp h
  obtain ⟨x, hx, hunique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  have hPfix (z : P) : (z.1 : PGL p) • x = x := by
    change (eP z : PGL p) • x = x
    exact hx (eP z)
  have hPunique (y : Projectivization (K p) (Fin 2 → K p))
      (hy : ∀ z : P, (z.1 : PGL p) • y = y) : y = x := by
    apply hunique
    intro z
    obtain ⟨w, rfl⟩ := eP.surjective z
    exact hy w
  let c : OnePoint (K p) := (OnePoint.equivProjectivization (K p)).symm x
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  let τ : PGL p := Matrix.ProjGenLinGroup.mk T
  have hτx : τ • x = DicksonWildAffine.infinity (K p) := by
    have hc : OnePoint.equivProjectivization (K p) c = x := Equiv.apply_symm_apply _ _
    rw [← hc]
    change Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    calc
      Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
          OnePoint.equivProjectivization (K p) (T • c) :=
        (OnePoint.equivProjectivization_smul (g := T) c).symm
      _ = OnePoint.equivProjectivization (K p) OnePoint.infty :=
        congrArg (OnePoint.equivProjectivization (K p)) hT
  let a : MulAut (PGL p) := MulAut.conj τ
  let nToB : N →* DicksonWildAffine.borel (K p) :=
    { toFun := fun n ↦ ⟨a (n.1 : PGL p), by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [← hτx]
        have hnfix : (n.1 : PGL p) • x = x :=
          (dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique n.1).mp n.2
        change (τ * (n.1 : PGL p) * τ⁻¹) • (τ • x) = τ • x
        simp only [mul_smul]
        rw [inv_smul_smul, hnfix]⟩
      map_one' := Subtype.ext (map_one a)
      map_mul' := fun n m ↦ Subtype.ext (map_mul a (n.1 : PGL p) (m.1 : PGL p)) }
  have hnToBInj : Function.Injective nToB := by
    intro n m hnm
    apply Subtype.ext
    apply G.subtype_injective
    apply a.injective
    exact congrArg (fun z : DicksonWildAffine.borel (K p) ↦ (z.1 : PGL p)) hnm
  let B : Subgroup (DicksonWildAffine.borel (K p)) := nToB.range
  let e : N ≃* B := MonoidHom.ofInjective hnToBInj
  refine ⟨a, B, e, fun n ↦ rfl, ?_⟩
  intro g hg hzero
  let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hAfix : A • (OnePoint.infty : OnePoint (K p)) = OnePoint.infty :=
    OnePoint.smul_infty_eq_self_iff.mpr hzero
  have hagfix : a (g : PGL p) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p) := by
    have h := congrArg (OnePoint.equivProjectivization (K p)) hAfix
    rw [OnePoint.equivProjectivization_smul] at h
    rw [← DicksonWildAffine.mk_lift (a (g : PGL p))]
    simpa [A, DicksonWildAffine.infinity] using h
  have hconjfix : a (g : PGL p) • (τ • x) = τ • x := by
    rw [hτx]
    exact hagfix
  have hleft : τ • ((g : PGL p) • x) = τ • x := by
    calc
      τ • ((g : PGL p) • x) = a (g : PGL p) • (τ • x) := by
        change τ • ((g : PGL p) • x) =
          (τ * (g : PGL p) * τ⁻¹) • (τ • x)
        simp [mul_smul]
      _ = τ • x := hconjfix
  have hgfix : (g : PGL p) • x = x := smul_left_cancel τ hleft
  exact hg ((dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique g).mpr hgfix)

private lemma dicksonWild_affine_right_range_card
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (DicksonWildAffine.Aff (K p))) [Finite H]
    (m t : ℕ) (htp : Nat.Coprime t p)
    (hcard : Nat.card H = p ^ m * t) :
    Nat.card (DicksonWildAffine.rightRestrict H).range = t := by
  let R := (DicksonWildAffine.rightRestrict H).range
  let _ : Finite R := Finite.of_surjective
    (DicksonWildAffine.rightRestrict H).rangeRestrict
    (DicksonWildAffine.rightRestrict H).rangeRestrict_surjective
  obtain ⟨r, hker⟩ := (DicksonWildAffine.kernel_isPGroup H).exists_card_eq
  have hprod : Nat.card (DicksonWildAffine.rightRestrict H).ker * Nat.card R =
      Nat.card H := by
    rw [← Subgroup.index_ker]
    exact (DicksonWildAffine.rightRestrict H).ker.card_mul_index
  have hpr : Nat.Coprime (p ^ r) t := htp.symm.pow_left r
  have hps : Nat.Coprime (p ^ m) (Nat.card R) :=
    (DicksonWildAffine.range_card_coprime_char H).pow_left m
  have hrle : r ≤ m := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    apply hpr.dvd_of_dvd_mul_right
    rw [← hcard, ← hprod, hker]
    exact dvd_mul_right _ _
  have hmle : m ≤ r := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    apply hps.dvd_of_dvd_mul_right
    rw [← hker, hprod, hcard]
    exact dvd_mul_right _ _
  have hrm : r = m := Nat.le_antisymm hrle hmle
  rw [hker, hcard, hrm] at hprod
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos m) hprod

private lemma dicksonWild_borel_multiplier_range_card
    {p : ℕ} [Fact p.Prime]
    (B : Subgroup (DicksonWildAffine.borel (K p))) [Finite B]
    (m t : ℕ) (htp : Nat.Coprime t p)
    (hcard : Nat.card B = p ^ m * t) :
    Nat.card (SemidirectProduct.rightHom.comp
      (DicksonWildAffine.toAff.comp B.subtype)).range = t := by
  let H : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom B
  let e : B ≃* H := DicksonWildAffine.borelMulEquivAffine.subgroupMap B
  let _ : Finite H := Finite.of_surjective e e.surjective
  have hcardH : Nat.card H = p ^ m * t := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcard
  have hrange : (SemidirectProduct.rightHom.comp
        (DicksonWildAffine.toAff.comp B.subtype)).range =
      (DicksonWildAffine.rightRestrict H).range := by
    ext u
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨e b, ?_⟩
      rfl
    · rintro ⟨h, rfl⟩
      obtain ⟨b, rfl⟩ := e.surjective h
      exact ⟨b, rfl⟩
  rw [hrange]
  exact dicksonWild_affine_right_range_card H m t htp hcardH

private lemma dicksonWild_card_order_char_in_normalizer_coset_le
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  have hBcard : Nat.card B = p ^ m * t := by
    rw [← Nat.card_congr e.toEquiv]
    exact hNcard
  let S : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := hout g hg
  let toParabolic : {n : N // (g * (n.1 : G)) ^ p = 1} →
      {b : B // (S * DicksonWildAffine.affineGL
        (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} := fun n ↦
    ⟨e n.1, by
      let z : G := g * (n.1.1 : G)
      have hzNe : z ≠ 1 := by
        intro hz
        apply hg
        have hgn : g = (n.1.1 : G)⁻¹ := by
          change g * (n.1.1 : G) = 1 at hz
          exact eq_inv_of_mul_eq_one_left hz
        rw [hgn]
        exact N.inv_mem n.1.2
      have hzOrderG : orderOf z = p := orderOf_eq_prime n.2 hzNe
      have hzOrder : orderOf (z : PGL p) = p := by
        exact (orderOf_injective G.subtype G.subtype_injective z).trans hzOrderG
      have haOrder : orderOf (a (z : PGL p)) = p := by
        rw [MulEquiv.orderOf_eq]
        exact hzOrder
      have hmk : Matrix.ProjGenLinGroup.mk
          (S * DicksonWildAffine.affineGL
            (DicksonWildAffine.gamma (e n.1).1)
            (DicksonWildAffine.lambda (e n.1).1)) = a (z : PGL p) := by
        calc
          Matrix.ProjGenLinGroup.mk
              (S * DicksonWildAffine.affineGL
                (DicksonWildAffine.gamma (e n.1).1)
                (DicksonWildAffine.lambda (e n.1).1)) =
              Matrix.ProjGenLinGroup.mk S * (e n.1).1 := by
            rw [map_mul, DicksonWildAffine.mk_affineGL_gamma_lambda]
          _ = a (g : PGL p) * a (n.1.1 : PGL p) := by
            rw [DicksonWildAffine.mk_lift]
            congr 1
            exact he n.1
          _ = a (z : PGL p) := by
            exact (map_mul a (g : PGL p) (n.1.1 : PGL p)).symm
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact haOrder⟩
  have htoInj : Function.Injective toParabolic := by
    intro n r hnr
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z ↦ z.1) hnr
  calc
    Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} ≤
        Nat.card {b : B // (S * DicksonWildAffine.affineGL
          (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} :=
      Nat.card_le_card_of_injective toParabolic htoInj
    _ ≤ 2 * Nat.card (SemidirectProduct.rightHom.comp
        (DicksonWildAffine.toAff.comp B.subtype)).range :=
      DicksonWildAffine.card_parabolic_borel_le_twice_range S hS10 B
    _ = 2 * t := by
      rw [dicksonWild_borel_multiplier_range_card B m t htp hBcard]

private lemma dicksonWild_card_order_char_outside_normalizer
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G)
    (m f : ℕ) (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1)) :
    Nat.card {g : G // g ∉ Subgroup.normalizer (P : Set G) ∧ g ^ p = 1} =
      f * p ^ m * (p ^ m - 1) := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let E := {g : G // g ≠ 1 ∧ g ^ p = 1}
  let Ein := {g : E // g.1 ∈ N}
  let Eout := {g : E // g.1 ∉ N}
  let O := {g : G // g ∉ N ∧ g ^ p = 1}
  let toEout : O → Eout := fun g ↦ ⟨⟨g.1, ⟨by
    intro hg1
    apply g.2.1
    rw [hg1]
    exact N.one_mem, g.2.2⟩⟩, g.2.1⟩
  have htoEout : Function.Bijective toEout := by
    constructor
    · intro g h hgh
      exact Subtype.ext (congrArg (fun z : Eout ↦ z.1.1) hgh)
    · intro g
      exact ⟨⟨g.1.1, g.2, g.1.2.2⟩, Subtype.ext rfl⟩
  have hOcard : Nat.card O = Nat.card Eout :=
    Nat.card_congr (Equiv.ofBijective toEout htoEout)
  let Pne := {g : (P : Subgroup G) // g ≠ 1}
  let toEin : Pne → Ein := fun g ↦ ⟨⟨g.1.1, ⟨by
    intro h
    apply g.2
    exact Subtype.ext h, by
    apply G.subtype_injective
    change (g.1.1 : PGL p) ^ p = 1
    exact (orderOf_eq_prime_iff.mp
      (dicksonWild_orderOf_coe_eq_char_of_isPGroup_in_subgroup G
        P.isPGroup' g.1 g.2)).1⟩⟩, Subgroup.le_normalizer g.1.2⟩
  have htoEin : Function.Bijective toEin := by
    constructor
    · intro g h hgh
      exact Subtype.ext (Subtype.ext (congrArg (fun z : Ein ↦ z.1.1) hgh))
    · intro z
      obtain ⟨Q, hzQ⟩ := dicksonWild_exists_sylow_mem_of_pow_char_eq_one z.1.1 z.1.2.2
      have hzInf : z.1.1 ∈ (Q : Subgroup G) ⊓ Subgroup.normalizer (P : Subgroup G) :=
        ⟨hzQ, z.2⟩
      have hzP : z.1.1 ∈ (P : Subgroup G) := by
        have heq : (Q : Subgroup G) ⊓ Subgroup.normalizer (P : Subgroup G) =
            (Q : Subgroup G) ⊓ (P : Subgroup G) :=
          IsPGroup.inf_normalizer_sylow Q.isPGroup' P
        rw [heq] at hzInf
        exact hzInf.2
      let zp : P := ⟨z.1.1, hzP⟩
      have hzpNe : zp ≠ 1 := by
        intro h
        apply z.1.2.1
        exact congrArg (fun w : P ↦ (w.1 : G)) h
      exact ⟨⟨zp, hzpNe⟩, Subtype.ext (Subtype.ext rfl)⟩
  have hPneCard : Nat.card Pne = p ^ m - 1 := by
    let _ : Fintype (P : Subgroup G) := Fintype.ofFinite (P : Subgroup G)
    let _ : Fintype Pne := Fintype.ofFinite Pne
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card Pne = Fintype.card (P : Subgroup G) - 1 :=
        Fintype.card_subtype_compl (fun g : (P : Subgroup G) ↦ g = 1) |>.trans
          (by simp)
      _ = p ^ m - 1 := by
        rw [← Nat.card_eq_fintype_card, hPcard]
  have hEinCard : Nat.card Ein = p ^ m - 1 := by
    rw [← hPneCard]
    exact (Nat.card_congr (Equiv.ofBijective toEin htoEin)).symm
  have hEoutCard : Nat.card Eout = Nat.card E - Nat.card Ein := by
    let _ : Fintype E := Fintype.ofFinite E
    let _ : Fintype Ein := Fintype.ofFinite Ein
    let _ : Fintype Eout := Fintype.ofFinite Eout
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl (fun g : E ↦ g.1 ∈ N)
  rw [hOcard, hEoutCard, show Nat.card E =
    (1 + f * p ^ m) * (p ^ m - 1) by exact hcount, hEinCard]
  have hfactor : (1 + f * p ^ m) * (p ^ m - 1) =
      f * p ^ m * (p ^ m - 1) + (p ^ m - 1) := by ring
  rw [hfactor, Nat.add_sub_cancel]

private lemma dicksonWild_sandwich_bound
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1)) :
    p ^ m - 1 ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {g : G // g ∉ N ∧ g ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun g ↦ ⟨Quotient.mk'' g.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N g.1 1 := Quotient.exact hq
    have hginv : g.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact g.2.1 (by simpa using N.inv_mem hginv)⟩
  have hfiber (c : C) : Nat.card {g : O // coset g = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {g : O // coset g = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun g ↦
      ⟨⟨s⁻¹ * g.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun z : C ↦ z.1) g.2).symm⟩, by
        simpa [mul_assoc] using g.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro g h hgh
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg (fun z : {n : N // (s * (n.1 : G)) ^ p = 1} ↦
        (z.1 : G)) hgh
      change s⁻¹ * g.1.1 = s⁻¹ * h.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hupper : Nat.card O ≤ 2 * t * Nat.card C :=
    DicksonWildAffine.card_le_mul_card_of_fiber_le coset (2 * t) hfiber
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  rw [hOcard, hCcard] at hupper
  apply Nat.le_of_mul_le_mul_left (c := f * p ^ m)
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hupper
  · exact mul_pos hf (pow_pos (Fact.out : p.Prime).pos m)

private lemma dicksonWild_card_order_char_in_normalizer_coset_eq
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} = 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {z : G // z ∉ N ∧ z ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun z ↦ ⟨Quotient.mk'' z.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N z.1 1 := Quotient.exact hq
    have hzinv : z.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact z.2.1 (by simpa using N.inv_mem hzinv)⟩
  have hfiber (c : C) : Nat.card {z : O // coset z = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {z : O // coset z = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun z ↦
      ⟨⟨s⁻¹ * z.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun w : C ↦ w.1) z.2).symm⟩, by
        simpa [mul_assoc] using z.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg
        (fun n : {n : N // (s * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
      change s⁻¹ * z.1.1 = s⁻¹ * w.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  have htotal : Nat.card O = 2 * t * Nat.card C := by
    rw [hOcard, hCcard, hhalf]
    ring
  have hfiberEq : ∀ c : C, Nat.card {z : O // coset z = c} = 2 * t :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul coset (2 * t) hfiber htotal
  let cg : C := ⟨Quotient.mk'' g, by
    intro hq
    have hrel : QuotientGroup.leftRel N g 1 := Quotient.exact hq
    have hginv : g⁻¹ ∈ N := by simpa using QuotientGroup.leftRel_apply.mp hrel
    exact hg (by simpa using N.inv_mem hginv)⟩
  let toN : {z : O // coset z = cg} →
      {n : N // (g * (n.1 : G)) ^ p = 1} := fun z ↦
    ⟨⟨g⁻¹ * z.1.1, by
      apply QuotientGroup.leftRel_apply.mp
      apply Quotient.exact
      exact congrArg (fun w : C ↦ w.1) z.2 |>.symm⟩, by
      simpa [mul_assoc] using z.1.2.2⟩
  have htoN : Function.Injective toN := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg
      (fun n : {n : N // (g * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
    change g⁻¹ * z.1.1 = g⁻¹ * w.1.1 at hv
    exact mul_left_cancel hv
  have hlower : 2 * t ≤ Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} := by
    rw [← hfiberEq cg]
    exact Nat.card_le_card_of_injective toN htoN
  exact Nat.le_antisymm
    (dicksonWild_card_order_char_in_normalizer_coset_le
      G hpG P m t htp hNcard g hg) hlower

private lemma dicksonWild_eq_or_two_mul_eq_of_dvd_of_le
    (n t : ℕ) (hn : 0 < n) (ht : 0 < t) (hdiv : t ∣ n) (hle : n ≤ 2 * t) :
    t = n ∨ 2 * t = n := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := by
    by_contra hk
    have : k = 0 := Nat.eq_zero_of_not_pos hk
    simp [this] at hn
  have hk2 : k ≤ 2 := by
    apply Nat.le_of_mul_le_mul_left (c := t)
    · simpa [Nat.mul_comm] using hle
    · exact ht
  interval_cases k <;> simp_all [Nat.mul_comm]

private lemma dicksonWild_exists_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield (K p)) (L : Subgroup Mˣ) (j : G →* PGL p)
      (coord : Subgroup.normalizer (P : Set G) → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Injective j ∧ Function.Bijective coord ∧
      (∀ n : Subgroup.normalizer (P : Set G),
        j n.1 = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1))) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
          (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  let H : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom B
  let eH : B ≃* H := DicksonWildAffine.borelMulEquivAffine.subgroupMap B
  let _ : Finite H := Finite.of_surjective eH eH.surjective
  have hHcard : Nat.card H = p ^ m * t := by
    rw [← Nat.card_congr eH.toEquiv, ← Nat.card_congr e.toEquiv]
    exact hNcard
  have hrange : Nat.card (DicksonWildAffine.rightRestrict H).range = t :=
    dicksonWild_affine_right_range_card H m t htp hHcard
  obtain ⟨M, c, L, coordH, hMfinite, hMcard, hLcard, hcoordH, hlower, hmatrix⟩ :=
    DicksonWildAffine.exists_affine_matrix_normal_form H m t hm hHcard hrange hsandwich
  let κ : PGL p := Matrix.ProjGenLinGroup.mk c
  let j : G →* PGL p :=
    (MulAut.conj κ).toMonoidHom.comp (a.toMonoidHom.comp G.subtype)
  let coord : N → M × L := fun n ↦ coordH (eH (e n))
  have hj : Function.Injective j :=
    (MulAut.conj κ).injective.comp (a.injective.comp G.subtype_injective)
  have hcoord : Function.Bijective coord :=
    hcoordH.comp (eH.bijective.comp e.bijective)
  refine ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, ?_, ?_⟩
  · intro n
    let b : B := e n
    let h : H := eH b
    have hmat := hmatrix h
    have hb : (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
        (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by
      calc
        (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (DicksonWildAffine.gamma b.1)
              (DicksonWildAffine.lambda b.1)) :=
          (DicksonWildAffine.mk_affineGL_gamma_lambda b.1).symm
        _ = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by rfl
    calc
      j n.1 = κ * a (n.1 : PGL p) * κ⁻¹ := rfl
      _ = Matrix.ProjGenLinGroup.mk c * b.1 *
          (Matrix.ProjGenLinGroup.mk c)⁻¹ := by rw [he n]
      _ = Matrix.ProjGenLinGroup.mk
          (c * DicksonWildAffine.affineGL h.1.left.toAdd h.1.right * c⁻¹) := by
        simp only [map_mul, map_inv]
        rw [hb]
      _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map M.subtype
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        exact congrArg Matrix.ProjGenLinGroup.mk hmat
      _ = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        rw [Matrix.ProjGenLinGroup.map_mk]
  · intro g hg
    let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
    let S : GL (Fin 2) (K p) := c * A * c⁻¹
    refine ⟨S, ?_, hlower A (hout g hg)⟩
    calc
      Matrix.ProjGenLinGroup.mk S = Matrix.ProjGenLinGroup.mk c *
          Matrix.ProjGenLinGroup.mk A * (Matrix.ProjGenLinGroup.mk c)⁻¹ := by
        simp [S]
      _ = κ * a (g : PGL p) * κ⁻¹ := by
        rw [DicksonWildAffine.mk_lift]
      _ = j g := rfl

private noncomputable def dicksonWildPoint {F : Type*} [Field F] [DecidableEq F] (z : F) :
    Projectivization F (Fin 2 → F) :=
  OnePoint.equivProjectivization F (z : OnePoint F)

private lemma dicksonWild_mk_smul_infinity {F : Type*} [Field F] [DecidableEq F]
    (S : GL (Fin 2) F) (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    Matrix.ProjGenLinGroup.mk S • DicksonWildAffine.infinity F =
      dicksonWildPoint (S 0 0 / S 1 0) := by
  change S • OnePoint.equivProjectivization F (OnePoint.infty : OnePoint F) =
    OnePoint.equivProjectivization F ((S 0 0 / S 1 0 : F) : OnePoint F)
  rw [← OnePoint.equivProjectivization_smul]
  simp [OnePoint.smul_infty_eq_ite, hS10]

private lemma dicksonWild_mk_smul_point {F : Type*} [Field F] [DecidableEq F]
    (S : GL (Fin 2) F) (z : F) :
    Matrix.ProjGenLinGroup.mk S • dicksonWildPoint z =
      if S 1 0 * z + S 1 1 = 0 then DicksonWildAffine.infinity F
      else dicksonWildPoint ((S 0 0 * z + S 0 1) / (S 1 0 * z + S 1 1)) := by
  change S • OnePoint.equivProjectivization F (z : OnePoint F) = _
  rw [← OnePoint.equivProjectivization_smul]
  rw [OnePoint.smul_some_eq_ite]
  split_ifs <;> rfl

private lemma dicksonWild_embedded_affine_smul_point {F : Type*} [Field F] [DecidableEq F]
    (M : Subfield F) (a : M) (u : Mˣ) (z : F) :
    Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk (DicksonWildAffine.affineGL a u)) •
      dicksonWildPoint z = dicksonWildPoint ((u.1.1 : F) * z + (a : F)) := by
  classical
  rw [Matrix.ProjGenLinGroup.map_mk,
    DicksonWildAffine.affineGL_map_subfield,
    dicksonWild_mk_smul_point]
  simp [DicksonWildAffine.affineGL]

private lemma dicksonWild_ratios_mem_of_preserves_subfield_line
    {F : Type*} [Field F] [DecidableEq F] (M : Subfield F) [Finite M]
    (S : GL (Fin 2) F) (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (hmap : ∀ z : OnePoint M, ∃ w : OnePoint M,
      S • OnePoint.map M.subtype z = OnePoint.map M.subtype w) :
    ∀ i k, (S : Matrix (Fin 2) (Fin 2) F) i k / S 1 0 ∈ M := by
  classical
  let _ := Fintype.ofFinite M
  let _ : Finite (OnePoint M) := Finite.of_fintype (OnePoint M)
  let embed : OnePoint M → OnePoint F := OnePoint.map M.subtype
  have hembed : Function.Injective embed := Option.map_injective M.subtype_injective
  let φ : OnePoint M → OnePoint M := fun z ↦ Classical.choose (hmap z)
  have hφ (z : OnePoint M) : S • embed z = embed (φ z) :=
    Classical.choose_spec (hmap z)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hembed
    apply (MulAction.toPerm S).injective
    change S • embed x = S • embed y
    rw [hφ, hφ, hxy]
  have hφsurj : Function.Surjective φ :=
    Finite.injective_iff_surjective.mp hφinj
  have ha : (S : Matrix (Fin 2) (Fin 2) F) 0 0 / S 1 0 ∈ M := by
    obtain ⟨w, hw⟩ := hmap (OnePoint.infty : OnePoint M)
    change S • (OnePoint.infty : OnePoint F) = embed w at hw
    have haction : S • (OnePoint.infty : OnePoint F) =
        ((S 0 0 / S 1 0 : F) : OnePoint F) :=
      OnePoint.smul_infty_eq_ite S |>.trans (ite_eq_right hS10)
    have hw' : ((S 0 0 / S 1 0 : F) : OnePoint F) = embed w :=
      haction.symm.trans hw
    cases w with
    | infty => simp [embed] at hw'
    | coe x =>
        have hx : (S : Matrix (Fin 2) (Fin 2) F) 0 0 / S 1 0 = (x : F) := by
          simpa [embed] using hw'
        rw [hx]
        exact x.2
  obtain ⟨z, hz⟩ := hφsurj (OnePoint.infty : OnePoint M)
  have hzAction : S • embed z = (OnePoint.infty : OnePoint F) := by
    rw [hφ, hz]
    rfl
  have hzFinite : ∃ x : M, z = (x : OnePoint M) := by
    cases z with
    | infty =>
        exfalso
        change S • (OnePoint.infty : OnePoint F) = OnePoint.infty at hzAction
        rw [OnePoint.smul_infty_eq_self_iff] at hzAction
        exact hS10 hzAction
    | coe x => exact ⟨x, rfl⟩
  obtain ⟨x, rfl⟩ := hzFinite
  have hden : (S : Matrix (Fin 2) (Fin 2) F) 1 0 * (x : F) + S 1 1 = 0 := by
    by_contra hne
    change S • ((x : F) : OnePoint F) = OnePoint.infty at hzAction
    simp [OnePoint.smul_some_eq_ite, hne] at hzAction
  have hdEq : (S : Matrix (Fin 2) (Fin 2) F) 1 1 / S 1 0 = -(x : F) := by
    apply (div_eq_iff hS10).2
    linear_combination hden
  have hd : (S : Matrix (Fin 2) (Fin 2) F) 1 1 / S 1 0 ∈ M := by
    rw [hdEq]
    exact M.neg_mem x.2
  have himage (z : M)
      (hden : (S : Matrix (Fin 2) (Fin 2) F) 1 0 * (z : F) + S 1 1 ≠ 0) :
      ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (z : F) + S 0 1) /
          (S 1 0 * (z : F) + S 1 1) ∈ M := by
    obtain ⟨w, hw⟩ := hmap (z : OnePoint M)
    change S • ((z : F) : OnePoint F) = embed w at hw
    have haction : S • ((z : F) : OnePoint F) =
        (((S 0 0 * (z : F) + S 0 1) / (S 1 0 * (z : F) + S 1 1) : F) :
          OnePoint F) :=
      OnePoint.smul_some_eq_ite.trans (ite_eq_right hden)
    have hw' : (((S 0 0 * (z : F) + S 0 1) /
        (S 1 0 * (z : F) + S 1 1) : F) : OnePoint F) = embed w :=
      haction.symm.trans hw
    cases w with
    | infty => exact (OnePoint.coe_ne_infty _ hw').elim
    | coe y =>
        have hy : ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (z : F) + S 0 1) /
            (S 1 0 * (z : F) + S 1 1) = (y : F) := by
          simpa [embed] using hw'
        rw [hy]
        exact y.2
  have hb : (S : Matrix (Fin 2) (Fin 2) F) 0 1 / S 1 0 ∈ M := by
    by_cases hS11 : (S : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
    · have honeDen : (S : Matrix (Fin 2) (Fin 2) F) 1 0 * (1 : F) + S 1 1 ≠ 0 := by
        simpa [hS11] using hS10
      have hone := himage (1 : M) honeDen
      change ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (1 : F) + S 0 1) /
          (S 1 0 * (1 : F) + S 1 1) ∈ M at hone
      have honeEq : ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (1 : F) + S 0 1) /
          (S 1 0 * (1 : F) + S 1 1) = S 0 0 / S 1 0 + S 0 1 / S 1 0 := by
        rw [hS11]
        field_simp [hS10]
        ring
      rw [honeEq] at hone
      convert M.sub_mem hone ha using 1
      ring
    · have hzero := himage (0 : M) (by simpa using hS11)
      have hbOverD : (S : Matrix (Fin 2) (Fin 2) F) 0 1 / S 1 1 ∈ M := by
        simpa using hzero
      have hfactor : (S : Matrix (Fin 2) (Fin 2) F) 0 1 / S 1 0 =
          (S 0 1 / S 1 1) * (S 1 1 / S 1 0) := by
        field_simp [hS10, hS11]
      rw [hfactor]
      exact M.mul_mem hbOverD hd
  intro i k
  fin_cases i <;> fin_cases k
  · exact ha
  · exact hb
  · simp [hS10]
  · exact hd

private lemma dicksonWild_upper_triangular_ratios_mem_of_preserves_subfield_line
    {F : Type*} [Field F] [DecidableEq F] (M : Subfield F)
    (S : GL (Fin 2) F) (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hmap : ∀ z : OnePoint M, ∃ w : OnePoint M,
      S • OnePoint.map M.subtype z = OnePoint.map M.subtype w) :
    ∀ i k, (S : Matrix (Fin 2) (Fin 2) F) i k / S 1 1 ∈ M := by
  classical
  let embed : OnePoint M → OnePoint F := OnePoint.map M.subtype
  have hS11 : (S : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro hzero
    apply S.det_ne_zero
    simp [Matrix.det_fin_two, hS10, hzero]
  have himage (z : M) :
      ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (z : F) + S 0 1) / S 1 1 ∈ M := by
    obtain ⟨w, hw⟩ := hmap (z : OnePoint M)
    change S • ((z : F) : OnePoint F) = embed w at hw
    have hden : (S : Matrix (Fin 2) (Fin 2) F) 1 0 * (z : F) + S 1 1 ≠ 0 := by
      simpa [hS10] using hS11
    have haction : S • ((z : F) : OnePoint F) =
        (((S 0 0 * (z : F) + S 0 1) / S 1 1 : F) : OnePoint F) := by
      rw [OnePoint.smul_some_eq_ite, ite_eq_right hden]
      congr 2
      rw [hS10, zero_mul, zero_add]
    have hw' : (((S 0 0 * (z : F) + S 0 1) / S 1 1 : F) : OnePoint F) =
        embed w := haction.symm.trans hw
    cases w with
    | infty => exact (OnePoint.coe_ne_infty _ hw').elim
    | coe y =>
        have hy : ((S : Matrix (Fin 2) (Fin 2) F) 0 0 * (z : F) + S 0 1) /
            S 1 1 = (y : F) := by
          simpa [embed] using hw'
        rw [hy]
        exact y.2
  have hb : (S : Matrix (Fin 2) (Fin 2) F) 0 1 / S 1 1 ∈ M := by
    simpa using himage (0 : M)
  have haPlus : ((S : Matrix (Fin 2) (Fin 2) F) 0 0 + S 0 1) / S 1 1 ∈ M := by
    simpa using himage (1 : M)
  have ha : (S : Matrix (Fin 2) (Fin 2) F) 0 0 / S 1 1 ∈ M := by
    have hsplit : ((S : Matrix (Fin 2) (Fin 2) F) 0 0 + S 0 1) / S 1 1 =
        S 0 0 / S 1 1 + S 0 1 / S 1 1 := by
      field_simp [hS11]
    rw [hsplit] at haPlus
    convert M.sub_mem haPlus hb using 1
    ring
  intro i k
  fin_cases i <;> fin_cases k
  · exact ha
  · exact hb
  · simp [hS10]
  · simp [hS11]

private lemma dicksonWild_exists_embedded_pgl_preimage_of_ratios_mem
    {F : Type*} [Field F] (M : Subfield F) (S : GL (Fin 2) F) (r : F)
    (hr : r ≠ 0) (hentries : ∀ i k,
      (S : Matrix (Fin 2) (Fin 2) F) i k / r ∈ M) :
    ∃ z : Matrix.ProjGenLinGroup (Fin 2) M,
      Matrix.ProjGenLinGroup.map M.subtype z = Matrix.ProjGenLinGroup.mk S := by
  let u : Fˣ := Units.mk0 r⁻¹ (inv_ne_zero hr)
  let T : GL (Fin 2) F := S * Matrix.GeneralLinearGroup.scalar (Fin 2) u
  have hTentry (i k : Fin 2) :
      (T : Matrix (Fin 2) (Fin 2) F) i k = S i k / r := by
    fin_cases k <;>
      simp [T, u, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  have hTentries : ∀ i k, (T : Matrix (Fin 2) (Fin 2) F) i k ∈ M := by
    intro i k
    rw [hTentry]
    exact hentries i k
  obtain ⟨z, hz⟩ := dicksonWild_exists_embedded_pgl_preimage_of_entries_mem M T hTentries
  refine ⟨z, hz.trans ?_⟩
  dsimp [T]
  rw [map_mul]
  simp

private lemma dicksonWild_exists_embedded_pgl_preimage_of_preserves_subfield_line
    {F : Type*} [Field F] [DecidableEq F] (M : Subfield F) [Finite M]
    (S : GL (Fin 2) F)
    (hmap : ∀ z : OnePoint M, ∃ w : OnePoint M,
      S • OnePoint.map M.subtype z = OnePoint.map M.subtype w) :
    ∃ z : Matrix.ProjGenLinGroup (Fin 2) M,
      Matrix.ProjGenLinGroup.map M.subtype z = Matrix.ProjGenLinGroup.mk S := by
  by_cases hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hS11 : (S : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro hzero
      apply S.det_ne_zero
      simp [Matrix.det_fin_two, hS10, hzero]
    exact dicksonWild_exists_embedded_pgl_preimage_of_ratios_mem M S (S 1 1) hS11
      (dicksonWild_upper_triangular_ratios_mem_of_preserves_subfield_line M S hS10 hmap)
  · exact dicksonWild_exists_embedded_pgl_preimage_of_ratios_mem M S (S 1 0) hS10
      (dicksonWild_ratios_mem_of_preserves_subfield_line M S hS10 hmap)

private lemma dicksonWild_pgl_toPermHom_injective
    {F : Type*} [Field F] :
    Function.Injective (MulAction.toPermHom
      (Matrix.ProjGenLinGroup (Fin 2) F)
      (Projectivization F (Fin 2 → F))) := by
  classical
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨S, hS⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hfix (x : Projectivization F (Fin 2 → F)) : g • x = x := by
    have h := congrArg (fun σ : Equiv.Perm (Projectivization F (Fin 2 → F)) ↦ σ x) hg
    simpa only [MulAction.toPermHom_apply, MulAction.toPerm_apply,
      Equiv.Perm.one_apply] using h
  have hfixOnePoint (z : OnePoint F) : S • z = z := by
    apply (OnePoint.equivProjectivization F).injective
    rw [OnePoint.equivProjectivization_smul]
    change Matrix.ProjGenLinGroup.mk S •
      OnePoint.equivProjectivization F z = OnePoint.equivProjectivization F z
    rw [hS]
    exact hfix _
  have hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (hfixOnePoint OnePoint.infty)
  have hS11 : (S : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro hzero
    apply S.det_ne_zero
    simp [Matrix.det_fin_two, hS10, hzero]
  have hS01 : (S : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have hzero := hfixOnePoint (0 : F)
    rw [OnePoint.smul_some_eq_ite] at hzero
    simp only [Fin.isValue, hS10, mul_zero, zero_add, hS11, ↓reduceIte,
      OnePoint.some_eq_iff, div_eq_zero_iff, or_false] at hzero
    exact hzero
  have hS00 : (S : Matrix (Fin 2) (Fin 2) F) 0 0 = S 1 1 := by
    have hone := hfixOnePoint (1 : F)
    rw [OnePoint.smul_some_eq_ite] at hone
    simp only [Fin.isValue, hS10, mul_one, zero_add, hS11, ↓reduceIte, hS01,
      add_zero, OnePoint.some_eq_iff] at hone
    exact (div_eq_one_iff_eq hS11).mp hone
  let u : Fˣ := Units.mk0 (S 1 1) hS11
  have hScalar : S = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    apply Units.ext
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      simp [Matrix.scalar_apply, u, hS00, hS01, hS10]
  rw [← hS, hScalar]
  simp

private lemma dicksonWild_mulEquiv_alternating_of_perm_index_two
    {H α : Type*} [Group H] [Fintype α] [DecidableEq α]
    (f : H →* Equiv.Perm α) (hf : Function.Injective f)
    (hindex : f.range.index = 2) : Nonempty (H ≃* alternatingGroup α) := by
  have hrange : f.range = alternatingGroup α :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  let eRange : H ≃* f.range := MonoidHom.ofInjective hf
  let eAlt : f.range ≃* alternatingGroup α :=
    MulEquiv.cast (M := fun Q : Subgroup (Equiv.Perm α) ↦ Q) hrange
  exact ⟨eRange.trans eAlt⟩

private lemma dicksonWild_perm_range_index_eq_two_of_card
    {H α : Type*} [Group H] [Finite H] [Finite α]
    (f : H →* Equiv.Perm α) (hf : Function.Injective f) (n : ℕ)
    (hHcard : Nat.card H = n) (hPermCard : Nat.card (Equiv.Perm α) = 2 * n) :
    f.range.index = 2 := by
  classical
  let _ : Finite f.range := Finite.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  have hRangeCard : Nat.card f.range = n := by
    rw [← hHcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  rw [Subgroup.index_eq_card_div, hRangeCard, hPermCard]
  rw [← hHcard]
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel_left 2 (Nat.card_pos (α := H))

private lemma dicksonWild_psl_card_three_equiv_alternating_four
    (p : ℕ) (M : Type*) [Field M] [Finite M] [CharP M p]
    (hp2 : p ≠ 2) (hMcard : Nat.card M = 3) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) M ≃*
      alternatingGroup (Fin 4)) := by
  classical
  let _ : Fintype M := Fintype.ofFinite M
  let X := Projectivization M (Fin 2 → M)
  let _ : Fintype X := Fintype.ofEquiv (OnePoint M)
    (OnePoint.equivProjectivization M)
  have hOneCard : Fintype.card (OnePoint M) = 4 := by
    change Fintype.card (Option M) = 4
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, hMcard]
  have hXcard : Fintype.card X = 4 := by
    calc
      Fintype.card X = Fintype.card (OnePoint M) :=
        (Fintype.card_congr (OnePoint.equivProjectivization M)).symm
      _ = 4 := hOneCard
  let eFin : X ≃ Fin 4 := (Fintype.equivFin X).trans (finCongr hXcard)
  let act : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →*
      Equiv.Perm (Fin 4) := eFin.permCongrHom.toMonoidHom.comp
        (Projectivization.PSLAction.toPermHom (K := M) (ι := Fin 2))
  have hact : Function.Injective act := eFin.permCongrHom.injective.comp
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  have hPSLcard : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) M) = 12 := by
    rw [card_projectiveSpecialLinearGroup_fin_two p M hp2,
      ← Nat.card_eq_fintype_card, hMcard]
    norm_num
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hactIndex : act.range.index = 2 :=
    dicksonWild_perm_range_index_eq_two_of_card act hact 12 hPSLcard (by omega)
  exact dicksonWild_mulEquiv_alternating_of_perm_index_two act hact hactIndex

private lemma dicksonWild_stabilizer_infinity_eq_normalizer
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G)
    (M : Subfield (K p)) (L : Subgroup Mˣ) (j : G →* PGL p)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    @MulAction.stabilizer G (Projectivization (K p) (Fin 2 → K p)) _
      (MulAction.compHom _ j) (DicksonWildAffine.infinity (K p)) =
        Subgroup.normalizer (P : Set G) := by
  classical
  let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
    MulAction.compHom _ j
  apply le_antisymm
  · intro g hg
    by_contra hgN
    obtain ⟨S, hS, hS10⟩ := hout g hgN
    have hfix : j g • DicksonWildAffine.infinity (K p) =
        DicksonWildAffine.infinity (K p) := MulAction.mem_stabilizer_iff.mp hg
    rw [← hS] at hfix
    have hfix' : S • (OnePoint.infty : OnePoint (K p)) = OnePoint.infty := by
      apply (OnePoint.equivProjectivization (K p)).injective
      rw [OnePoint.equivProjectivization_smul]
      simpa [DicksonWildAffine.infinity] using hfix
    exact hS10 (OnePoint.smul_infty_eq_self_iff.mp hfix')
  · intro n hn
    apply MulAction.mem_stabilizer_iff.mpr
    let nN : Subgroup.normalizer (P : Set G) := ⟨n, hn⟩
    let A : GL (Fin 2) (K p) := Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord nN).1 (coord nN).2.1)
    have hA10 : (A : Matrix (Fin 2) (Fin 2) (K p)) 1 0 = 0 := by
      simp [A, DicksonWildAffine.affineGL]
    have hAfix : A • (OnePoint.infty : OnePoint (K p)) = OnePoint.infty :=
      OnePoint.smul_infty_eq_self_iff.mpr hA10
    change j n • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p)
    rw [hnormal nN, Matrix.ProjGenLinGroup.map_mk]
    change Matrix.ProjGenLinGroup.mk A • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p)
    change Matrix.ProjGenLinGroup.mk A •
      OnePoint.equivProjectivization (K p) OnePoint.infty =
        OnePoint.equivProjectivization (K p) OnePoint.infty
    change A • OnePoint.equivProjectivization (K p) OnePoint.infty =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    rw [← OnePoint.equivProjectivization_smul]
    exact congrArg (OnePoint.equivProjectivization (K p)) hAfix

set_option maxHeartbeats 800000 in
-- A full projective-line orbit supplies the field of definition after one translation.
private lemma dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G) (m : ℕ)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (j : G →* PGL p)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    ∃ κ : PGL p, ((MulAut.conj κ).toMonoidHom.comp j).range ≤
      (Matrix.ProjGenLinGroup.map M.subtype).range := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let X := Projectivization (K p) (Fin 2 → K p)
  let xInf : X := DicksonWildAffine.infinity (K p)
  let _ : MulAction G X := MulAction.compHom X j
  have hstab : MulAction.stabilizer G xInf = N :=
    dicksonWild_stabilizer_infinity_eq_normalizer G P M L j coord hnormal hout
  have hindexN : N.index = 1 + p ^ m := by simpa [N] using hindex
  have hNne : N ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hindexN
    have hpow : 0 < p ^ m := pow_pos (Fact.out : p.Prime).pos m
    omega
  obtain ⟨g₀, hg₀⟩ : ∃ g : G, g ∉ N := by
    by_contra hall
    push Not at hall
    apply hNne
    exact top_unique fun g _ ↦ hall g
  obtain ⟨S₀, hS₀, hS₀10⟩ := hout g₀ hg₀
  let y : K p := (S₀ : Matrix (Fin 2) (Fin 2) (K p)) 0 0 / S₀ 1 0
  have hg₀x : j g₀ • xInf = dicksonWildPoint y := by
    rw [← hS₀]
    exact dicksonWild_mk_smul_infinity S₀ hS₀10
  let shifted : OnePoint M → X := OnePoint.rec xInf fun a ↦
    dicksonWildPoint (y + (a : K p))
  have hshiftOrbit (z : OnePoint M) : shifted z ∈ MulAction.orbit G xInf := by
    cases z with
    | infty => exact MulAction.mem_orbit_self xInf
    | coe a =>
        obtain ⟨n, hn⟩ := hcoord.2 (a, 1)
        apply MulAction.mem_orbit_iff.mpr
        refine ⟨n.1 * g₀, ?_⟩
        change j (n.1 * g₀) • xInf = dicksonWildPoint (y + (a : K p))
        rw [map_mul, mul_smul, hg₀x, hnormal n, hn]
        simpa using
          (dicksonWild_embedded_affine_smul_point M a (1 : Mˣ) y)
  have hshiftInj : Function.Injective shifted := by
    intro z w hzw
    cases z with
    | infty =>
        cases w with
        | infty => rfl
        | coe b =>
            exfalso
            change xInf = dicksonWildPoint (y + (b : K p)) at hzw
            have h := congrArg (OnePoint.equivProjectivization (K p)).symm hzw
            simp [xInf, DicksonWildAffine.infinity, dicksonWildPoint] at h
    | coe a =>
        cases w with
        | infty =>
            exfalso
            change dicksonWildPoint (y + (a : K p)) = xInf at hzw
            have h := congrArg (OnePoint.equivProjectivization (K p)).symm hzw
            simp [xInf, DicksonWildAffine.infinity, dicksonWildPoint] at h
        | coe b =>
            change dicksonWildPoint (y + (a : K p)) =
              dicksonWildPoint (y + (b : K p)) at hzw
            have h := congrArg (OnePoint.equivProjectivization (K p)).symm hzw
            have hab : a = b := by
              apply Subtype.ext
              have h' : y + (a : K p) = y + (b : K p) := by
                simpa only [dicksonWildPoint, Equiv.symm_apply_apply,
                  OnePoint.some_eq_iff] using h
              exact add_left_cancel h'
            cases hab
            rfl
  let O := MulAction.orbit G xInf
  let orbitMap : G → O := fun g ↦
    ⟨g • xInf, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩
  have horbitMap : Function.Surjective orbitMap := by
    intro z
    obtain ⟨g, hg⟩ := z.2
    exact ⟨g, Subtype.ext hg⟩
  let _ : Finite O := Finite.of_surjective orbitMap horbitMap
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite M
  have hOcard : Nat.card O = 1 + p ^ m := by
    calc
      Nat.card O = (MulAction.orbit G xInf).ncard := Nat.card_coe_set_eq _
      _ = (MulAction.stabilizer G xInf).index :=
        (MulAction.index_stabilizer G xInf).symm
      _ = N.index := by rw [hstab]
      _ = 1 + p ^ m := hindexN
  let toOrbit : OnePoint M → O := fun z ↦ ⟨shifted z, hshiftOrbit z⟩
  have htoInjective : Function.Injective toOrbit := by
    intro z w hzw
    exact hshiftInj (congrArg Subtype.val hzw)
  have hMfcard : Fintype.card M = p ^ m := by
    simpa only [Nat.card_eq_fintype_card] using hMcard
  have htoSurjective : Function.Surjective toOrbit := by
    have hbij : Function.Bijective toOrbit :=
      (Fintype.bijective_iff_injective_and_card toOrbit).2 ⟨htoInjective, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hOcard]
        rw [Nat.card_eq_fintype_card]
        change Fintype.card (Option M) = 1 + p ^ m
        rw [Fintype.card_option, hMfcard, Nat.add_comm]⟩
    exact hbij.2
  let T : GL (Fin 2) (K p) := DicksonWildAffine.affineGL (-y) 1
  let κ : PGL p := Matrix.ProjGenLinGroup.mk T
  let embedded : OnePoint M → X := fun z ↦
    OnePoint.equivProjectivization (K p) (OnePoint.map M.subtype z)
  have hTshift (z : OnePoint M) : κ • shifted z = embedded z := by
    cases z with
    | infty =>
        change T • OnePoint.equivProjectivization (K p) OnePoint.infty =
          OnePoint.equivProjectivization (K p) OnePoint.infty
        rw [← OnePoint.equivProjectivization_smul]
        congr 1
        simp [T, DicksonWildAffine.affineGL, OnePoint.smul_infty_eq_ite]
    | coe a =>
        change Matrix.ProjGenLinGroup.mk T •
            dicksonWildPoint (y + (a : K p)) = dicksonWildPoint (a : K p)
        rw [dicksonWild_mk_smul_point]
        simp [T, DicksonWildAffine.affineGL]
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hpreserve (g : G) (z : OnePoint M) :
      ∃ w : OnePoint M, j' g • embedded z = embedded w := by
    have hmem : g • shifted z ∈ MulAction.orbit G xInf := by
      obtain ⟨a, ha⟩ := hshiftOrbit z
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g * a, ?_⟩
      rw [mul_smul]
      exact congrArg (fun u : X ↦ g • u) ha
    obtain ⟨w, hw⟩ := htoSurjective ⟨g • shifted z, hmem⟩
    have hwval : shifted w = g • shifted z := congrArg Subtype.val hw
    change shifted w = j g • shifted z at hwval
    refine ⟨w, ?_⟩
    have hback : κ⁻¹ • embedded z = shifted z := by
      rw [← hTshift z]
      simp [← mul_smul]
    calc
      j' g • embedded z = (κ * j g * κ⁻¹) • embedded z := by
        rw [show j' g = κ * j g * κ⁻¹ by simp [j', MulAut.conj_apply]]
      _ = κ • (j g • (κ⁻¹ • embedded z)) := by
        rw [mul_smul, mul_smul]
      _ = κ • (j g • shifted z) := by rw [hback]
      _ = κ • shifted w := by rw [hwval]
      _ = embedded w := hTshift w
  refine ⟨κ, ?_⟩
  rintro _ ⟨g, rfl⟩
  obtain ⟨S, hS⟩ := Matrix.ProjGenLinGroup.mk_surjective (j' g)
  have hmap (z : OnePoint M) : ∃ w : OnePoint M,
      S • OnePoint.map M.subtype z = OnePoint.map M.subtype w := by
    obtain ⟨w, hw⟩ := hpreserve g z
    refine ⟨w, ?_⟩
    apply (OnePoint.equivProjectivization (K p)).injective
    rw [OnePoint.equivProjectivization_smul]
    change Matrix.ProjGenLinGroup.mk S • embedded z = embedded w
    rw [hS]
    exact hw
  obtain ⟨s, hs⟩ :=
    dicksonWild_exists_embedded_pgl_preimage_of_preserves_subfield_line M S hmap
  exact ⟨s, hs.trans hS⟩

private lemma dicksonWild_card_fixedBy_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (j : G →* PGL p)
    (hj : Function.Injective j) (g : G) (hg : g ≠ 1) :
    (g ^ p = 1 ∧ Nat.card (@MulAction.fixedBy G
      (Projectivization (K p) (Fin 2 → K p)) _ (MulAction.compHom _ j) g) = 1) ∨
    (g ^ p ≠ 1 ∧ Nat.card (@MulAction.fixedBy G
      (Projectivization (K p) (Fin 2 → K p)) _ (MulAction.compHom _ j) g) = 2) := by
  classical
  by_cases hgp : g ^ p = 1
  · left
    refine ⟨hgp, ?_⟩
    have horderG : orderOf g = p := orderOf_eq_prime hgp hg
    have horderJ : orderOf (j g) = p :=
      (orderOf_injective j hj g).trans horderG
    obtain ⟨x, hx, hxUnique⟩ :=
      dicksonWild_existsUnique_fixedPoint_of_orderOf_eq_char (j g) horderJ
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      intro a b
      apply Subtype.ext
      exact (hxUnique a.1 a.2).trans (hxUnique b.1 b.2).symm
    · exact ⟨⟨x, hx⟩⟩
  · right
    refine ⟨hgp, ?_⟩
    change Nat.card (MulAction.fixedBy
      (Projectivization (K p) (Fin 2 → K p)) (j g)) = 2
    apply dicksonWild_card_fixedBy_of_not_dvd_order (j g) (by
      intro h
      apply hg
      apply hj
      simpa using h)
    intro hporder
    have hfinite : orderOf (j g) ≠ 0 := by
      rw [orderOf_injective j hj]
      exact (orderOf_pos g).ne'
    have horderJ := orderOf_eq_char_of_char_dvd (j g) hfinite hporder
    have horderG : orderOf g = p := by
      rw [orderOf_injective j hj] at horderJ
      exact horderJ
    apply hgp
    exact (congrArg (fun n : ℕ => g ^ n) horderG).symm.trans
      (pow_orderOf_eq_one g)

private lemma dicksonWild_exceptional_burnside_count
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (j : G →* PGL p)
    (hj : Function.Injective j) (R : ℕ)
    (hR : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} = R) :
    let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
      MulAction.compHom _ j
    let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
    Nat.card E + R + 2 * (Nat.card G - 1 - R) =
      Nat.card (MulAction.orbitRel.Quotient G E) * Nat.card G := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let _ : MulAction G X := MulAction.compHom _ j
  let E := dicksonWildExceptional G X
  have hfixed (g : G) (hg : g ≠ 1) :
      (g ^ p = 1 ∧ Nat.card (MulAction.fixedBy X g) = 1) ∨
      (g ^ p ≠ 1 ∧ Nat.card (MulAction.fixedBy X g) = 2) :=
    dicksonWild_card_fixedBy_normal_form G j hj g hg
  let _ : Finite E := dicksonWildExceptional_finite fun g hg => by
    rcases hfixed g hg with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hfixedE (g : G) (hg : g ≠ 1) :
      (g ^ p = 1 ∧ Nat.card (MulAction.fixedBy E g) = 1) ∨
      (g ^ p ≠ 1 ∧ Nat.card (MulAction.fixedBy E g) = 2) := by
    have hc : Nat.card (MulAction.fixedBy E g) =
        Nat.card (MulAction.fixedBy X g) :=
      Nat.card_congr (dicksonWild_fixedByExceptionalEquiv g hg)
    rcases hfixed g hg with h | h
    · exact Or.inl ⟨h.1, hc.trans h.2⟩
    · exact Or.inr ⟨h.1, hc.trans h.2⟩
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite E
  let _ (g : G) := Fintype.ofFinite (MulAction.fixedBy E g)
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient G E)
  let S : Finset G := (Finset.univ : Finset G).erase 1
  let Q : Finset G := S.filter fun g => g ^ p = 1
  have hQcard : Q.card = R := by
    let eQ : {g : G // g ≠ 1 ∧ g ^ p = 1} ≃ {g : G // g ∈ Q} := {
      toFun g := ⟨g.1, by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_erase.mpr ⟨g.2.1, Finset.mem_univ _⟩, g.2.2⟩⟩
      invFun g := ⟨g.1, by
        have hg := Finset.mem_filter.mp g.2
        exact ⟨Finset.ne_of_mem_erase hg.1, hg.2⟩⟩
      left_inv g := by ext; rfl
      right_inv g := by ext; rfl }
    rw [← hR, Nat.card_congr eQ]
    simp
  let T : Finset G := S.filter fun g => g ^ p ≠ 1
  have hScard : S.card = Fintype.card G - 1 := by simp [S]
  have hparts : Q.card + T.card = S.card := by
    simpa [Q, T] using
      (Finset.sum_filter_add_sum_filter_not S (fun g : G => g ^ p = 1)
        (fun _g => (1 : ℕ)))
  have hTcard : T.card = Fintype.card G - 1 - R := by omega
  have hsumQ : (∑ g ∈ Q, Fintype.card (MulAction.fixedBy E g)) = R := by
    calc
      (∑ g ∈ Q, Fintype.card (MulAction.fixedBy E g)) = ∑ _g ∈ Q, 1 := by
        apply Finset.sum_congr rfl
        intro g hg
        have hgdata := Finset.mem_filter.mp hg
        have hg1 : g ≠ 1 := Finset.ne_of_mem_erase hgdata.1
        have hgp : g ^ p = 1 := hgdata.2
        rcases hfixedE g hg1 with h | h
        · simpa only [Nat.card_eq_fintype_card] using h.2
        · exact (h.1 hgp).elim
      _ = R := by simp [hQcard]
  have hsumT : (∑ g ∈ T, Fintype.card (MulAction.fixedBy E g)) =
      2 * (Fintype.card G - 1 - R) := by
    calc
      (∑ g ∈ T, Fintype.card (MulAction.fixedBy E g)) = ∑ _g ∈ T, 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        have hgdata := Finset.mem_filter.mp hg
        have hg1 : g ≠ 1 := Finset.ne_of_mem_erase hgdata.1
        have hgp : g ^ p ≠ 1 := hgdata.2
        rcases hfixedE g hg1 with h | h
        · exact (hgp h.1).elim
        · simpa only [Nat.card_eq_fintype_card] using h.2
      _ = 2 * (Fintype.card G - 1 - R) := by simp [hTcard, Nat.mul_comm]
  have hsumS : (∑ g ∈ S, Fintype.card (MulAction.fixedBy E g)) =
      R + 2 * (Fintype.card G - 1 - R) := by
    calc
      (∑ g ∈ S, Fintype.card (MulAction.fixedBy E g)) =
          (∑ g ∈ Q, Fintype.card (MulAction.fixedBy E g)) +
            ∑ g ∈ T, Fintype.card (MulAction.fixedBy E g) := by
        simpa [Q, T] using
          (Finset.sum_filter_add_sum_filter_not S (fun g : G => g ^ p = 1)
            (fun g => Fintype.card (MulAction.fixedBy E g))).symm
      _ = R + 2 * (Fintype.card G - 1 - R) := by rw [hsumQ, hsumT]
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G E
  rw [show (∑ g : G, Fintype.card (MulAction.fixedBy E g)) =
      (∑ g ∈ S, Fintype.card (MulAction.fixedBy E g)) +
        Fintype.card (MulAction.fixedBy E (1 : G)) by
      simpa [S] using (Finset.sum_erase_add (Finset.univ : Finset G)
        (fun g : G => Fintype.card (MulAction.fixedBy E g))
        (Finset.mem_univ 1)).symm] at hburn
  rw [hsumS] at hburn
  have hOne : Fintype.card (MulAction.fixedBy E (1 : G)) = Fintype.card E := by
    exact Fintype.card_congr
      ((Set.equivOfEq (MulAction.fixedBy_one_eq_univ E G)).trans
        (Equiv.Set.univ E))
  rw [hOne] at hburn
  change Nat.card E + R + 2 * (Nat.card G - 1 - R) =
    Nat.card (MulAction.orbitRel.Quotient G E) * Nat.card G
  simpa only [Nat.card_eq_fintype_card, add_assoc, add_comm, add_left_comm] using hburn

set_option maxHeartbeats 800000 in
-- The orbit count expands two finite quotient sums and their stabilizers.
private lemma dicksonWild_exceptional_orbit_data
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G)
    (m f t : ℕ) (hm : 1 ≤ m) (hf : 0 < f)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (M : Subfield (K p)) (L : Subgroup Mˣ) (j : G →* PGL p)
    (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    ∃ d : ℕ, 2 ≤ d ∧
      d * (1 + f * (p ^ m - 2)) = t * (1 + f * p ^ m) ∧
      (let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
          MulAction.compHom _ j
        let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
        (∃ x : E, Nat.card (MulAction.stabilizer G x) = p ^ m * t) ∧
        (∃ x : E, Nat.card (MulAction.stabilizer G x) = d) ∧
        (∀ x : E, Nat.card (MulAction.stabilizer G x) = p ^ m * t ∨
          Nat.card (MulAction.stabilizer G x) = d) ∧
        Nat.card (MulAction.orbitRel.Quotient G E) = 2) := by
  classical
  let q := p ^ m
  let s := 1 + f * q
  let N := Subgroup.normalizer (P : Set G)
  let X := Projectivization (K p) (Fin 2 → K p)
  let _ : MulAction G X := MulAction.compHom _ j
  let E := dicksonWildExceptional G X
  let Ω := MulAction.orbitRel.Quotient G E
  have hq3 : 3 ≤ q := by
    have hpgt : 2 < p := Fact.out
    have hp3 : 3 ≤ p := by omega
    exact hp3.trans (Nat.le_pow hm)
  have hs4 : 4 ≤ s := by
    dsimp [s]
    nlinarith
  have ht : 0 < t := by
    by_contra ht0
    have : t = 0 := Nat.eq_zero_of_not_pos ht0
    rw [this, mul_zero] at hNcard
    exact Nat.card_pos.ne' hNcard
  have hNgt : 1 < Nat.card N := by
    rw [hNcard]
    dsimp [q] at hq3
    nlinarith
  let _ : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp hNgt
  have hstabX : MulAction.stabilizer G (DicksonWildAffine.infinity (K p)) = N :=
    dicksonWild_stabilizer_infinity_eq_normalizer G P M L j coord hnormal hout
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  have hnG : (n.1 : G) ≠ 1 := fun h => hn (Subtype.ext h)
  have hnfix : (n.1 : G) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p) := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hstabX]
    exact n.2
  let x : E := ⟨DicksonWildAffine.infinity (K p), ⟨n.1, hnG, hnfix⟩⟩
  have hstabx : MulAction.stabilizer G x = N := by
    ext g
    constructor
    · intro hg
      have hval : g • DicksonWildAffine.infinity (K p) =
          DicksonWildAffine.infinity (K p) :=
        congrArg (fun z : E => z.1) (MulAction.mem_stabilizer_iff.mp hg)
      have : g ∈ MulAction.stabilizer G (DicksonWildAffine.infinity (K p)) :=
        MulAction.mem_stabilizer_iff.mpr hval
      rwa [hstabX] at this
    · intro hg
      apply MulAction.mem_stabilizer_iff.mpr
      apply Subtype.ext
      have : g ∈ MulAction.stabilizer G (DicksonWildAffine.infinity (K p)) := by
        rw [hstabX]
        exact hg
      exact MulAction.mem_stabilizer_iff.mp this
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite N
  let orbitMap : G → MulAction.orbit G x := fun g =>
    ⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩
  have horbitMap : Function.Surjective orbitMap := by
    intro y
    obtain ⟨g, hg⟩ := y.2
    exact ⟨g, Subtype.ext hg⟩
  let _ : Finite (MulAction.orbit G x) := Finite.of_surjective orbitMap horbitMap
  let _ := Fintype.ofFinite (MulAction.orbit G x)
  have hOrbitProd : Nat.card (MulAction.orbit G x) * Nat.card N = Nat.card G := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
    simpa only [Nat.card_eq_fintype_card, hstabx] using h
  have hNProd : Nat.card N * s = Nat.card G := by
    have h := N.card_mul_index
    rw [hindex] at h
    exact h
  have hOrbitCard : Nat.card (MulAction.orbit G x) = s := by
    nlinarith [Nat.card_pos (α := N)]
  have hGcard : Nat.card G = q * t * s := by
    rw [← hNProd, hNcard]
  have hR : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} = s * (q - 1) := by
    simpa [q, s] using hcount
  have hRle : s * (q - 1) ≤ Nat.card G - 1 := by
    rw [hGcard]
    have hqeq : q = (q - 1) + 1 := by omega
    have hqs : q * s = (q - 1) * s + s := by
      calc
        q * s = ((q - 1) + 1) * s :=
          congrArg (fun z : ℕ ↦ z * s) hqeq
        _ = (q - 1) * s + s := by ring
    have hbase : s * (q - 1) + 1 ≤ q * s := by
      calc
        s * (q - 1) + 1 ≤ s * (q - 1) + s := by omega
        _ = q * s := by
          rw [hqs]
          ac_rfl
    have hsMul : s ≤ t * s := by
      simpa using Nat.mul_le_mul_right s (show 1 ≤ t by omega)
    have hscale : q * s ≤ q * t * s := by
      calc
        q * s ≤ q * (t * s) := Nat.mul_le_mul_left q hsMul
        _ = q * t * s := by ring
    have htotal := hbase.trans hscale
    omega
  have hRsucc : 1 + s * (q - 1) ≤ Nat.card G := by
    simpa [Nat.add_comm] using Nat.add_le_of_le_sub
      (show 1 ≤ Nat.card G from Nat.card_pos) hRle
  have hsubEq : Nat.card G - 1 - s * (q - 1) =
      Nat.card G - (1 + s * (q - 1)) := by
    rw [Nat.sub_sub]
  have hdecompG : Nat.card G = 1 + s * (q - 1) +
      (Nat.card G - 1 - s * (q - 1)) := by
    calc
      Nat.card G = (1 + s * (q - 1)) +
          (Nat.card G - (1 + s * (q - 1))) :=
        (Nat.add_sub_of_le hRsucc).symm
      _ = 1 + s * (q - 1) + (Nat.card G - 1 - s * (q - 1)) := by
        rw [hsubEq]
  have hfixed (g : G) (hg : g ≠ 1) :
      (g ^ p = 1 ∧ Nat.card (MulAction.fixedBy X g) = 1) ∨
      (g ^ p ≠ 1 ∧ Nat.card (MulAction.fixedBy X g) = 2) :=
    dicksonWild_card_fixedBy_normal_form G j hj g hg
  let _ : Finite E := dicksonWildExceptional_finite fun g hg => by
    rcases hfixed g hg with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite Ω
  let _ (y : E) := Fintype.ofFinite (MulAction.stabilizer G y)
  have hburn : Nat.card E + s * (q - 1) +
      2 * (Nat.card G - 1 - s * (q - 1)) = Nat.card Ω * Nat.card G :=
    dicksonWild_exceptional_burnside_count G j hj (s * (q - 1)) hR
  have hnontrivial (y : E) : Nontrivial (MulAction.stabilizer G y) := by
    obtain ⟨g, hg, hgy⟩ := y.2
    exact ⟨⟨⟨1, by simp⟩, ⟨g, Subtype.ext hgy⟩, by
      intro h
      apply hg
      exact (congrArg Subtype.val h).symm⟩⟩
  have hclass : Nat.card E =
      ∑ ω : Ω, Nat.card G / Nat.card (MulAction.stabilizer G ω.out) := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_eq_sum_card_group_div_card_stabilizer G E
  let ω0 : Ω := Quotient.mk'' x
  let term : Ω → ℕ := fun ω =>
    Nat.card G / Nat.card (MulAction.stabilizer G ω.out)
  have hstabω0 : Nat.card (MulAction.stabilizer G ω0.out) = Nat.card N := by
    calc
      Nat.card (MulAction.stabilizer G ω0.out) =
          Nat.card (MulAction.stabilizer G x) :=
        dicksonWild_card_stabilizer_eq_of_quotient_eq ω0.out x <| by
          simp [ω0]
      _ = Nat.card N := by rw [hstabx]
  have hterm0 : term ω0 = s := by
    dsimp [term]
    rw [hstabω0, ← Subgroup.index_eq_card_div, hindex]
  have htermLe (ω : Ω) : 2 * term ω ≤ Nat.card G := by
    have he : 2 ≤ Nat.card (MulAction.stabilizer G ω.out) := by
      exact Finite.one_lt_card_iff_nontrivial.mpr (hnontrivial ω.out)
    have hdvd : Nat.card (MulAction.stabilizer G ω.out) ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card (MulAction.stabilizer G ω.out)
    calc
      2 * term ω ≤ Nat.card (MulAction.stabilizer G ω.out) * term ω :=
        Nat.mul_le_mul_right _ he
      _ = Nat.card G := by
        dsimp [term]
        rw [mul_comm, Nat.div_mul_cancel hdvd]
  let rest := ∑ ω ∈ ({ω0}ᶜ : Finset Ω), term ω
  have hsplit : Nat.card E = s + rest := by
    rw [hclass]
    change (∑ ω : Ω, term ω) = _
    rw [Fintype.sum_eq_add_sum_compl ω0 term, hterm0]
  have hrestLe : 2 * rest ≤ (Nat.card Ω - 1) * Nat.card G := by
    have hcompcard : ({ω0}ᶜ : Finset Ω).card = Fintype.card Ω - 1 := by
      rw [Finset.card_compl, Finset.card_singleton]
    calc
      2 * rest = ∑ ω ∈ ({ω0}ᶜ : Finset Ω), 2 * term ω := by
        simp [rest, Finset.mul_sum]
      _ ≤ ∑ _ω ∈ ({ω0}ᶜ : Finset Ω), Nat.card G := by
        exact Finset.sum_le_sum fun ω _ => htermLe ω
      _ = (Nat.card Ω - 1) * Nat.card G := by
        simp [hcompcard, Nat.card_eq_fintype_card]
  let _ : Nonempty Ω := ⟨ω0⟩
  have hΩpos : 0 < Nat.card Ω := Nat.card_pos
  have hΩtwo : Nat.card Ω = 2 := by
    have htwo : 2 ≤ q - 1 := by omega
    have hRge : 2 * s ≤ s * (q - 1) := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left s htwo
    rw [hsplit] at hburn
    have hΩone : ¬Nat.card Ω ≤ 1 := by
      intro hle
      have heq : Nat.card Ω = 1 := by omega
      rw [heq] at hburn hrestLe
      norm_num at hrestLe
      omega
    have hΩlt3 : Nat.card Ω < 3 := by
      by_contra hnot
      have hge : 3 ≤ Nat.card Ω := by omega
      have hsub : Nat.card Ω = (Nat.card Ω - 1) + 1 := by omega
      have hlarge : 2 * Nat.card G ≤ (Nat.card Ω - 1) * Nat.card G := by
        exact Nat.mul_le_mul_right (Nat.card G) (by omega)
      have hmul : Nat.card Ω * Nat.card G =
          (Nat.card Ω - 1) * Nat.card G + Nat.card G := by
        calc
          Nat.card Ω * Nat.card G = ((Nat.card Ω - 1) + 1) * Nat.card G :=
            congrArg (fun z : ℕ => z * Nat.card G) hsub
          _ = (Nat.card Ω - 1) * Nat.card G + Nat.card G := by
            rw [add_mul, one_mul]
      omega
    omega
  obtain ⟨ω1, hω1, hω1Unique⟩ := (Nat.card_eq_two_iff' ω0).mp hΩtwo
  let d := Nat.card (MulAction.stabilizer G ω1.out)
  have hd2 : 2 ≤ d := by
    exact Finite.one_lt_card_iff_nontrivial.mpr (hnontrivial ω1.out)
  have hrestEq : rest = term ω1 := by
    apply Finset.sum_eq_single ω1
    · intro z hz hz1
      exfalso
      apply hz1
      exact hω1Unique z (by simpa using hz)
    · simp [hω1]
  have hEcard : Nat.card E = s + term ω1 := by rw [hsplit, hrestEq]
  have hterm1 : term ω1 = q * (1 + f * (q - 2)) := by
    rw [hΩtwo, hEcard] at hburn
    have hraw : term ω1 + s = 2 + s * (q - 1) := by omega
    have hid : q * (1 + f * (q - 2)) + s = 2 + s * (q - 1) := by
      have hqeq : q = (q - 2) + 2 := by omega
      dsimp [s]
      conv_lhs => rw [hqeq]
      conv_rhs => rw [hqeq]
      simp
      ring
    omega
  have htermMul : term ω1 * d = Nat.card G := by
    dsimp [term, d]
    exact Nat.div_mul_cancel
      (Subgroup.card_subgroup_dvd_card (MulAction.stabilizer G ω1.out))
  have hrelation : d * (1 + f * (q - 2)) = t * s := by
    rw [hterm1, hGcard] at htermMul
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos m)
    simpa [q, mul_assoc, mul_left_comm, mul_comm] using htermMul
  refine ⟨d, hd2, ?_, ⟨x, ?_⟩, ⟨ω1.out, rfl⟩, ?_, hΩtwo⟩
  · simpa [q, s] using hrelation
  · rw [hstabx, hNcard]
  · change ∀ y : E, Nat.card (MulAction.stabilizer G y) = p ^ m * t ∨
      Nat.card (MulAction.stabilizer G y) = d
    intro y
    by_cases hy : (Quotient.mk'' y : Ω) = ω0
    · left
      calc
        Nat.card (MulAction.stabilizer G y) =
            Nat.card (MulAction.stabilizer G ω0.out) :=
          dicksonWild_card_stabilizer_eq_of_quotient_eq y ω0.out <| by
            simpa using hy.trans (Quotient.out_eq' ω0).symm
        _ = Nat.card N := hstabω0
        _ = p ^ m * t := hNcard
    · right
      have hy1 : (Quotient.mk'' y : Ω) = ω1 := hω1Unique _ hy
      exact dicksonWild_card_stabilizer_eq_of_quotient_eq y ω1.out <| by
        simpa using hy1.trans (Quotient.out_eq' ω1).symm

private lemma dicksonWild_f_eq_one_of_half_multiplier_relation
    (q f t d : ℕ) (hq : 3 ≤ q) (hf : 0 < f)
    (hhalf : 2 * t = q - 1)
    (hrelation : d * (1 + f * (q - 2)) = t * (1 + f * q)) : f = 1 := by
  have hqeq : q = 2 * t + 1 := by omega
  have ht : 1 ≤ t := by omega
  have htEq : t = (t - 1) + 1 := by omega
  have hqpoly : q = 2 * (t - 1) + 3 := by omega
  have hsub : q - 2 = 2 * (t - 1) + 1 := by omega
  let A := 1 + f * (q - 2)
  have hApos : 0 < A := by simp [A]
  have hfEq : f = (f - 1) + 1 := by omega
  have hid : t * (1 + f * q) = (t + 1) * A + (f - 1) := by
    dsimp [A]
    rw [htEq, hsub, hqpoly, hfEq]
    ring_nf
    omega
  by_contra hne
  have hf2 : 2 ≤ f := by omega
  have hprod : d * A = (t + 1) * A + (f - 1) := by
    rw [hrelation, hid]
  have hgt : (t + 1) * A < d * A := by omega
  have hdt : t + 1 < d := (Nat.mul_lt_mul_right hApos).mp hgt
  have hlower : (t + 2) * A ≤ d * A :=
    Nat.mul_le_mul_right A (by omega)
  have hAle : A ≤ f - 1 := by
    rw [hprod] at hlower
    have hmul : (t + 2) * A = (t + 1) * A + A := by ring
    rw [hmul] at hlower
    omega
  have hAge : f + 1 ≤ A := by
    dsimp [A]
    have hsubpos : 1 ≤ q - 2 := by omega
    have hmul := Nat.mul_le_mul_left f hsubpos
    omega
  omega

private lemma dicksonWild_f_eq_one_or_exceptional_of_full_multiplier_relation
    (q f t d : ℕ) (hq : 3 ≤ q) (hf : 0 < f)
    (hfull : t = q - 1)
    (hrelation : d * (1 + f * (q - 2)) = t * (1 + f * q)) :
    f = 1 ∨ (q = 3 ∧ f = 3) := by
  by_cases hf1 : f = 1
  · exact Or.inl hf1
  right
  have hf2 : 2 ≤ f := by omega
  let u := q - 2
  let A := 1 + f * u
  have hu : 1 ≤ u := by simp [u]; omega
  have hApos : 0 < A := by simp [A]
  have hqEq : q = u + 2 := by simp [u]; omega
  have hqm : q - 1 = u + 1 := by omega
  have hqp : q + 1 = u + 3 := by omega
  have hfEq : f = (f - 1) + 1 := by omega
  have hid : (q - 1) * (1 + f * q) =
      (q + 1) * A + 2 * (f - 1) := by
    change (q - 1) * (1 + f * q) =
      (q + 1) * (1 + f * u) + 2 * (f - 1)
    rw [hqm, hqp, hqEq, hfEq]
    ring_nf
    omega
  have hprod : d * A = (q + 1) * A + 2 * (f - 1) := by
    change d * A = t * (1 + f * q) at hrelation
    rw [hrelation, hfull, hid]
  have hgt : (q + 1) * A < d * A := by omega
  have hdq : q + 1 < d := (Nat.mul_lt_mul_right hApos).mp hgt
  have hlower : (q + 2) * A ≤ d * A :=
    Nat.mul_le_mul_right A (by omega)
  have hAle : A ≤ 2 * (f - 1) := by
    rw [hprod] at hlower
    have hmul : (q + 2) * A = (q + 1) * A + A := by ring
    rw [hmul] at hlower
    omega
  have hq3 : q = 3 := by
    by_contra hne
    have hq4 : 4 ≤ q := by omega
    have hAge : 1 + 2 * f ≤ A := by
      dsimp [A, u]
      have hu2 : 2 ≤ q - 2 := by omega
      have hmul := Nat.mul_le_mul_left f hu2
      omega
    omega
  refine ⟨hq3, ?_⟩
  have hA : A = f + 1 := by simp [A, u, hq3, Nat.add_comm]
  have hd5 : d = 5 := by
    have hdge : 5 ≤ d := by omega
    have hdle : d ≤ 5 := by
      by_contra hne
      have hd6 : 6 ≤ d := by omega
      rw [hA, hq3] at hprod
      nlinarith
    omega
  rw [hA, hq3, hd5] at hprod
  omega

private lemma dicksonWild_same_orbit_of_stabilizer_card_six
    {G X : Type*} [Group G] [MulAction G X] [Finite G]
    (x₆ x₅ : dicksonWildExceptional G X)
    (h₆ : Nat.card (MulAction.stabilizer G x₆) = 6)
    (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
    (horbits : Nat.card
      (MulAction.orbitRel.Quotient G (dicksonWildExceptional G X)) = 2)
    {x y : dicksonWildExceptional G X}
    (hx : Nat.card (MulAction.stabilizer G x) = 6)
    (hy : Nat.card (MulAction.stabilizer G y) = 6) :
    Quotient.mk'' x = (Quotient.mk'' y :
      MulAction.orbitRel.Quotient G (dicksonWildExceptional G X)) := by
  classical
  let E := dicksonWildExceptional G X
  let Ω := MulAction.orbitRel.Quotient G E
  have h₆₅ : (Quotient.mk'' x₆ : Ω) ≠ Quotient.mk'' x₅ := by
    intro h
    have hc := dicksonWild_card_stabilizer_eq_of_quotient_eq x₆ x₅ h
    omega
  let reps : Fin 2 → Ω := ![Quotient.mk'' x₆, Quotient.mk'' x₅]
  have hrepsInj : Function.Injective reps := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp_all [reps]
  let _ : Finite Ω := Nat.finite_of_card_ne_zero (by rw [horbits]; decide)
  have hΩ : Nat.card Ω = 2 := by simpa [Ω, E] using horbits
  have hrepsBij : Function.Bijective reps :=
    hrepsInj.bijective_of_nat_card_le (by rw [hΩ, Nat.card_fin])
  have hx₆ : (Quotient.mk'' x : Ω) = Quotient.mk'' x₆ := by
    obtain ⟨i, hi⟩ := hrepsBij.2 (Quotient.mk'' x)
    fin_cases i
    · simpa [reps] using hi.symm
    · have hc := dicksonWild_card_stabilizer_eq_of_quotient_eq x₅ x
          (by simpa [reps] using hi)
      omega
  have hy₆ : (Quotient.mk'' y : Ω) = Quotient.mk'' x₆ := by
    obtain ⟨i, hi⟩ := hrepsBij.2 (Quotient.mk'' y)
    fin_cases i
    · simpa [reps] using hi.symm
    · have hc := dicksonWild_card_stabilizer_eq_of_quotient_eq x₅ y
          (by simpa [reps] using hi)
      omega
  exact hx₆.trans hy₆.symm

private lemma dicksonWild_card_centralizer_in_order_six_le_two
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (H : Subgroup G) (hHcard : Nat.card H = 6)
    (t : H) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) ≤ 2 := by
  let C := Subgroup.centralizer ({t} : Set H)
  have htmem : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
  have htwoDiv : 2 ∣ Nat.card C := by
    simpa only [ht] using Subgroup.orderOf_dvd_natCard C htmem
  have hcardDiv : Nat.card C ∣ 6 := by
    rw [← hHcard]
    exact Subgroup.card_subgroup_dvd_card C
  have hCcard : Nat.card C = 2 ∨ Nat.card C = 6 := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hCle : Nat.card C ≤ 6 := Nat.le_of_dvd (by decide) hcardDiv
    interval_cases hc : Nat.card C
    · norm_num [hc] at htwoDiv
    · norm_num
    · norm_num [hc] at htwoDiv
    · norm_num [hc] at hcardDiv
    · norm_num [hc] at htwoDiv
    · norm_num
  rcases hCcard with hCcard | hCcard
  · change Nat.card C ≤ 2
    omega
  · have hCtop : C = ⊤ := C.eq_top_of_card_eq (hCcard.trans hHcard.symm)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (by
      rw [hHcard]
      norm_num)
    have huC : u ∈ C := by rw [hCtop]; simp
    have hcomm : Commute u t := by
      rw [Subgroup.mem_centralizer_iff] at huC
      exact (huC t (Set.mem_singleton t)).symm
    have hut : orderOf (u * t) = 6 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hu, ht]; decide), hu, ht]
    have hutPGL : orderOf (((u * t : H) : G) : PGL p) = 6 := by
      simpa only [Subgroup.orderOf_coe] using hut
    have hchar := orderOf_eq_char_of_char_dvd (((u * t : H) : G) : PGL p)
      (by rw [hutPGL]; decide) (by rw [hutPGL, hp]; norm_num)
    rw [hutPGL, hp] at hchar
    omega

private lemma dicksonWild_card_centralizer_le_four_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (j : G →* PGL p) (hj : Function.Injective j)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (t : G) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) ≤ 4 := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let _ : MulAction G X := MulAction.compHom _ j
  let E := dicksonWildExceptional G X
  have ht1 : t ≠ 1 := by intro h; simp_all
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have htpow : t ^ p ≠ 1 := by
    intro htp
    apply ht1
    calc
      t = t ^ 3 := by rw [show 3 = 2 + 1 by omega, pow_succ, ht2, one_mul]
      _ = t ^ p := (congrArg (fun n : ℕ ↦ t ^ n) hp).symm
      _ = 1 := htp
  let F := MulAction.fixedBy X t
  have hF : Nat.card F = 2 := by
    rcases dicksonWild_card_fixedBy_normal_form G j hj t ht1 with h | h
    · exact (htpow h.1).elim
    · exact h.2
  have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
  let _ : Finite F := hFdata.2
  let xF : F := Classical.choice hFdata.1
  have htfix : t • xF.1 = xF.1 := MulAction.mem_fixedBy.mp xF.2
  let xE : E := ⟨xF.1, ⟨t, ht1, htfix⟩⟩
  let H := MulAction.stabilizer G xE
  have htmem : t ∈ H := Subtype.ext htfix
  have htdiv := Subgroup.orderOf_dvd_natCard H htmem
  have hHcard : Nat.card H = 6 := by
    rcases hall xE with h | h
    · exact h
    · rw [h, ht] at htdiv
      norm_num at htdiv
  let C := Subgroup.centralizer ({t} : Set G)
  let O := MulAction.orbit C xF.1
  have horbitFixed (y : X) (hy : y ∈ O) : t • y = y := by
    obtain ⟨c, hc⟩ := hy
    have hcomm : t * (c : G) = (c : G) * t :=
      (Subgroup.mem_centralizer_iff.mp c.2) t (Set.mem_singleton t)
    have hfix : t • ((c : G) • xF.1) = (c : G) • xF.1 := by
      calc
        t • ((c : G) • xF.1) = (t * (c : G)) • xF.1 :=
          (mul_smul t (c : G) xF.1).symm
        _ = ((c : G) * t) • xF.1 := by rw [hcomm]
        _ = (c : G) • (t • xF.1) := mul_smul (c : G) t xF.1
        _ = (c : G) • xF.1 := by rw [htfix]
    rw [← hc]
    exact hfix
  let toFixed : O → F := fun y ↦
    ⟨y.1, MulAction.mem_fixedBy.mpr (horbitFixed y.1 y.2)⟩
  have htoFixed : Function.Injective toFixed := by
    intro y z h
    apply Subtype.ext
    exact congrArg (fun w : F ↦ w.1) h
  have hO : Nat.card O ≤ 2 := by
    rw [← hF]
    exact Nat.card_le_card_of_injective toFixed htoFixed
  let S := MulAction.stabilizer C xF.1
  let tH : H := ⟨t, htmem⟩
  have htH : orderOf tH = 2 := by
    calc
      orderOf tH = orderOf (tH : G) := (Subgroup.orderOf_coe tH).symm
      _ = orderOf t := by rfl
      _ = 2 := ht
  let CH := Subgroup.centralizer ({tH} : Set H)
  let k : S → CH := fun c ↦ ⟨⟨c.1.1, by exact Subtype.ext c.2⟩, by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.1.2) t (Set.mem_singleton t)⟩
  have hkinj : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : CH ↦ (z.1.1 : G)) hab
  have hS : Nat.card S ≤ 2 := by
    calc
      Nat.card S ≤ Nat.card CH := Nat.card_le_card_of_injective k hkinj
      _ ≤ 2 := dicksonWild_card_centralizer_in_order_six_le_two
        G hp H hHcard tH htH
  let orbitMap : C → O := fun c ↦
    ⟨c • xF.1, MulAction.mem_orbit_iff.mpr ⟨c, rfl⟩⟩
  have horbitMap : Function.Surjective orbitMap := by
    intro y
    obtain ⟨c, hc⟩ := y.2
    exact ⟨c, Subtype.ext hc⟩
  let _ : Finite O := Finite.of_surjective orbitMap horbitMap
  let _ := Fintype.ofFinite C
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite S
  have hprod : Nat.card O * Nat.card S = Nat.card C := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group C xF.1
  change Nat.card C ≤ 4
  nlinarith

private lemma dicksonWild_sylow_two_sq_eq_one_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G]
    (j : G →* PGL p) (hj : Function.Injective j)
    (hGcard : Nat.card G = 60)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (Q : Sylow 2 G) (u : Q) : (u : G) ^ 2 = 1 := by
  classical
  by_cases hu1 : (u : G) = 1
  · simp [hu1]
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hQcard : Nat.card Q = 4 := by
    rw [Sylow.card_eq_multiplicity, hGcard]
    norm_num [Nat.factorization, Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
  let X := Projectivization (K p) (Fin 2 → K p)
  let _ : MulAction G X := MulAction.compHom _ j
  let E := dicksonWildExceptional G X
  let F := MulAction.fixedBy X (u : G)
  have hFpos : 0 < Nat.card F := by
    rcases dicksonWild_card_fixedBy_normal_form G j hj (u : G) hu1 with h | h
    · rw [h.2]
      decide
    · rw [h.2]
      decide
  have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp hFpos
  let xF : F := Classical.choice hFdata.1
  let xE : E := ⟨xF.1, ⟨(u : G), hu1, MulAction.mem_fixedBy.mp xF.2⟩⟩
  have humem : (u : G) ∈ MulAction.stabilizer G xE := by
    exact Subtype.ext (MulAction.mem_fixedBy.mp xF.2)
  have hdivQ := Subgroup.orderOf_dvd_natCard (Q : Subgroup G) u.2
  have hdivS := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer G xE) humem
  have hordpos : 0 < orderOf (u : G) := by
    simpa only [Subgroup.orderOf_coe] using orderOf_pos u
  have hordne : orderOf (u : G) ≠ 1 := mt orderOf_eq_one_iff.mp hu1
  have hordle : orderOf (u : G) ≤ 4 := by
    rw [hQcard] at hdivQ
    exact Nat.le_of_dvd (by decide) hdivQ
  have hord : orderOf (u : G) = 2 := by
    rcases hall xE with hs | hs
    · rw [hs] at hdivS
      interval_cases orderOf (u : G) <;>
        simp_all [Nat.dvd_iff_mod_eq_zero]
    · rw [hs] at hdivS
      interval_cases orderOf (u : G) <;>
        simp_all [Nat.dvd_iff_mod_eq_zero]
  simpa only [hord] using pow_orderOf_eq_one (u : G)

private lemma dicksonWild_sylow_two_commute_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G]
    (j : G →* PGL p) (hj : Function.Injective j)
    (hGcard : Nat.card G = 60)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (Q : Sylow 2 G) (a b : Q) : Commute (a : G) (b : G) := by
  have ha2 := dicksonWild_sylow_two_sq_eq_one_exceptional
    G j hj hGcard hall Q a
  have hb2 := dicksonWild_sylow_two_sq_eq_one_exceptional
    G j hj hGcard hall Q b
  let ab : Q := a * b
  have hab2 := dicksonWild_sylow_two_sq_eq_one_exceptional
    G j hj hGcard hall Q ab
  have haInv : (a : G) = (a : G)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [pow_two] using ha2)
  have hbInv : (b : G) = (b : G)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hb2)
  have habInv : (a : G) * b = ((a : G) * b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [ab, pow_two] using hab2)
  exact calc
    (a : G) * b = ((a : G) * b)⁻¹ := habInv
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev (a : G) b
    _ = (b : G) * a := by rw [← hbInv, ← haInv]

private lemma dicksonWild_sylow_two_unique_of_mem_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (j : G →* PGL p) (hj : Function.Injective j)
    (hGcard : Nat.card G = 60)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (r : G) (hr : orderOf r = 2) (Q R : Sylow 2 G)
    (hrQ : r ∈ Q) (hrR : r ∈ R) : Q = R := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hsylowCard (S : Sylow 2 G) : Nat.card S = 4 := by
    rw [Sylow.card_eq_multiplicity, hGcard]
    norm_num [Nat.factorization, Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
  have centralizerEq (S : Sylow 2 G) (hrS : r ∈ S) :
      (S : Subgroup G) = Subgroup.centralizer ({r} : Set G) := by
    have hSle : (S : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact dicksonWild_sylow_two_commute_exceptional
        G j hj hGcard hall S ⟨r, hrS⟩ ⟨s, hs⟩
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [hsylowCard S]
    exact dicksonWild_card_centralizer_le_four_exceptional G hp j hj hall r hr
  apply Sylow.ext
  exact (centralizerEq Q hrQ).trans (centralizerEq R hrR).symm

private lemma dicksonWild_involutions_conjugate_of_card_six
    {H : Type*} [Group H] [Finite H] (hHcard : Nat.card H = 6)
    (a b : H) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ c : H, c * a * c⁻¹ = b := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let A := Subgroup.zpowers a
  have hAcard : Nat.card A = 2 := by rw [Nat.card_zpowers, ha]
  have hAgroup : IsPGroup 2 A := IsPGroup.iff_card.mpr ⟨1, by
    simpa only [pow_one, Nat.card_eq_fintype_card] using hAcard⟩
  obtain ⟨Qa, hAQa⟩ := hAgroup.exists_le_sylow
  let B := Subgroup.zpowers b
  have hBcard : Nat.card B = 2 := by rw [Nat.card_zpowers, hb]
  have hBgroup : IsPGroup 2 B := IsPGroup.iff_card.mpr ⟨1, by
    simpa only [pow_one, Nat.card_eq_fintype_card] using hBcard⟩
  obtain ⟨Qb, hBQb⟩ := hBgroup.exists_le_sylow
  have hQbcard : Nat.card Qb = 2 := by
    rw [Sylow.card_eq_multiplicity, hHcard]
    norm_num [Nat.factorization, Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H Qa Qb
  have haQa : a ∈ Qa := hAQa (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hbQb : b ∈ Qb := hBQb (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hcaQa : c * a * c⁻¹ ∈ (c • Qa : Sylow 2 H) := by
    change c * a * c⁻¹ ∈ MulAut.conj c • (Qa : Set H)
    simpa only [MulAut.smul_def, MulAut.conj_apply] using
      (Set.smul_mem_smul_set (a := MulAut.conj c) haQa)
  have hcaQb : c * a * c⁻¹ ∈ Qb := by rwa [hc] at hcaQa
  let ca : Qb := ⟨c * a * c⁻¹, hcaQb⟩
  let bb : Qb := ⟨b, hbQb⟩
  have ha1 : a ≠ 1 := by intro h; simp_all
  have hca1 : ca ≠ 1 := by
    intro h
    apply ha1
    have hval : c * a * c⁻¹ = 1 := congrArg Subtype.val h
    calc
      a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [hval]; simp
  have hb1 : bb ≠ 1 := by
    intro h
    have hval : b = 1 := congrArg Subtype.val h
    have : b ≠ 1 := by intro h; simp_all
    exact this hval
  have hunique : ∃! z : Qb, z ≠ 1 := (Nat.card_eq_two_iff' 1).mp hQbcard
  have hEq : ca = bb := hunique.unique hca1 hb1
  exact ⟨c, congrArg Subtype.val hEq⟩

private lemma dicksonWild_involutions_conjugate_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (j : G →* PGL p) (hj : Function.Injective j)
    (x₆ x₅ :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p)))
    (h₆ : Nat.card (MulAction.stabilizer G x₆) = 6)
    (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (horbits :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      Nat.card (MulAction.orbitRel.Quotient G E) = 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) :
    ∃ g : G, g * t * g⁻¹ = s := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let _ : MulAction G X := MulAction.compHom _ j
  let E := dicksonWildExceptional G X
  have cardFixed (a : G) (ha : orderOf a = 2) :
      Nat.card (MulAction.fixedBy X a) = 2 := by
    have ha1 : a ≠ 1 := by intro h; simp_all
    have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
    have hapow : a ^ p ≠ 1 := by
      intro hap
      apply ha1
      calc
        a = a ^ 3 := by rw [show 3 = 2 + 1 by omega, pow_succ, ha2, one_mul]
        _ = a ^ p := (congrArg (fun n : ℕ ↦ a ^ n) hp).symm
        _ = 1 := hap
    rcases dicksonWild_card_fixedBy_normal_form G j hj a ha1 with h | h
    · exact (hapow h.1).elim
    · exact h.2
  have point (a : G) (ha : orderOf a = 2) :
      ∃ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∧ a • x = x := by
    have ha1 : a ≠ 1 := by intro h; simp_all
    let F := MulAction.fixedBy X a
    have hF : Nat.card F = 2 := cardFixed a ha
    have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
    let z : F := Classical.choice hFdata.1
    let x : E := ⟨z.1, ⟨a, ha1, MulAction.mem_fixedBy.mp z.2⟩⟩
    have hfix : a • x = x := Subtype.ext (MulAction.mem_fixedBy.mp z.2)
    have hdiv := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer G x) hfix
    have hstab : Nat.card (MulAction.stabilizer G x) = 6 := by
      rcases hall x with h | h
      · exact h
      · rw [h, ha] at hdiv
        norm_num at hdiv
    exact ⟨x, hstab, hfix⟩
  obtain ⟨xt, hxt, htfix⟩ := point t ht
  obtain ⟨xs, hxs, hsfix⟩ := point s hs
  have hquot : Quotient.mk'' xt =
      (Quotient.mk'' xs : MulAction.orbitRel.Quotient G E) :=
    dicksonWild_same_orbit_of_stabilizer_card_six x₆ x₅ h₆ h₅ horbits hxt hxs
  obtain ⟨g, hg⟩ := Quotient.exact hquot
  let S := MulAction.stabilizer G xs
  let ct : S := ⟨g⁻¹ * t * g, by
    change (g⁻¹ * t * g) • xs = xs
    calc
      (g⁻¹ * t * g) • xs = g⁻¹ • (t • (g • xs)) := by simp only [mul_smul]
      _ = g⁻¹ • (t • xt) := congrArg (fun z : E ↦ g⁻¹ • (t • z)) hg
      _ = g⁻¹ • xt := by rw [htfix]
      _ = xs := by rw [← hg, inv_smul_smul]⟩
  let ss : S := ⟨s, hsfix⟩
  have hct : orderOf ct = 2 := by
    calc
      orderOf ct = orderOf (ct : G) := (Subgroup.orderOf_coe ct).symm
      _ = orderOf (g⁻¹ * t * g) := rfl
      _ = orderOf t := by
        simpa using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
      _ = 2 := ht
  have hss : orderOf ss = 2 := by
    calc
      orderOf ss = orderOf (ss : G) := (Subgroup.orderOf_coe ss).symm
      _ = orderOf s := rfl
      _ = 2 := hs
  obtain ⟨c, hc⟩ := dicksonWild_involutions_conjugate_of_card_six hxs ct ss hct hss
  refine ⟨(c : G) * g⁻¹, ?_⟩
  have hcval : (c : G) * (g⁻¹ * t * g) * (c : G)⁻¹ = s :=
    congrArg Subtype.val hc
  calc
    ((c : G) * g⁻¹) * t * ((c : G) * g⁻¹)⁻¹ =
        (c : G) * (g⁻¹ * t * g) * (c : G)⁻¹ := by group
    _ = s := hcval

private lemma dicksonWild_card_ne_one_of_card_four
    {H : Type*} [Group H] [Finite H] (hHcard : Nat.card H = 4) :
    Nat.card {u : H // u ≠ 1} = 3 := by
  classical
  let _ := Fintype.ofFinite H
  let _ := Fintype.ofFinite {u : H // u ≠ 1}
  let _ := Fintype.ofFinite {u : H // u = 1}
  have hHF : Fintype.card H = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hHcard
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun u : H ↦ u = 1)]
  simp [hHF]

private lemma dicksonWild_card_sylow_two_eq_five_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (j : G →* PGL p) (hj : Function.Injective j)
    (hGcard : Nat.card G = 60)
    (x₆ x₅ :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p)))
    (h₆ : Nat.card (MulAction.stabilizer G x₆) = 6)
    (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (horbits :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      Nat.card (MulAction.orbitRel.Quotient G E) = 2) :
    Nat.card (Sylow 2 G) = 5 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hsylowCard (Q : Sylow 2 G) : Nat.card Q = 4 := by
    rw [Sylow.card_eq_multiplicity, hGcard]
    norm_num [Nat.factorization, Nat.primeFactorsList, Nat.minFac, Nat.minFacAux]
  have sylowCentralizer (r : G) (hr : orderOf r = 2) (Q : Sylow 2 G)
      (hrQ : r ∈ Q) : (Q : Subgroup G) = Subgroup.centralizer ({r} : Set G) := by
    have hQle : (Q : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact dicksonWild_sylow_two_commute_exceptional
        G j hj hGcard hall Q ⟨r, hrQ⟩ ⟨q, hq⟩
    apply Subgroup.eq_of_le_of_card_ge hQle
    rw [hsylowCard Q]
    exact dicksonWild_card_centralizer_le_four_exceptional G hp j hj hall r hr
  let P : Sylow 2 G := Classical.choice inferInstance
  have hPcard : Nat.card P = 4 := hsylowCard P
  let _ : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; decide)
  obtain ⟨t, ht1⟩ := exists_ne (1 : P)
  have ht1G : (t : G) ≠ 1 := fun h ↦ ht1 (Subtype.ext h)
  have ht2pow := dicksonWild_sylow_two_sq_eq_one_exceptional
    G j hj hGcard hall P t
  have htorder : orderOf (t : G) = 2 := orderOf_eq_prime ht2pow ht1G
  let C := Subgroup.centralizer ({(t : G)} : Set G)
  have hPC : (P : Subgroup G) = C := sylowCentralizer t htorder P t.2
  have hCcard : Nat.card C = 4 := by rw [← hPC, hPcard]
  let I := {r : G // orderOf r = 2}
  let O := MulAction.orbit (ConjAct G) (t : G)
  let toInvolution : O → I := fun y ↦ ⟨y.1, by
    obtain ⟨c, hc⟩ := y.2
    rw [← hc]
    calc
      orderOf (c • (t : G)) = orderOf (t : G) := by
        change orderOf ((MulAut.conj (ConjAct.ofConjAct c)) (t : G)) = _
        exact MulEquiv.orderOf_eq (MulAut.conj (ConjAct.ofConjAct c)) t
      _ = 2 := htorder⟩
  have htoInvolutionInj : Function.Injective toInvolution := by
    intro y z h
    apply Subtype.ext
    exact congrArg (fun w : I ↦ w.1) h
  have htoInvolutionSurj : Function.Surjective toInvolution := by
    intro r
    obtain ⟨g, hg⟩ := dicksonWild_involutions_conjugate_exceptional
      G hp j hj x₆ x₅ h₆ h₅ hall horbits t r htorder r.2
    have hact : ConjAct.toConjAct g • (t : G) = r.1 := by
      simpa only [ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.conj_apply] using hg
    exact ⟨⟨r.1, ⟨ConjAct.toConjAct g, hact⟩⟩, Subtype.ext rfl⟩
  let S := MulAction.stabilizer (ConjAct G) (t : G)
  have hScard : Nat.card S = 4 := by
    calc
      Nat.card S = Nat.card (Subgroup.centralizer ({(t : G)} : Set G)) := by
        simpa [S] using
          (Subgroup.nat_card_centralizer_nat_card_stabilizer (t : G)).symm
      _ = Nat.card C := rfl
      _ = 4 := hCcard
  let _ : Finite O := Finite.of_injective toInvolution htoInvolutionInj
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofEquiv G (ConjAct.toConjAct (G := G)).toEquiv
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite S
  have hprod : Nat.card O * Nat.card S = Nat.card (ConjAct G) := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (t : G)
  have hOcard : Nat.card O = 15 := by
    have hconj : Nat.card (ConjAct G) = Nat.card G :=
      Nat.card_congr (ConjAct.ofConjAct (G := G)).toEquiv
    rw [hScard, hconj, hGcard] at hprod
    omega
  have hIcard : Nat.card I = 15 := by
    rw [← hOcard]
    exact (Nat.card_congr (Equiv.ofBijective toInvolution
      ⟨htoInvolutionInj, htoInvolutionSurj⟩)).symm
  let A := (Q : Sylow 2 G) × {u : (Q : Subgroup G) // u ≠ 1}
  let toI : A → I := fun z ↦ ⟨(z.2.1 : G), by
    have hu1 : (z.2.1 : G) ≠ 1 := by
      exact fun h ↦ z.2.2 (Subtype.ext h)
    exact orderOf_eq_prime
      (dicksonWild_sylow_two_sq_eq_one_exceptional
        G j hj hGcard hall z.1 z.2.1) hu1⟩
  have htoIInj : Function.Injective toI := by
    rintro ⟨Qa, ua⟩ ⟨Qb, ub⟩ hab
    have hval : (ua.1 : G) = (ub.1 : G) := congrArg (fun r : I ↦ r.1) hab
    have huaQb : (ua.1 : G) ∈ Qb := by rw [hval]; exact ub.1.2
    have hQR : Qa = Qb := dicksonWild_sylow_two_unique_of_mem_exceptional
      G hp j hj hGcard hall (ua.1 : G) (toI ⟨Qa, ua⟩).2
        Qa Qb ua.1.2 huaQb
    subst Qb
    have huv : ua = ub := Subtype.ext (Subtype.ext hval)
    subst ub
    rfl
  have htoISurj : Function.Surjective toI := by
    intro r
    let R : Subgroup G := Subgroup.zpowers r.1
    have hRcard : Nat.card R = 2 := by
      rw [show Nat.card R = orderOf r.1 by exact Nat.card_zpowers r.1, r.2]
    have hRgroup : IsPGroup 2 R := IsPGroup.iff_card.mpr ⟨1, by
      simpa only [pow_one, Nat.card_eq_fintype_card] using hRcard⟩
    obtain ⟨Q, hRQ⟩ := hRgroup.exists_le_sylow
    have hrR : r.1 ∈ R := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    let u : Q := ⟨r.1, hRQ hrR⟩
    have hu1 : u ≠ 1 := by
      intro h
      have hr1 : r.1 = 1 := congrArg Subtype.val h
      have hrne : r.1 ≠ 1 := by
        intro hr
        have hord := r.2
        rw [hr] at hord
        norm_num at hord
      exact hrne hr1
    exact ⟨⟨Q, ⟨u, hu1⟩⟩, Subtype.ext rfl⟩
  have hfiberCard (Q : Sylow 2 G) :
      Nat.card {u : (Q : Subgroup G) // u ≠ 1} = 3 :=
    dicksonWild_card_ne_one_of_card_four (hsylowCard Q)
  let _ := Fintype.ofFinite (Sylow 2 G)
  let _ (Q : Sylow 2 G) := Fintype.ofFinite {u : (Q : Subgroup G) // u ≠ 1}
  have hAcard : Nat.card A = Nat.card (Sylow 2 G) * 3 := by
    calc
      Nat.card A = ∑ Q : Sylow 2 G,
          Nat.card {u : (Q : Subgroup G) // u ≠ 1} := by
        simp only [A, Nat.card_eq_fintype_card, Fintype.card_sigma]
      _ = ∑ _Q : Sylow 2 G, 3 := by
        apply Finset.sum_congr rfl
        intro Q _
        exact hfiberCard Q
      _ = Nat.card (Sylow 2 G) * 3 := by
        simp [Nat.card_eq_fintype_card]
  have hA15 : Nat.card A = 15 := by
    rw [Nat.card_congr (Equiv.ofBijective toI ⟨htoIInj, htoISurj⟩), hIcard]
  omega

private lemma dicksonWild_a5_case_of_exceptional
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hp : p = 3)
    (P : Sylow p G) (hPnormal : ¬(P : Subgroup G).Normal)
    (hPcard : Nat.card (P : Subgroup G) = 3)
    (j : G →* PGL p) (hj : Function.Injective j)
    (hGcard : Nat.card G = 60)
    (x₆ x₅ :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p)))
    (h₆ : Nat.card (MulAction.stabilizer G x₆) = 6)
    (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
    (hall :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      ∀ x : E, Nat.card (MulAction.stabilizer G x) = 6 ∨
        Nat.card (MulAction.stabilizer G x) = 5)
    (horbits :
      let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
        MulAction.compHom _ j
      let E := dicksonWildExceptional G (Projectivization (K p) (Fin 2 → K p))
      Nat.card (MulAction.orbitRel.Quotient G E) = 2) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hn₂ : Nat.card (Sylow 2 G) = 5 :=
    dicksonWild_card_sylow_two_eq_five_exceptional
      G hp j hj hGcard x₆ x₅ h₆ h₅ hall horbits
  let Q : Sylow 2 G := Classical.choice inferInstance
  let ρ := MulAction.toPermHom G (Sylow 2 G)
  let H := ρ.ker
  have hnotTwoH : ¬2 ∣ Nat.card H := by
    intro htwo
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 htwo
    let g : G := u
    have hgorder : orderOf g = 2 := (Subgroup.orderOf_coe u).trans hu
    let R : Subgroup G := Subgroup.zpowers g
    have hRcard : Nat.card R = 2 := by
      rw [show Nat.card R = orderOf g by exact Nat.card_zpowers g, hgorder]
    have hRgroup : IsPGroup 2 R := IsPGroup.of_card (hRcard.trans (pow_one 2).symm)
    have hgker : g ∈ H := u.2
    have hgmem (S : Sylow 2 G) : g ∈ S := by
      have hρg : ρ g = 1 := hgker
      have hgfix : g • S = S := Equiv.congr_fun hρg S
      have hRnorm : R ≤ Subgroup.normalizer S := by
        apply Subgroup.zpowers_le.mpr
        exact Sylow.smul_eq_iff_mem_normalizer.mp hgfix
      have hRS : R ≤ S := by
        rw [← inf_eq_left, ← hRgroup.inf_normalizer_sylow S]
        exact inf_eq_left.mpr hRnorm
      exact hRS (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    let _ : Nontrivial (Sylow 2 G) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hn₂]; decide)
    obtain ⟨S, hSQ⟩ := exists_ne Q
    have heq := dicksonWild_sylow_two_unique_of_mem_exceptional
      G hp j hj hGcard hall g hgorder Q S (hgmem Q) (hgmem S)
    exact hSQ heq.symm
  have hHle : H ≤ MulAction.stabilizer G Q := by
    intro g hg
    have hρg : ρ g = 1 := hg
    exact Equiv.congr_fun hρg Q
  have hstabIndex : (MulAction.stabilizer G Q).index = 5 := by
    rw [Q.stabilizer_eq_normalizer, ← Q.card_eq_index_normalizer, hn₂]
  have hindexFive : 5 ∣ H.index := by
    rw [← hstabIndex]
    exact Subgroup.index_dvd_of_le hHle
  have hprod : Nat.card H * H.index = 60 := by rw [H.card_mul_index, hGcard]
  have hindexNe : H.index ≠ 0 := by intro h; simp_all
  have hindexGe : 5 ≤ H.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hindexNe) hindexFive
  have hHleTwelve : Nat.card H ≤ 12 := by nlinarith
  have hHcardCases : Nat.card H = 1 ∨ Nat.card H = 3 := by
    have hHpos : 0 < Nat.card H := Nat.card_pos
    interval_cases Nat.card H <;>
      simp_all [Nat.dvd_iff_mod_eq_zero] <;> omega
  have hHcardOne : Nat.card H = 1 := by
    rcases hHcardCases with hHcardOne | hHcardThree
    · exact hHcardOne
    · exfalso
      have hHgroup : IsPGroup p H := IsPGroup.iff_card.mpr ⟨1, by
        rw [hHcardThree, hp]
        norm_num⟩
      have hHleP : H ≤ P := hHgroup.le_sylow_of_normal P
      have hHP : H = (P : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge hHleP
        rw [hHcardThree, hPcard]
      apply hPnormal
      rw [← hHP]
      infer_instance
  have hρinj : Function.Injective ρ :=
    (ρ.ker_eq_bot_iff).mp (Subgroup.card_eq_one.mp hHcardOne)
  let _ := Fintype.ofFinite (Sylow 2 G)
  have hSylowFintype : Fintype.card (Sylow 2 G) = 5 := by
    simpa only [Nat.card_eq_fintype_card] using hn₂
  let q : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hSylowFintype
  let σ : G →* Equiv.Perm (Fin 5) := q.permCongrHom.toMonoidHom.comp ρ
  have hσinj : Function.Injective σ := q.permCongrHom.injective.comp hρinj
  have hPermCard : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hσindex : σ.range.index = 2 :=
    dicksonWild_perm_range_index_eq_two_of_card
      σ hσinj 60 hGcard (by omega)
  exact dicksonWild_mulEquiv_alternating_of_perm_index_two σ hσinj hσindex

private lemma dicksonWild_card_order_char_with_multiplier_eq_two
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) (l : L) :
    Nat.card {n : {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l} = 2 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let E := {n : N // (g * (n.1 : G)) ^ p = 1}
  let toL : E → L := fun n ↦ (coord n.1).2
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  obtain ⟨S, hS, hS10⟩ := hout g hg
  have hEcard : Nat.card E = 2 * t :=
    dicksonWild_card_order_char_in_normalizer_coset_eq G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf g hg
  have hfiber (u : L) : Nat.card {n : E // toL n = u} ≤ 2 := by
    let uK : (K p)ˣ := Units.map M.subtype.toMonoidHom u.1
    let c : K p := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) * (uK : K p)
    let toRoot : {n : E // toL n = u} → {x : K p // x ^ 2 = c} := fun n ↦ ⟨
      Matrix.trace (((S * A n.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))), by
        have hnSecond : (coord n.1.1).2 = u := n.2
        have hgne : g * (n.1.1.1 : G) ≠ 1 := by
          intro hone
          apply hg
          have hgeq : g = (n.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
          rw [hgeq]
          exact N.inv_mem n.1.1.2
        have horderG : orderOf (g * (n.1.1.1 : G)) = p :=
          orderOf_eq_prime n.1.2 hgne
        have horderJ : orderOf (j (g * (n.1.1.1 : G))) = p :=
          (orderOf_injective j hj (g * (n.1.1.1 : G))).trans horderG
        have hmk : Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
            j (g * (n.1.1.1 : G)) := by
          calc
            Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
                Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A n.1.1) :=
              map_mul Matrix.ProjGenLinGroup.mk S (A n.1.1)
            _ = j g * j n.1.1.1 := by rw [hS, hnormal' n.1.1]
            _ = j (g * (n.1.1.1 : G)) := (map_mul j g n.1.1.1).symm
        have hpar : ((S * A n.1.1 : GL (Fin 2) (K p)) :
            Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
          apply dicksonWild_lift_isParabolic_of_order_eq_char
          rw [hmk]
          exact horderJ
        have hdisc := hpar.2
        rw [Matrix.discr_fin_two] at hdisc
        have heq := sub_eq_zero.mp hdisc
        rw [hA n.1.1, hnSecond, DicksonWildAffine.det_mul_affineGL] at heq
        rw [hA n.1.1, hnSecond]
        simpa [c, uK, mul_assoc] using heq⟩
    have htoRoot : Function.Injective toRoot := by
      intro x y hxy
      have hxSecond : (coord x.1.1).2 = u := x.2
      have hySecond : (coord y.1.1).2 = u := y.2
      have htrace := congrArg (fun z : {w : K p // w ^ 2 = c} ↦ z.1) hxy
      change Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) at htrace
      rw [hA x.1.1, hA y.1.1, hxSecond, hySecond,
        DicksonWildAffine.trace_mul_affineGL,
        DicksonWildAffine.trace_mul_affineGL] at htrace
      have hfirst : (coord x.1.1).1 = (coord y.1.1).1 := by
        apply Subtype.ext
        apply mul_left_cancel₀ hS10
        linear_combination htrace
      have hcoordEq : coord x.1.1 = coord y.1.1 := by
        apply Prod.ext hfirst
        exact hxSecond.trans hySecond.symm
      have hn : x.1.1 = y.1.1 := hcoord.1 hcoordEq
      apply Subtype.ext
      apply Subtype.ext
      exact hn
    let q : (K p)[X] := Polynomial.X ^ 2 - Polynomial.C c
    have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
    have hfinite : Set.Finite {x : K p | x ^ 2 = c} := by
      apply (Finset.finite_toSet (q.map (algebraMap (K p) (K p))).roots.toFinset).subset
      intro x hx
      rw [show (q.map (algebraMap (K p) (K p))).roots.toFinset = q.rootSet (K p) by rfl,
        Polynomial.mem_rootSet_of_ne hq0]
      change x ^ 2 = c at hx
      simpa [q] using sub_eq_zero.mpr hx
    let _ : Fintype {x : K p // x ^ 2 = c} := hfinite.fintype
    exact (Nat.card_le_card_of_injective toRoot htoRoot).trans
      (DicksonWildAffine.card_quadraticFiber_le_two c)
  have htotal : Nat.card E = 2 * Nat.card L := by rw [hEcard, hLcard]
  have hfiberEq : ∀ u : L, Nat.card {n : E // toL n = u} = 2 :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul toL 2 hfiber htotal
  exact hfiberEq l

set_option maxHeartbeats 800000 in
-- The trace-fiber argument expands several nested finite subtypes.
private lemma dicksonWild_exists_order_char_with_multiplier_and_trace
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (l : L) (r : K p)
    (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
      (Units.map M.subtype.toMonoidHom l.1 : K p)) :
    ∃ n : Subgroup.normalizer (P : Set G),
      (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
      Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
          GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let X := {n : {n : N // (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l}
  have hXcard : Nat.card X = 2 :=
    dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout g hg l
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hXcard
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  have htraceSq (z : X) :
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) ^ 2 = r ^ 2 := by
    have hgne : g * (z.1.1.1 : G) ≠ 1 := by
      intro hone
      apply hg
      have hgeq : g = (z.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
      rw [hgeq]
      exact N.inv_mem z.1.1.2
    have horderG : orderOf (g * (z.1.1.1 : G)) = p :=
      orderOf_eq_prime z.1.2 hgne
    have horderJ : orderOf (j (g * (z.1.1.1 : G))) = p :=
      (orderOf_injective j hj (g * (z.1.1.1 : G))).trans horderG
    have hmk : Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
        j (g * (z.1.1.1 : G)) := by
      calc
        Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
            Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A z.1.1) :=
          map_mul Matrix.ProjGenLinGroup.mk S (A z.1.1)
        _ = j g * j z.1.1.1 := by rw [hS, hnormal' z.1.1]
        _ = j (g * (z.1.1.1 : G)) := (map_mul j g z.1.1.1).symm
    have hpar : ((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact horderJ
    have hdisc := hpar.2
    rw [Matrix.discr_fin_two] at hdisc
    have heq := sub_eq_zero.mp hdisc
    have hdet : Matrix.det (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by
      rw [hA z.1.1, z.2, DicksonWildAffine.det_mul_affineGL]
    rw [hdet] at heq
    calc
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) ^ 2 =
          4 * (Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
            (Units.map M.subtype.toMonoidHom l.1 : K p)) := heq
      _ = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by ring
      _ = r ^ 2 := hr.symm
  have htraceInjective : Function.Injective (fun z : X ↦
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)))) := by
    intro z w htrace
    change Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
      Matrix.trace (((S * A w.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) at htrace
    rw [hA z.1.1, hA w.1.1, z.2, w.2,
      DicksonWildAffine.trace_mul_affineGL,
      DicksonWildAffine.trace_mul_affineGL] at htrace
    have hfirst : (coord z.1.1).1 = (coord w.1.1).1 := by
      apply Subtype.ext
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    have hcoordEq : coord z.1.1 = coord w.1.1 := by
      apply Prod.ext hfirst
      exact z.2.trans w.2.symm
    have hn : z.1.1 = w.1.1 := hcoord.1 hcoordEq
    apply Subtype.ext
    apply Subtype.ext
    exact hn
  have hxCases : Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq x)
  rcases hxCases with hx | hx
  · exact ⟨x.1.1, x.1.2, x.2, hx⟩
  have hyCases : Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq y)
  rcases hyCases with hy | hy
  · exact ⟨y.1.1, y.1.2, y.2, hy⟩
  exact (hxy (htraceInjective (hx.trans hy.symm))).elim

private lemma dicksonWild_normalized_order_char_lift_entries_mem
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (htrace : Matrix.trace (S : Matrix (Fin 2) (Fin 2) (K p)) = 2)
    (hdet : Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) = 1)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    ∀ i k, (S : Matrix (Fin 2) (Fin 2) (K p)) i k ∈ M := by
  classical
  have htwo : (2 : K p) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff (K p) p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    have hpgt : 2 < p := Fact.out
    omega
  have hfour : (4 : K p) ≠ 0 := by
    rw [show (4 : K p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have htraceEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 + S 1 1 = 2 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htrace
  have findTrace (l : L) (r : K p)
      (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom l.1 : K p)) :
      ∃ n : Subgroup.normalizer (P : Set G),
        (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
        Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
            GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r :=
    dicksonWild_exists_order_char_with_multiplier_and_trace G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
      g hg S hS hS10 l r hr
  have hnegRoot : (-2 : K p) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) := by
    rw [hdet]
    norm_num
  obtain ⟨nNeg, -, hnNeg, htrNeg⟩ := findTrace 1 (-2) hnegRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnNeg,
    DicksonWildAffine.trace_mul_affineGL] at htrNeg
  have hunit : Units.map M.subtype.toMonoidHom (1 : L).1 = (1 : (K p)ˣ) := by
    exact map_one (Units.map M.subtype.toMonoidHom)
  have hunitVal : (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) = 1 :=
    congrArg Units.val hunit
  rw [hunitVal, mul_one] at htrNeg
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 +
      S 1 0 * ((coord nNeg).1 : K p) + S 1 1 = -2 at htrNeg
  let xNeg : M := (coord nNeg).1
  have hgammaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 * (xNeg : K p) = -4 := by
    dsimp [xNeg]
    linear_combination htrNeg - htraceEntries
  have hxNeg : (xNeg : K p) ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hgammaMul
    exact hfour (by simpa using hgammaMul.symm)
  have hgammaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 =
      (-4 : K p) / (xNeg : K p) := (eq_div_iff hxNeg).2 hgammaMul
  have hgamma : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ∈ M := by
    rw [hgammaEq]
    exact M.div_mem (M.neg_mem (natCast_mem M 4)) xNeg.2
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨eta, heta0, heta1, hetaNeg1⟩ :
      ∃ eta : M, eta ≠ 0 ∧ eta ≠ 1 ∧ eta ≠ -1 := by
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset M) ⊆ {0, 1, -1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      by_cases hx1 : x = 1
      · exact Or.inr (Or.inl hx1)
      · exact Or.inr (Or.inr (hnone x hx0 hx1))
    have hsmall : Fintype.card M ≤ 3 := by
      calc
        Fintype.card M = (Finset.univ : Finset M).card := by simp
        _ ≤ ({0, 1, -1} : Finset M).card := Finset.card_le_card hsubset
        _ ≤ 3 := Finset.card_le_three
    rw [← Nat.card_eq_fintype_card, hMcard] at hsmall
    omega
  let etaU : Mˣ := Units.mk0 eta heta0
  have hetaSqMem : etaU ^ 2 ∈ L := by
    rw [hLsquare]
    exact ⟨etaU, rfl⟩
  let lEta : L := ⟨etaU ^ 2, hetaSqMem⟩
  have hetaRoot : (2 * (eta : K p)) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom lEta.1 : K p) := by
    rw [hdet]
    simp [lEta, etaU]
    ring
  obtain ⟨nEta, -, hnEta, htrEta⟩ := findTrace lEta (2 * (eta : K p)) hetaRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnEta,
    DicksonWildAffine.trace_mul_affineGL] at htrEta
  have hetaUnitVal :
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) = (eta : K p) ^ 2 := by
    rfl
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 *
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) +
      S 1 0 * ((coord nEta).1 : K p) + S 1 1 = 2 * (eta : K p) at htrEta
  rw [hetaUnitVal] at htrEta
  let gammaM : M := ⟨(S : Matrix (Fin 2) (Fin 2) (K p)) 1 0, hgamma⟩
  let denom : M := eta ^ 2 - 1
  let numer : M := 2 * eta - 2 - gammaM * (coord nEta).1
  have hdenom : (denom : K p) ≠ 0 := by
    intro hzero
    have hetaSq : eta ^ 2 = 1 := by
      apply Subtype.ext
      exact sub_eq_zero.mp hzero
    rcases sq_eq_one_iff.mp hetaSq with h | h
    · exact heta1 h
    · exact hetaNeg1 h
  have halphaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * (denom : K p) =
      (numer : K p) := by
    dsimp [denom, numer, gammaM]
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * ((eta : K p) ^ 2 - 1) =
          (S 0 0 * (eta : K p) ^ 2 + S 1 0 * ((coord nEta).1 : K p) + S 1 1) -
            (S 0 0 + S 1 1) - S 1 0 * ((coord nEta).1 : K p) := by ring
      _ = 2 * (eta : K p) - 2 - S 1 0 * ((coord nEta).1 : K p) := by
        rw [htrEta, htraceEntries]
  have halphaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 =
      (numer : K p) / (denom : K p) := (eq_div_iff hdenom).2 halphaMul
  have halpha : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 ∈ M := by
    rw [halphaEq]
    exact (numer / denom).2
  have hdeltaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 =
      2 - S 0 0 := by linear_combination htraceEntries
  have hdelta : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 ∈ M := by
    rw [hdeltaEq]
    exact M.sub_mem (natCast_mem M 2) halpha
  have hdetEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * S 1 1 -
      S 0 1 * S 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hbetaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
      S 0 0 * S 1 1 - 1 := by
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
          S 0 0 * S 1 1 - (S 0 0 * S 1 1 - S 0 1 * S 1 0) := by ring
      _ = S 0 0 * S 1 1 - 1 := by rw [hdetEntries]
  have hbetaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 =
      (S 0 0 * S 1 1 - 1) / S 1 0 := (eq_div_iff hS10).2 hbetaMul
  have hbeta : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 ∈ M := by
    rw [hbetaEq]
    exact M.div_mem (M.sub_mem (M.mul_mem halpha hdelta) (M.one_mem)) hgamma
  intro i k
  fin_cases i <;> fin_cases k
  · exact halpha
  · exact hbeta
  · exact hgamma
  · exact hdelta

set_option maxHeartbeats 800000 in
-- The containment proof instantiates the trace-fiber lemma twice in dependent subtypes.
private lemma dicksonWild_range_le_embedded_psl_of_half
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) :
    j.range ≤ ((Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL).range := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range :=
    DicksonWildAffine.subgroup_eq_square_range_of_card L (p ^ m) t hMcard hLcard hhalf
  have hNmem (n : N) : j n.1 ∈ pslEmbed.range := by
    have hl : (coord n).2.1 ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range := by
      rw [← hLsquare]
      exact (coord n).2.2
    obtain ⟨v, hv⟩ := hl
    have hv' : v ^ 2 = (coord n).2.1 := by simpa using hv
    have hdetAff : v ^ 2 = Matrix.GeneralLinearGroup.det
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) := by
      rw [hv']
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      simp [DicksonWildAffine.affineGL, Matrix.det_fin_two]
    obtain ⟨z, hz⟩ := dicksonWild_exists_psl_preimage_of_det_square
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) v hdetAff
    refine ⟨z, ?_⟩
    change Matrix.ProjGenLinGroup.map M.subtype
      (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = j n.1
    rw [hz, hnormal n]
  rintro y ⟨g, rfl⟩
  by_cases hg : g ∈ N
  · exact hNmem ⟨g, hg⟩
  · have hfiber : Nat.card {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} = 2 :=
      dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
        hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
          g hg 1
    have hnonempty : Nonempty {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} :=
      (Nat.card_pos_iff.mp (by rw [hfiber]; omega)).1
    obtain ⟨w⟩ := hnonempty
    let n : N := w.1.1
    let z : G := g * (n.1 : G)
    have hzpow : z ^ p = 1 := w.1.2
    have hzOut : z ∉ N := by
      intro hzN
      apply hg
      have hgeq : g = z * (n.1 : G)⁻¹ := by dsimp [z]; group
      rw [hgeq]
      exact N.mul_mem hzN (N.inv_mem n.2)
    have hzNe : z ≠ 1 := by
      intro hz
      apply hzOut
      rw [hz]
      exact N.one_mem
    have hzOrder : orderOf z = p := orderOf_eq_prime hzpow hzNe
    obtain ⟨S₀, hS₀, hS₀10⟩ := hout z hzOut
    have hS₀Order : orderOf (Matrix.ProjGenLinGroup.mk S₀) = p := by
      rw [hS₀]
      exact (orderOf_injective j hj z).trans hzOrder
    obtain ⟨S, hSmk, hStrace, hSdet, hS10⟩ :=
      dicksonWild_exists_normalized_lift_of_orderOf_eq_char S₀ hS₀Order hS₀10
    have hSj : Matrix.ProjGenLinGroup.mk S = j z := hSmk.trans hS₀
    have hentries := dicksonWild_normalized_order_char_lift_entries_mem
      G hpG P m f t htp hPcard hNcard hindex hcount hhalf M hMcard L hLcard
      hLsquare j hj coord hcoord hnormal hout hq z hzOut S hSj hStrace hSdet hS10
    obtain ⟨s, hs⟩ :=
      dicksonWild_exists_embedded_psl_preimage_of_entries_mem M S hentries hSdet
    have hzMem : j z ∈ pslEmbed.range := by
      refine ⟨s, ?_⟩
      exact hs.trans hSj
    have hnMem : j n.1 ∈ pslEmbed.range := hNmem n
    have hjg : j g = j z * (j n.1)⁻¹ := by
      dsimp [z]
      rw [map_mul]
      group
    rw [hjg]
    exact pslEmbed.range.mul_mem hzMem (pslEmbed.range.inv_mem hnMem)

private lemma dicksonWild_psl_case_of_half_gt_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hm : 1 ≤ m) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1) (hq : 3 < p ^ m) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hpslInjective : Function.Injective pslEmbed :=
    (projGenLinGroup_map_injective M.subtype M.subtype_injective).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let J : Subgroup (PGL p) := j.range
  let H : Subgroup (PGL p) := pslEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j.rangeRestrict
    j.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  have hHfinite : Finite H := Finite.of_surjective pslEmbed.rangeRestrict
    pslEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hle : J ≤ H :=
    dicksonWild_range_le_embedded_psl_of_half G hpG P m f t htp hPcard hNcard
      hindex hcount hhalf M hMcard L hLcard j hj coord hcoord hnormal hout hq
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  have hqeq : p ^ m = 2 * t + 1 := by omega
  have hquad : (p ^ m) ^ 2 - 1 = 2 * (t * (p ^ m + 1)) := by
    rw [hqeq]
    have hring : (2 * t + 1) ^ 2 = 2 * (t * (2 * t + 1 + 1)) + 1 := by ring
    omega
  have hHcard : Nat.card H = p ^ m * t * (p ^ m + 1) := by
    calc
      Nat.card H = Nat.card
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpslInjective).symm.toEquiv
      _ = Nat.card M * (Nat.card M ^ 2 - 1) / 2 := by
        rw [card_projectiveSpecialLinearGroup_fin_two p M hp2,
          Nat.card_eq_fintype_card]
      _ = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by rw [hMcard]
      _ = p ^ m * t * (p ^ m + 1) := by
        rw [hquad]
        rw [show p ^ m * (2 * (t * (p ^ m + 1))) =
          2 * (p ^ m * t * (p ^ m + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by omega)
  have hGcard : Nat.card G = p ^ m * t * (1 + f * p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + f * p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hcardLe : Nat.card J ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  rw [hJcard, hHcard] at hcardLe
  have hfactorPos : 0 < p ^ m * t := by
    have ht : 0 < t := by
      have hpPow : 3 < p ^ m := hq
      omega
    exact mul_pos (pow_pos (Fact.out : p.Prime).pos m) ht
  have honeLe : 1 + f * p ^ m ≤ p ^ m + 1 := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ m * t)
    · simpa [mul_assoc] using hcardLe
    · exact hfactorPos
  have hfmul : f * p ^ m ≤ 1 * p ^ m := by omega
  have hfle : f ≤ 1 := Nat.le_of_mul_le_mul_right hfmul (pow_pos (Fact.out : p.Prime).pos m)
  have hf1 : f = 1 := by omega
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hf1]
    ring
  let incl : J →* H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj
  let eH : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpslInjective
  let eJH : J ≃* H :=
    MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

private lemma dicksonWild_pgl_case_of_full
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hfull : t = p ^ m - 1) :
    Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := by omega
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j'.rangeRestrict
    j'.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  let _ : Finite (Matrix.ProjGenLinGroup (Fin 2) M) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hHfinite : Finite H := Finite.of_surjective pglEmbed.rangeRestrict
    pglEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hHcard : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) := by
    calc
      Nat.card H = Nat.card (Matrix.ProjGenLinGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpglInjective).symm.toEquiv
      _ = Fintype.card M * (Fintype.card M ^ 2 - 1) :=
        card_projGenLinGroup_fin_two M
      _ = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [← Nat.card_eq_fintype_card, hMcard]
  have hGcard : Nat.card G = p ^ m * t * (1 + p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj').toEquiv).symm
  have hqone : 1 ≤ p ^ m := one_le_pow₀ (Fact.out : p.Prime).one_lt.le
  have hfactor : (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
    have hqeq : p ^ m = (p ^ m - 1) + 1 := by omega
    rw [Nat.sub_eq_iff_eq_add (one_le_pow₀ hqone)]
    nlinarith
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hfull, hfactor]
    ring
  let incl : J → H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let eJH : J ≃* H := MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjGenLinGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans (dicksonWild_projGenLinGroup_congr eField.toRingEquiv)⟩

private lemma dicksonWild_psl_case_of_half_eq_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hhalf : 2 * t = p ^ m - 1) (hq3 : p ^ m = 3) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let incl : J →* H := Subgroup.inclusion hle
  let toPGL : J →* Matrix.ProjGenLinGroup (Fin 2) M :=
    eH.symm.toMonoidHom.comp incl
  have htoPGL : Function.Injective toPGL :=
    eH.symm.injective.comp (Subgroup.inclusion_injective hle)
  have ht1 : t = 1 := by omega
  have hGcard : Nat.card G = 12 := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex, hq3, ht1] at hprod
    norm_num at hprod ⊢
    exact hprod.symm
  have hJfinite : Finite J := Finite.of_surjective eJ eJ.surjective
  let _ : Finite J := hJfinite
  have hJcard : Nat.card J = 12 := by
    rw [← hGcard]
    exact (Nat.card_congr eJ.toEquiv).symm
  let X := Projectivization M (Fin 2 → M)
  let _ : Fintype X := Fintype.ofEquiv (OnePoint M)
    (OnePoint.equivProjectivization M)
  have hMcard3 : Nat.card M = 3 := hMcard.trans hq3
  have hOneCard : Fintype.card (OnePoint M) = 4 := by
    change Fintype.card (Option M) = 4
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, hMcard3]
  have hXcard : Fintype.card X = 4 := by
    calc
      Fintype.card X = Fintype.card (OnePoint M) :=
        (Fintype.card_congr (OnePoint.equivProjectivization M)).symm
      _ = 4 := hOneCard
  let eFin : X ≃ Fin 4 := (Fintype.equivFin X).trans (finCongr hXcard)
  let pglAct : Matrix.ProjGenLinGroup (Fin 2) M →* Equiv.Perm (Fin 4) :=
    eFin.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (Matrix.ProjGenLinGroup (Fin 2) M) X)
  have hpglAct : Function.Injective pglAct := eFin.permCongrHom.injective.comp
    dicksonWild_pgl_toPermHom_injective
  let act : J →* Equiv.Perm (Fin 4) := pglAct.comp toPGL
  have hact : Function.Injective act := hpglAct.comp htoPGL
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hactIndex : act.range.index = 2 :=
    dicksonWild_perm_range_index_eq_two_of_card act hact 12 hJcard (by omega)
  obtain ⟨eJAlt⟩ :=
    dicksonWild_mulEquiv_alternating_of_perm_index_two act hact hactIndex
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  obtain ⟨ePSLAlt⟩ :=
    dicksonWild_psl_card_three_equiv_alternating_four p M hp2 hMcard3
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJAlt.trans ePSLAlt.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

private lemma dicksonWild_card_order_char_elements
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (P : Sylow p G) :
    Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      Nat.card (Sylow p G) * (Nat.card (P : Subgroup G) - 1) := by
  classical
  let D := Σ Q : Sylow p G, {g : (Q : Subgroup G) // g ≠ 1}
  let E := {g : G // g ≠ 1 ∧ g ^ p = 1}
  let toE : D → E := fun d ↦ ⟨d.2.1.1, ⟨by
    intro h
    apply d.2.2
    apply Subtype.ext
    exact h, by
    apply G.subtype_injective
    change (d.2.1.1 : PGL p) ^ p = 1
    exact (orderOf_eq_prime_iff.mp
      (dicksonWild_orderOf_coe_eq_char_of_isPGroup_in_subgroup G
        d.1.isPGroup' d.2.1 d.2.2)).1⟩⟩
  have htoEInjective : Function.Injective toE := by
    rintro ⟨Q, g⟩ ⟨R, h⟩ hde
    have hval : g.1.1 = h.1.1 := congrArg (fun z : E ↦ z.1) hde
    have hQ : Q = R := by
      by_contra hQ
      have hmem : g.1.1 ∈ (Q : Subgroup G) ⊓ (R : Subgroup G) := by
        constructor
        · exact g.1.2
        · rw [hval]
          exact h.1.2
      rw [dicksonWild_distinct_sylow_inf_eq_bot G Q R hQ] at hmem
      apply g.2
      apply Subtype.ext
      exact hmem
    subst R
    have hgh : g = h := by
      apply Subtype.ext
      apply Subtype.ext
      exact hval
    subst h
    rfl
  have htoESurjective : Function.Surjective toE := by
    intro g
    obtain ⟨Q, hQ⟩ := dicksonWild_exists_sylow_mem_of_pow_char_eq_one g.1 g.2.2
    let gQ : Q := ⟨g.1, hQ⟩
    have hgQ : gQ ≠ 1 := by
      intro h
      apply g.2.1
      exact congrArg Subtype.val h
    refine ⟨⟨Q, ⟨gQ, hgQ⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hcardD : Nat.card D =
      Nat.card (Sylow p G) * (Nat.card (P : Subgroup G) - 1) := by
    let _ : Fintype (Sylow p G) := Fintype.ofFinite (Sylow p G)
    change Nat.card (Σ Q : Sylow p G, {g : (Q : Subgroup G) // g ≠ 1}) =
      Nat.card (Sylow p G) * (Nat.card (P : Subgroup G) - 1)
    rw [Nat.card_sigma]
    have hfiber (Q : Sylow p G) :
        Nat.card {g : (Q : Subgroup G) // g ≠ 1} = Nat.card (Q : Subgroup G) - 1 := by
      let _ : Fintype (Q : Subgroup G) := Fintype.ofFinite (Q : Subgroup G)
      let _ : Fintype {g : (Q : Subgroup G) // g ≠ 1} :=
        Fintype.ofFinite {g : (Q : Subgroup G) // g ≠ 1}
      rw [Nat.card_eq_fintype_card]
      calc
        Fintype.card {g : (Q : Subgroup G) // g ≠ 1} =
            Fintype.card (Q : Subgroup G) - 1 :=
          Fintype.card_subtype_compl (fun g : (Q : Subgroup G) ↦ g = 1) |>.trans
            (by simp)
        _ = Nat.card (Q : Subgroup G) - 1 := by rw [Nat.card_eq_fintype_card]
    have hQcard (Q : Sylow p G) :
        Nat.card (Q : Subgroup G) = Nat.card (P : Subgroup G) := by
      rw [Q.card_eq_multiplicity, P.card_eq_multiplicity]
    simp_rw [hfiber, hQcard]
    simp [Nat.card_eq_fintype_card]
  rw [← hcardD]
  exact (Nat.card_congr (Equiv.ofBijective toE ⟨htoEInjective, htoESurjective⟩)).symm

private lemma dicksonWild_order_char_count
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G)
    (P : Sylow p G) (hPnormal : ¬(P : Subgroup G).Normal) :
    ∃ m f : ℕ, 1 ≤ m ∧ Nat.card (P : Subgroup G) = p ^ m ∧ 0 < f ∧
      Nat.card (Sylow p G) = 1 + f * p ^ m ∧
      Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
        (1 + f * p ^ m) * (p ^ m - 1) := by
  let m := (Nat.card G).factorization p
  have hm : 1 ≤ m :=
    (Fact.out : p.Prime).dvd_iff_one_le_factorization (Nat.card_pos.ne') |>.mp hpG
  have hPcard : Nat.card (P : Subgroup G) = p ^ m := P.card_eq_multiplicity
  obtain ⟨f, hf⟩ := dicksonWild_card_sylow_eq_one_add_mul_card G P
  have hfpos : 0 < f := by
    by_contra hfzero
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos hfzero
    have hSylowCard : Nat.card (Sylow p G) = 1 := by simpa [hf0] using hf
    let _ : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hSylowCard).1
    let _ : (P : Subgroup G).Characteristic := Sylow.characteristic_of_subsingleton P
    exact hPnormal inferInstance
  have hf' : Nat.card (Sylow p G) = 1 + f * p ^ m := by
    rwa [hPcard] at hf
  refine ⟨m, f, hm, hPcard, hfpos, hf', ?_⟩
  rw [dicksonWild_card_order_char_elements G P, hf, hPcard]

variable (p : ℕ) [Fact (Nat.Prime p)]

variable [Fact (2 < p)]

/-- **Dickson's classification, wild case.** Let $p$ be an odd prime, let $K$ be an algebraic
closure of $\mathbb{F}_p$, and let $G$ be a finite subgroup of $\mathrm{PGL}_2(K)$ whose order
is divisible by $p$. Then at least one of the following holds. (a) There are natural numbers
$m \ge 1$ and $t$ with $t$ coprime to $p$ and $t \mid p^m - 1$, and an injective homomorphism
$\varphi$ from the cyclic group $\mathbb{Z}/t\mathbb{Z}$ to the automorphism group of the
additive group $\mathbb{F}_p^m$ such that $\varphi(c)$ fixes no nonzero vector of
$\mathbb{F}_p^m$ for every $c \ne 0$, and $G$ is isomorphic to the semidirect product
$\mathbb{F}_p^m \rtimes_\varphi \mathbb{Z}/t\mathbb{Z}$. (b) $G$ is isomorphic to
$\mathrm{PSL}_2(\mathbb{F}_{p^m})$ for some $m \ge 1$, where $\mathbb{F}_{p^m}$ is the field
with $p^m$ elements. (c) $G$ is isomorphic to $\mathrm{PGL}_2(\mathbb{F}_{p^m})$ for some
$m \ge 1$. (d) $p = 3$ and $G$ is isomorphic to the alternating group $A_5$.

In the source, the first case is a group of maps $z \mapsto az + b$ with $a$ a root of unity;
only the resulting abstract group structure is recorded here.

Proof: We follow X. Faber, *Finite p-irregular subgroups of $\mathrm{PGL}_2(k)$*,
arXiv:1112.1999, §6, using the Sylow normal form, exceptional-orbit count, and projective-line
actions to identify the $\mathrm{PSL}_2$, $\mathrm{PGL}_2$, and $A_5$ cases.

Proves `Wanted` entry `classification_wild`.

Source: L. E. Dickson, *Linear Groups with an Exposition of the Galois Field
Theory*, Teubner (1901).
-/
theorem classification_wild (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  let P : Sylow p G := Classical.choice inferInstance
  by_cases hPnormal : (P : Subgroup G).Normal
  · exact Or.inl (dicksonWild_frobenius_case_of_normal_sylow G hG_p P hPnormal)
  · obtain ⟨m, f, hm, hPcard, hf, hSylowCard, hpCount⟩ :=
      dicksonWild_order_char_count G hG_p P hPnormal
    obtain ⟨mN, t, hmN, htp, htdiv, hPcardN, hNcard⟩ :=
      dicksonWild_normalizer_order_data G hG_p P
    have hmEq : mN = m := by
      apply (Nat.pow_right_inj (Fact.out : p.Prime).one_lt).mp
      exact hPcardN.symm.trans hPcard
    subst mN
    have hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m :=
      (P.card_eq_index_normalizer.symm.trans hSylowCard)
    have hsandwich : p ^ m - 1 ≤ 2 * t :=
      dicksonWild_sandwich_bound G hG_p P m f t hf htp hPcard hNcard
        hindex hpCount
    have hqpos : 0 < p ^ m - 1 := by
      have hpPow : 1 < p ^ m := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      omega
    have htpos : 0 < t := by
      by_contra ht
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
      rw [ht0, mul_zero] at hNcard
      exact Nat.card_pos.ne' hNcard
    have htCases : t = p ^ m - 1 ∨ 2 * t = p ^ m - 1 :=
      dicksonWild_eq_or_two_mul_eq_of_dvd_of_le (p ^ m - 1) t hqpos htpos
        htdiv hsandwich
    obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
      dicksonWild_exists_matrix_normal_form G hG_p P m t hm htp hNcard hsandwich
    let _ : Finite M := hMfinite
    obtain ⟨d, hd, hrelation, hstabilizerLarge, hstabilizerSmall,
      hstabilizers, hexceptionalOrbits⟩ :=
      dicksonWild_exceptional_orbit_data G P m f t hm hf hNcard hindex hpCount
        M L j hj coord hnormal hout
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      omega
    have hq3 : 3 ≤ p ^ m :=
      hp3.trans (Nat.le_pow (a := p) (b := m) hm)
    rcases htCases with hfull | hhalf
    · rcases dicksonWild_f_eq_one_or_exceptional_of_full_multiplier_relation
          (p ^ m) f t d hq3 hf hfull hrelation with hf1 | hexceptional
      · subst f
        have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
          simpa using hindex
        exact Or.inr (Or.inr (Or.inl ⟨m, hm,
          dicksonWild_pgl_case_of_full G hG_p P m t hm htp hNcard hindex1 hfull⟩))
      · obtain ⟨hqEq, hfEq⟩ := hexceptional
        subst f
        let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
          MulAction.compHom _ j
        have hpEq : p = 3 := by
          have hpLe : p ≤ p ^ m := Nat.le_pow hm
          omega
        have hdEq : d = 5 := by
          rw [hfull, hqEq] at hrelation
          norm_num at hrelation
          omega
        have hqt : p ^ m * t = 6 := by rw [hfull, hqEq]
        obtain ⟨x₆, hx₆⟩ := hstabilizerLarge
        obtain ⟨x₅, hx₅⟩ := hstabilizerSmall
        have hx₆' : Nat.card (MulAction.stabilizer G x₆) = 6 := hx₆.trans hqt
        have hx₅' : Nat.card (MulAction.stabilizer G x₅) = 5 := hx₅.trans hdEq
        have hall :
            ∀ x : dicksonWildExceptional G
                (Projectivization (K p) (Fin 2 → K p)),
              Nat.card (MulAction.stabilizer G x) = 6 ∨
              Nat.card (MulAction.stabilizer G x) = 5 := by
          intro x
          rcases hstabilizers x with h | h
          · exact Or.inl (h.trans hqt)
          · exact Or.inr (h.trans hdEq)
        have hGcard : Nat.card G = 60 := by
          have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
          rw [hNcard, hindex, hfull, hqEq] at hprod
          norm_num at hprod ⊢
          omega
        have hPcardThree : Nat.card (P : Subgroup G) = 3 := hPcard.trans hqEq
        exact Or.inr (Or.inr (Or.inr ⟨hpEq,
          dicksonWild_a5_case_of_exceptional G hpEq P hPnormal hPcardThree
            j hj hGcard x₆ x₅ hx₆' hx₅' hall hexceptionalOrbits⟩))
    · have hf1 := dicksonWild_f_eq_one_of_half_multiplier_relation
          (p ^ m) f t d hq3 hf hhalf hrelation
      subst f
      have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
        simpa using hindex
      by_cases hqgt : 3 < p ^ m
      · exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_gt_three G hG_p P m 1 t hm (by omega)
            htp hPcard hNcard (by simpa using hindex1) (by simpa using hpCount) hhalf hqgt⟩)
      · have hqEq : p ^ m = 3 := by omega
        exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_eq_three G hG_p P m t hm htp hNcard
            hindex1 hhalf hqEq⟩)

end Dickson

end

end MetaMathlibExt
