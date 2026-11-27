/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.ConnesTrace
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Data.Matrix.Basis
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.NormNum

/-!
# Integral matrix representatives in the Connes quotient

The coefficient algebra is the ring of two-by-two integer matrices, acting
on itself on both sides. An outer two-by-two matrix trace contracts the
closed path `0 → 1 → 0`, whose entries are the inner units `E₀₁` and `E₁₀`.
Its degree-one boundary is the nonzero inner commutator `E₀₀ - E₁₁`.

The projected representatives distinguish the cyclic minus sign, an
incorrect matrix-index contraction, and a missing coefficient action.
Degree-zero trace retains the integral factor two on the outer identity.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open ModuleCat.Algebra.Hochschild
open ModuleCat.Algebra.Hochschild.Matrix
open scoped BigOperators TensorProduct

namespace MathlibExtTest.Algebra.Homology.Hochschild.Matrix.ConnesTraceTests

private abbrev A := Matrix (Fin 2) (Fin 2) ℤ
private abbrev B := Matrix (Fin 2) (Fin 2) A
private abbrev x : A := Matrix.single 0 1 1
private abbrev y : A := Matrix.single 1 0 1
private abbrev diagonalDifference : A := Matrix.single 0 0 1 - Matrix.single 1 1 1
private abbrev outerX : B := Matrix.single 0 1 x
private abbrev outerY : B := Matrix.single 1 0 y
private abbrev wrongOuterY : B := Matrix.single 0 1 y

private abbrev word0 (C : Type) [AddCommGroup C] [Module ℤ C] (a : C) :
    C ⊗[ℤ] TensorPower ℤ 0 C :=
  a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun i : Fin 0 => Fin.elim0 i)

private abbrev word1 (C : Type) [AddCommGroup C] [Module ℤ C] (a b : C) :
    C ⊗[ℤ] TensorPower ℤ 1 C :=
  a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (fun _ : Fin 1 => b)

private def zeroEval (C : Type) [AddCommGroup C] [Module ℤ C] :
    C ⊗[ℤ] TensorPower ℤ 0 C →ₗ[ℤ] C :=
  (TensorProduct.rid ℤ C).toLinearMap.comp
    (TensorProduct.map LinearMap.id (TensorPower.zeroEquiv ℤ C).toLinearMap)

@[simp]
private lemma zeroEval_word0 (C : Type) [AddCommGroup C] [Module ℤ C] (a : C) :
    zeroEval C (word0 C a) = a := by
  simp only [zeroEval, word0, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorPower.zeroEquiv,
    PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

private lemma word1_zero_right (C : Type) [AddCommGroup C] [Module ℤ C] (a : C) :
    word1 C a 0 = 0 := by
  change a ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ (0 : Fin 1 → C) = 0
  rw [(PiTensorProduct.tprod ℤ).map_zero, TensorProduct.tmul_zero]

private lemma xy : x * y = Matrix.single 0 0 (1 : ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

private lemma yx : y * x = Matrix.single 1 1 (1 : ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

private lemma commutator_value : x * y - y * x = diagonalDifference := by
  rw [xy, yx]

private lemma diagonal_entry : diagonalDifference 0 0 = 1 := by
  norm_num [diagonalDifference, Matrix.single_apply]

private lemma diagonal_ne_zero : diagonalDifference ≠ 0 := by
  intro h
  have h0 := congrArg (fun a : A => a 0 0) h
  rw [diagonal_entry] at h0
  norm_num at h0

private lemma projection_zero_injective (C : Type) [Ring C] [Algebra ℤ C] :
    Function.Injective (connesProjection ℤ C 0).hom := by
  let f : chainLevel ℤ C C 0 ⟶ chainLevel ℤ C C 0 :=
    ((NonUnital.cyclicBicomplex ℤ C).d 1 0).f 0
  let E := NonUnital.connesComplexXIsoRangeQuotient ℤ C 0
  have hf : f.hom = 0 := by
    exact (NonUnital.connesComplex_levelMap ℤ C 0).trans
      (by rw [TensorPower.consCyclicOperator_zero, sub_self])
  have hr : f.hom.range = ⊥ := by rw [hf, LinearMap.range_zero]
  have hk : LinearMap.ker f.hom.range.mkQ = ⊥ :=
    (Submodule.ker_mkQ f.hom.range).trans hr
  have hi : Function.Injective f.hom.range.mkQ := LinearMap.ker_eq_bot.mp hk
  have hπ : connesProjection ℤ C 0 ≫ E.hom = ModuleCat.ofHom f.hom.range.mkQ :=
    NonUnital.connesComplex_X_isoRangeQuotient_π ℤ C 0
  intro a b hab
  apply hi
  have ha := congrArg (fun g => g.hom a) hπ
  have hb := congrArg (fun g => g.hom b) hπ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at ha hb
  exact ha.symm.trans ((congrArg E.hom.hom hab).trans hb)

private lemma representative_zero_ne_zero (a : A) (ha : a ≠ 0) :
    connesRepresentative ℤ A 0 (word0 A a) ≠ 0 := by
  intro h
  have hw : word0 A a = 0 :=
    projection_zero_injective A (h.trans (connesProjection ℤ A 0).hom.map_zero.symm)
  have hz := congrArg (zeroEval A) hw
  have hz' : a = 0 := by simpa only [zeroEval_word0, map_zero] using hz
  exact ha hz'

private lemma first_face_pair (C : Type) [Ring C] [Algebra ℤ C] (a b : C) :
    (NonUnital.regularFace ℤ C 0 0).hom (word1 C a b) = word0 C (a * b) := by
  have he : hochschildDropFirst (fun _ : Fin 1 => b) =
      (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  simpa only [word1, word0, he] using
    NonUnital.regularFace_first_tprod ℤ C 0 a (fun _ : Fin 1 => b)

private lemma last_face_pair (C : Type) [Ring C] [Algebra ℤ C] (a b : C) :
    (NonUnital.regularFace ℤ C 0 (1 : Fin 2)).hom (word1 C a b) =
      word0 C (b * a) := by
  have he : hochschildDropLast (fun _ : Fin 1 => b) =
      (fun i : Fin 0 => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  simpa only [word1, word0, he] using
    NonUnital.regularFace_last_tprod ℤ C 0 a (fun _ : Fin 1 => b)

private lemma boundary_pair (C : Type) [Ring C] [Algebra ℤ C] (a b : C) :
    ((NonUnital.bComplex ℤ C).d 1 0).hom (word1 C a b) = word0 C (a * b - b * a) := by
  have h := congrArg (fun f => f.hom (word1 C a b)) (NonUnital.bComplex_d ℤ C 0)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, Fin.sum_univ_two] at h
  have hs : ((NonUnital.bComplex ℤ C).d 1 0).hom (word1 C a b) =
      word0 C (a * b) - word0 C (b * a) := by
    simpa only [first_face_pair, last_face_pair, pow_zero, pow_one,
      one_smul, neg_one_smul, sub_eq_add_neg] using h
  exact hs.trans (TensorProduct.sub_tmul (a * b) (b * a) _).symm

private lemma projected_boundary_pair (C : Type) [Ring C] [Algebra ℤ C] (a b : C) :
    ((NonUnital.connesComplex ℤ C).d 1 0).hom
        (connesRepresentative ℤ C 1 (word1 C a b)) =
      connesRepresentative ℤ C 0 (word0 C (a * b - b * a)) := by
  have h := congrArg (fun f => f.hom (word1 C a b)) (connesProjection_boundary ℤ C 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (congrArg (connesRepresentative ℤ C 0) (boundary_pair C a b))

private lemma projected_xy_boundary :
    ((NonUnital.connesComplex ℤ A).d 1 0).hom
        (connesRepresentative ℤ A 1 (word1 A x y)) =
      connesRepresentative ℤ A 0 (word0 A diagonalDifference) := by
  simpa only [commutator_value] using projected_boundary_pair A x y

private lemma projected_xy_ne_zero : connesRepresentative ℤ A 1 (word1 A x y) ≠ 0 := by
  intro h
  have hd := congrArg ((NonUnital.connesComplex ℤ A).d 1 0).hom h
  rw [projected_xy_boundary, map_zero] at hd
  exact representative_zero_ne_zero diagonalDifference diagonal_ne_zero hd

private lemma cyclic_xy_sign :
    connesRepresentative ℤ A 1 (word1 A x y) =
      -connesRepresentative ℤ A 1 (word1 A y x) := by
  have h := connesRepresentative_cyclic ℤ A 1 (word1 A x y)
  rw [NonUnital.consCyclic_pair_value] at h
  simpa only [map_neg] using h.symm

private lemma cyclic_xy_ne_reverse :
    connesRepresentative ℤ A 1 (word1 A x y) ≠
      connesRepresentative ℤ A 1 (word1 A y x) := by
  intro h
  have hz : connesRepresentative ℤ A 1 (word1 A x y) =
      -connesRepresentative ℤ A 1 (word1 A x y) := cyclic_xy_sign.trans (congrArg Neg.neg h.symm)
  have hd := congrArg ((NonUnital.connesComplex ℤ A).d 1 0).hom hz
  rw [map_neg, projected_xy_boundary, ← map_neg] at hd
  have hw := projection_zero_injective A hd
  have he := congrArg (fun z => zeroEval A z 0 0) hw
  simp only [zeroEval_word0, map_neg, Matrix.neg_apply, diagonal_entry] at he
  norm_num at he

private lemma trace_outer_pair (Q : B) :
    generalizedTrace ℤ (Fin 2) 1 (word1 B outerX Q) = word1 A x (Q 1 0) := by
  classical
  rw [generalizedTrace_tmul_tprod]
  let cycle : Fin 2 → Fin 2 := id
  let term (γ : Fin 2 → Fin 2) :=
    outerX (γ 0) (γ 1) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ
      (fun j : Fin 1 => Q (γ j.succ) (γ (j.succ + 1)))
  change (∑ γ, term γ) = _
  calc
    (∑ γ, term γ) = term cycle := by
      apply Finset.sum_eq_single cycle
      · intro γ _ hneq
        by_cases h0 : γ 0 = 0
        · by_cases h1 : γ 1 = 1
          · exfalso
            apply hneq
            funext i
            fin_cases i <;> simp only [cycle, id_eq]
            · exact h0
            · exact h1
          · simp [term, outerX, Matrix.single_apply, h0, h1]
        · simp [term, outerX, Matrix.single_apply, h0]
      · simp
    _ = word1 A x (Q 1 0) := by
      have ht : (fun j : Fin 1 => Q (cycle j.succ) (cycle (j.succ + 1))) =
          (fun _ : Fin 1 => Q 1 0) := by
        funext j
        fin_cases j
        rfl
      dsimp only [term]
      rw [ht]
      simp [cycle, outerX, Matrix.single_apply, word1]

private lemma trace_outer_xy :
    generalizedTrace ℤ (Fin 2) 1 (word1 B outerX outerY) = word1 A x y := by
  simpa [outerY, Matrix.single_apply] using trace_outer_pair outerY

private lemma trace_wrong_indices :
    generalizedTrace ℤ (Fin 2) 1 (word1 B outerX wrongOuterY) = 0 := by
  simpa [wrongOuterY, Matrix.single_apply, word1_zero_right] using
    trace_outer_pair wrongOuterY

private lemma traced_projected_xy :
    ((connesTrace ℤ A 2).f 1).hom
        ((connesProjection ℤ B 1).hom (word1 B outerX outerY)) =
      connesRepresentative ℤ A 1 (word1 A x y) := by
  rw [connesTrace_f]
  have h := congrArg (fun f => f.hom (word1 B outerX outerY))
    (connesProjection_traceComponent ℤ A 2 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (congrArg (connesRepresentative ℤ A 1) trace_outer_xy)

private lemma traced_boundary_xy :
    ((connesTrace ℤ A 2).f 0).hom
        (((NonUnital.connesComplex ℤ B).d 1 0).hom
          ((connesProjection ℤ B 1).hom (word1 B outerX outerY))) =
      connesRepresentative ℤ A 0 (word0 A diagonalDifference) := by
  have h := congrArg
    (fun f => f.hom ((connesProjection ℤ B 1).hom (word1 B outerX outerY)))
    ((connesTrace ℤ A 2).comm 1 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [traced_projected_xy] at h
  exact h.symm.trans projected_xy_boundary

private lemma trace_identity_zero :
    generalizedTrace ℤ (Fin 2) 0 (word0 B 1) = word0 A ((2 : ℤ) • (1 : A)) := by
  classical
  rw [generalizedTrace_tmul_tprod]
  have hterm (γ : Fin 1 → Fin 2) :
      (1 : B) (γ 0) (γ 1) ⊗ₜ[ℤ] PiTensorProduct.tprod ℤ
        (fun j : Fin 0 => (Fin.elim0 j : B) (γ j.succ) (γ (j.succ + 1))) =
        word0 A 1 := by
    have hi : (1 : Fin 1) = 0 := Subsingleton.elim _ _
    have he : (fun j : Fin 0 => (Fin.elim0 j : B) (γ j.succ) (γ (j.succ + 1))) =
        (fun j : Fin 0 => (Fin.elim0 j : A)) := by
      funext j
      exact Fin.elim0 j
    rw [hi, he]
    simp [Matrix.one_apply, word0]
  simp_rw [hterm]
  simp [Finset.sum_const, Fintype.card_fun, word0, two_smul, TensorProduct.add_tmul]

private lemma traced_identity_zero :
    ((connesTrace ℤ A 2).f 0).hom ((connesProjection ℤ B 0).hom (word0 B 1)) =
      connesRepresentative ℤ A 0 (word0 A ((2 : ℤ) • (1 : A))) := by
  rw [connesTrace_f]
  have h := congrArg (fun f => f.hom (word0 B 1)) (connesProjection_traceComponent ℤ A 2 0)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (congrArg (connesRepresentative ℤ A 0) trace_identity_zero)

example : zeroEval A ((NonUnital.regularFace ℤ A 0 0).hom (word1 A x y)) 0 0 = 1 := by
  rw [first_face_pair, zeroEval_word0, xy]
  norm_num [Matrix.single_apply]

example : zeroEval A ((NonUnital.regularFace ℤ A 0 (1 : Fin 2)).hom (word1 A x y)) 1 1 = 1 := by
  rw [last_face_pair, zeroEval_word0, yx]
  norm_num [Matrix.single_apply]

example : connesRepresentative ℤ A 0 (word0 A diagonalDifference) ≠ 0 :=
  representative_zero_ne_zero diagonalDifference diagonal_ne_zero

example : connesRepresentative ℤ A 1 (word1 A x y) ≠ 0 := projected_xy_ne_zero

example : connesRepresentative ℤ A 1 (word1 A x y) =
    -connesRepresentative ℤ A 1 (word1 A y x) := cyclic_xy_sign

example : connesRepresentative ℤ A 1 (word1 A x y) ≠
    connesRepresentative ℤ A 1 (word1 A y x) := cyclic_xy_ne_reverse

example : generalizedTrace ℤ (Fin 2) 1 (word1 B outerX outerY) = word1 A x y :=
  trace_outer_xy

example : generalizedTrace ℤ (Fin 2) 1 (word1 B outerX wrongOuterY) = 0 := trace_wrong_indices

example : ((connesTrace ℤ A 2).f 1).hom
    ((connesProjection ℤ B 1).hom (word1 B outerX outerY)) =
      connesRepresentative ℤ A 1 (word1 A x y) := traced_projected_xy

example : (connesProjection ℤ B 1).hom (word1 B outerX outerY) ≠ 0 := by
  intro h
  have ht := congrArg ((connesTrace ℤ A 2).f 1).hom h
  rw [traced_projected_xy, map_zero] at ht
  exact projected_xy_ne_zero ht

example : ((connesTrace ℤ A 2).f 0).hom
    (((NonUnital.connesComplex ℤ B).d 1 0).hom
      ((connesProjection ℤ B 1).hom (word1 B outerX outerY))) =
      connesRepresentative ℤ A 0 (word0 A diagonalDifference) := traced_boundary_xy

example : ((connesTrace ℤ A 2).f 0).hom ((connesProjection ℤ B 0).hom (word0 B 1)) =
    connesRepresentative ℤ A 0 (word0 A ((2 : ℤ) • (1 : A))) := traced_identity_zero

example : ((connesTrace ℤ A 2).f 0).hom ((connesProjection ℤ B 0).hom (word0 B 1)) ≠
    connesRepresentative ℤ A 0 (word0 A (1 : A)) := by
  rw [traced_identity_zero]
  intro h
  have hw := projection_zero_injective A h
  have he := congrArg (fun z => zeroEval A z 0 0) hw
  simp only [zeroEval_word0] at he
  norm_num [Matrix.smul_apply, Matrix.one_apply] at he

end MathlibExtTest.Algebra.Homology.Hochschild.Matrix.ConnesTraceTests
