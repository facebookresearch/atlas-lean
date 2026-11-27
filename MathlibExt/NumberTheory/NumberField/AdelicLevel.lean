/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`P2M/Sol/S_NumberField_AdelicLevel_exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat.lean`,
`Definitions/Def_NumberField_AdelicLevel.lean`
and
`Definitions/Def_AutomorphicForm_SmoothAutomorphicFnAt.lean`
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

public import MathlibExt.NumberTheory.NumberField.AdelicBox
public import MathlibExt.NumberTheory.NumberField.HeckeCharacter

@[expose] public section

/-!
# Level subgroups and Hecke generators of adelic `GL₂`

Let `R` be a Dedekind domain with fraction field `K`. This file defines

* `glArch` and `glFin`, the projections of `GL₂` over the adeles onto `GL₂` over the infinite
  and the finite adeles;
* `archComponent K w` and `finComponent R K v`, the components of `GL₂` over the infinite and
  the finite adeles at an infinite place `w` and at a finite place `v`;
* `finiteLevelOne R K N`, the level subgroup of `GL₂` over the finite adeles at an ideal `N`:
  the matrices `g` such that `g` and `g⁻¹` have integral entries, lower-left entry in `N` and
  lower-right entry congruent to `1` modulo `N` at every finite place;
* `levelOne R K N`, the adelic matrices whose finite part lies in `finiteLevelOne R K N`;
* `heckeGen R K v`, the Hecke generator at a finite place `v`: the matrix `diag(ϖ, 1)` at `v`,
  for the chosen uniformizer `ϖ` at `v`, and the identity at every other place;
* for a number field `F`, `AutomorphicForm.finiteAdelicGL2Subgroup F`, the adelic matrices whose
  infinite part is the identity.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Projections

/-- The projection of `GL₂` over the adeles onto `GL₂` over the infinite adeles. -/
def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

/-- The projection of `GL₂` over the adeles onto `GL₂` over the finite adeles. -/
def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 :=
  rfl

theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 :=
  rfl

/-- The component of an archimedean `GL(2)` element at one infinite place. -/
def archComponent (w : InfinitePlace K) :
    GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

/-- The component at a finite place `v` of `GL₂` over the finite adeles. -/
def finComponent (v : HeightOneSpectrum R) :
    GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (finAdeleEval R K v)

theorem archComponent_apply (w : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K))
    (i j : Fin 2) :
    (archComponent K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w :=
  rfl

theorem finComponent_apply (v : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K))
    (i j : Fin 2) :
    (finComponent R K v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v :=
  rfl

end Projections

section FiniteLevel

open scoped Classical in
/-- The local bound of an ideal `N` at a finite place `v`: `0` when `N = ⊥`, and `exp (-n)`
otherwise, where `n` is the multiplicity of `v` in the factorization of `N`. -/
def idealBound (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

/-- The finite adeles whose valuation at every finite place `v` is at most the local bound of
`N` at `v`. -/
def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ idealBound R N v}

variable {R K}

theorem one_mem_integralFiniteAdeles :
    (1 : FiniteAdeleRing R K) ∈ AdelicBox.integralFiniteAdeles R K :=
  fun _ => one_mem _

theorem zero_mem_integralFiniteAdeles :
    (0 : FiniteAdeleRing R K) ∈ AdelicBox.integralFiniteAdeles R K :=
  fun _ => zero_mem _

theorem add_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K}
    (hx : x ∈ AdelicBox.integralFiniteAdeles R K) (hy : y ∈ AdelicBox.integralFiniteAdeles R K) :
    x + y ∈ AdelicBox.integralFiniteAdeles R K :=
  fun v => add_mem (hx v) (hy v)

theorem mul_mem_integralFiniteAdeles {x y : FiniteAdeleRing R K}
    (hx : x ∈ AdelicBox.integralFiniteAdeles R K) (hy : y ∈ AdelicBox.integralFiniteAdeles R K) :
    x * y ∈ AdelicBox.integralFiniteAdeles R K :=
  fun v => mul_mem (hx v) (hy v)

theorem valued_apply_le_one {x : FiniteAdeleRing R K}
    (hx : x ∈ AdelicBox.integralFiniteAdeles R K) (v : HeightOneSpectrum R) :
    Valued.v (x v) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx v)

theorem zero_mem_idealBall (N : Ideal R) : (0 : FiniteAdeleRing R K) ∈ idealBall R K N :=
  fun v => by
    rw [show (0 : FiniteAdeleRing R K) v = 0 from rfl, map_zero]
    exact zero_le

variable {N : Ideal R}

theorem add_mem_idealBall {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x + y ∈ idealBall R K N := fun v =>
  (Valuation.map_add _ _ _).trans (max_le (hx v) (hy v))

theorem mul_mem_idealBall_left {x y : FiniteAdeleRing R K}
    (hx : x ∈ AdelicBox.integralFiniteAdeles R K) (hy : y ∈ idealBall R K N) :
    x * y ∈ idealBall R K N := fun v => by
  rw [show (x * y) v = x v * y v from rfl, map_mul]
  calc Valued.v (x v) * Valued.v (y v) ≤ 1 * idealBound R N v :=
        mul_le_mul' (valued_apply_le_one hx v) (hy v)
    _ = idealBound R N v := one_mul _

theorem mul_mem_idealBall_right {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ AdelicBox.integralFiniteAdeles R K) : x * y ∈ idealBall R K N := by
  rw [mul_comm]
  exact mul_mem_idealBall_left hy hx

theorem neg_mem_idealBall {x : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N) :
    -x ∈ idealBall R K N := fun v => by
  rw [show (-x) v = -(x v) from rfl, Valuation.map_neg]; exact hx v

theorem sub_mem_idealBall {x y : FiniteAdeleRing R K} (hx : x ∈ idealBall R K N)
    (hy : y ∈ idealBall R K N) : x - y ∈ idealBall R K N := by
  rw [sub_eq_add_neg]; exact add_mem_idealBall hx (neg_mem_idealBall hy)

theorem idealBall_mono {M : Ideal R} (h : M ≤ N) :
    idealBall R K M ⊆ idealBall R K N := fun x hx v => by
  refine (hx v).trans ?_
  by_cases hM : M = ⊥
  · rw [idealBound, ite_eq_left hM]
    exact zero_le
  have hN : N ≠ ⊥ := fun hN => hM (le_bot_iff.mp (hN ▸ h))
  rw [idealBound, ite_eq_right hM, idealBound, ite_eq_right hN, WithZero.exp_le_exp,
    neg_le_neg_iff, Int.ofNat_le]
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hM)
    (Associates.irreducible_mk.mpr v.irreducible)
    (Associates.mk_le_mk_iff_dvd.mpr (Ideal.dvd_iff_le.mpr h))

variable (R K N)

/-- A `2 × 2` matrix over the finite adeles has level zero at `N` when its entries are integral
and its lower-left entry lies in `idealBall R K N`. -/
structure IsLevelZeroMatrix (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Prop where
  /-- Every entry is integral at every finite place. -/
  integral : ∀ i j, m i j ∈ AdelicBox.integralFiniteAdeles R K
  /-- The lower-left entry lies in `N` at every finite place. -/
  lowerLeft : m 1 0 ∈ idealBall R K N

/-- A matrix of level zero at `N` has level one at `N` when, in addition, its lower-right entry
is congruent to `1` modulo `N` at every finite place. -/
structure IsLevelOneMatrix (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) : Prop
    extends IsLevelZeroMatrix R K N m where
  /-- The lower-right entry is congruent to `1` modulo `N` at every finite place. -/
  lowerRight : m 1 1 - 1 ∈ idealBall R K N

variable {R K N}

namespace IsLevelZeroMatrix

protected theorem one : IsLevelZeroMatrix R K N 1 where
  integral i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [Matrix.one_apply_ne (by decide)]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelZeroMatrix R K N m) (hm' : IsLevelZeroMatrix R K N m') :
    IsLevelZeroMatrix R K N (m * m') where
  integral i j := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_integralFiniteAdeles
      (mul_mem_integralFiniteAdeles (hm.integral i 0) (hm'.integral 0 j))
      (mul_mem_integralFiniteAdeles (hm.integral i 1) (hm'.integral 1 j))
  lowerLeft := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 0))
      (mul_mem_idealBall_left (hm.integral 1 1) hm'.lowerLeft)

end IsLevelZeroMatrix

namespace IsLevelOneMatrix

protected theorem one : IsLevelOneMatrix R K N 1 where
  toIsLevelZeroMatrix := .one
  lowerRight := by
    rw [Matrix.one_apply_eq, sub_self]
    exact zero_mem_idealBall N

variable {m m' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)}

protected theorem mul (hm : IsLevelOneMatrix R K N m) (hm' : IsLevelOneMatrix R K N m') :
    IsLevelOneMatrix R K N (m * m') where
  toIsLevelZeroMatrix := hm.toIsLevelZeroMatrix.mul hm'.toIsLevelZeroMatrix
  lowerRight := by
    have h : (m * m') 1 1 - 1 = m 1 0 * m' 0 1 + ((m 1 1 - 1) * m' 1 1 + (m' 1 1 - 1)) := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [h]
    exact add_mem_idealBall (mul_mem_idealBall_right hm.lowerLeft (hm'.integral 0 1))
      (add_mem_idealBall (mul_mem_idealBall_right hm.lowerRight (hm'.integral 1 1))
        hm'.lowerRight)

end IsLevelOneMatrix

variable (R K N)

/-- The level subgroup of `GL₂` over the finite adeles at `N`: the matrices `g` such that `g`
and `g⁻¹` have level one at `N`. -/
def finiteLevelOne : Subgroup (GL (Fin 2) (FiniteAdeleRing R K)) where
  carrier := {g | IsLevelOneMatrix R K N (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) ∧
    IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _)}
  one_mem' := ⟨by rw [Units.val_one]; exact .one, by rw [inv_one, Units.val_one]; exact .one⟩
  mul_mem' ha hb := ⟨by rw [Units.val_mul]; exact ha.1.mul hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact hb.2.mul ha.2⟩
  inv_mem' ha := ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

/-- The adelic level subgroup at `N`: the matrices over the adeles whose finite part lies in
`finiteLevelOne R K N`. -/
def levelOne : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  (finiteLevelOne R K N).comap (glFin R K)

variable {R K N}

theorem mem_finiteLevelOne_iff {g : GL (Fin 2) (FiniteAdeleRing R K)} :
    g ∈ finiteLevelOne R K N ↔ IsLevelOneMatrix R K N (g : Matrix _ _ _) ∧
      IsLevelOneMatrix R K N ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing R K)) : Matrix _ _ _) :=
  Iff.rfl

theorem mem_levelOne_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ levelOne R K N ↔ glFin R K g ∈ finiteLevelOne R K N :=
  Subgroup.mem_comap

end FiniteLevel

section Gen

/-- The embedding `a ↦ diag(a, 1)` of the units of a commutative ring into `GL₂`. -/
def diagOne {A : Type*} [CommRing A] : Aˣ →* GL (Fin 2) A where
  toFun a :=
    { val := Matrix.diagonal ![(a : A), 1]
      inv := Matrix.diagonal ![((a⁻¹ : Aˣ) : A), 1]
      val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
      inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

variable (v : HeightOneSpectrum R)

/-- The matrix `diag(t, 1)` at the finite place `v`, with the identity at every other place. -/
def heckeGenAt : (v.adicCompletion K)ˣ →* GL (Fin 2) (AdeleRing R K) :=
  diagOne.comp ((Units.map (finIncl R K)).comp (localUnit R K v))

/-- The Hecke generator at the finite place `v`: the matrix `diag(ϖ, 1)` at `v`, for the chosen
uniformizer `ϖ = uniformizerUnit R K v`, with the identity at every other place. -/
def heckeGen : GL (Fin 2) (AdeleRing R K) :=
  heckeGenAt R K v (uniformizerUnit R K v)

end Gen

end NumberField.AdelicLevel

namespace AutomorphicForm

variable (F : Type*) [Field F] [NumberField F]

/-- The matrices over the adeles of `F` whose infinite part is the identity: the kernel of
`NumberField.AdelicLevel.glArch`. -/
def finiteAdelicGL2Subgroup : Subgroup (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
  (NumberField.AdelicLevel.glArch (𝓞 F) F).ker

theorem mem_finiteAdelicGL2Subgroup_iff (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    g ∈ finiteAdelicGL2Subgroup F ↔ NumberField.AdelicLevel.glArch (𝓞 F) F g = 1 :=
  MonoidHom.mem_ker

end AutomorphicForm

end
