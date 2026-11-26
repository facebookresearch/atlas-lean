/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_AdelicLsXi.lean`,
`Definitions/Def_AutomorphicForm_ArchType.lean`,
`Definitions/Def_AutomorphicForm_ArchWeightChar.lean`,
`Definitions/Def_AutomorphicForm_FnTwist.lean`,
`Definitions/Def_AutomorphicForm_RowIsometryInvariance.lean`,
`Definitions/Def_NumberField_AdelicLevel.lean`,
`Theorems/Thm_AutomorphicForm_hasArchType0_fnTwist.lean`
and
`P2M/Sol/S_AutomorphicForm_hasArchType0_fnTwist.lean`
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

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing

import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace AutomorphicForm

/-- The group of `2 × 2` invertible matrices over the adele ring. -/
abbrev AdelicGL2 (R : Type*) (K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

/-- The determinant character of an adelic matrix, viewed in `ℂ`. -/
def chiDet (R : Type*) (K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (η : (AdeleRing R K)ˣ →* ℂˣ) : AdelicGL2 R K → ℂ :=
  fun g => ((η (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

/-- Twisting a function on the adelic group by a determinant character. -/
def fnTwist (F : Type*) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => chiDet (𝓞 F) F η g * φ g

@[simp]
theorem fnTwist_apply (F : Type*) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    fnTwist F η φ g = chiDet (𝓞 F) F η g * φ g :=
  rfl

section RowIsometry

variable {K : Type*} [NormedField K]

/-- A matrix in `GL (Fin 2) K` whose rows act as an isometry and whose
determinant has norm `1`. -/
def IsRowIsometry (k : GL (Fin 2) K) : Prop :=
  ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 ∧
    ∀ x y : K,
      ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2

theorem isRowIsometry_one : IsRowIsometry (1 : GL (Fin 2) K) := by
  constructor
  · simp
  · intro x y
    have h00 : (1 : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := Matrix.one_apply_eq 0
    have h11 : (1 : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := Matrix.one_apply_eq 1
    have h10 : (1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
      Matrix.one_apply_ne (by decide)
    have h01 : (1 : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
      Matrix.one_apply_ne (by decide)
    change ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * (1 : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * (1 : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [h00, h11, h10, h01, mul_one, mul_one, mul_zero, mul_zero, add_zero,
      zero_add]

theorem IsRowIsometry.mul {k k' : GL (Fin 2) K} (hk : IsRowIsometry k)
    (hk' : IsRowIsometry k') : IsRowIsometry (k * k') := by
  obtain ⟨hdet, hrow⟩ := hk
  obtain ⟨hdet', hrow'⟩ := hk'
  have hcoe : ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K) := rfl
  constructor
  · rw [hcoe, Matrix.det_mul, norm_mul, hdet, hdet', one_mul]
  · intro x y
    have hentry : ∀ i : Fin 2,
        x * ((k : Matrix (Fin 2) (Fin 2) K) * (k' : Matrix (Fin 2) (Fin 2) K)) 0 i
          + y * ((k : Matrix (Fin 2) (Fin 2) K)
              * (k' : Matrix (Fin 2) (Fin 2) K)) 1 i
        = (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0
              + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
              * (k' : Matrix (Fin 2) (Fin 2) K) 0 i
          + (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
              + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1)
              * (k' : Matrix (Fin 2) (Fin 2) K) 1 i := by
      intro i
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    change ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
        + ‖x * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1
            + y * ((k * k' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      = ‖x‖ ^ 2 + ‖y‖ ^ 2
    rw [hcoe, hentry 0, hentry 1,
      hrow' (x * (k : Matrix (Fin 2) (Fin 2) K) 0 0
          + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0)
        (x * (k : Matrix (Fin 2) (Fin 2) K) 0 1
          + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1),
      hrow x y]

theorem IsRowIsometry.inv {k : GL (Fin 2) K} (hk : IsRowIsometry k) :
    IsRowIsometry k⁻¹ := by
  obtain ⟨hdet, hrow⟩ := hk
  have hcoe : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := Units.inv_mul k
  constructor
  · have hd : ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        * ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [← Matrix.det_mul, hcoe, Matrix.det_one]
    have hnorm := congrArg norm hd
    rwa [norm_mul, hdet, mul_one, norm_one] at hnorm
  · intro x y
    set A := ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hA
    set B := ((k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hB
    have entry : ∀ i j : Fin 2,
        A i 0 * B 0 j + A i 1 * B 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j := by
      intro i j
      calc A i 0 * B 0 j + A i 1 * B 1 j
          = (A * B) i j := by rw [Matrix.mul_apply, Fin.sum_univ_two]
        _ = (1 : Matrix (Fin 2) (Fin 2) K) i j := by rw [hcoe]
    have e00 := entry 0 0
    have e01 := entry 0 1
    have e10 := entry 1 0
    have e11 := entry 1 1
    rw [Matrix.one_apply_eq] at e00 e11
    rw [Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at e01
    rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
    have hwx : (x * A 0 0 + y * A 1 0) * B 0 0
        + (x * A 0 1 + y * A 1 1) * B 1 0 = x := by
      calc (x * A 0 0 + y * A 1 0) * B 0 0
            + (x * A 0 1 + y * A 1 1) * B 1 0
          = x * (A 0 0 * B 0 0 + A 0 1 * B 1 0)
            + y * (A 1 0 * B 0 0 + A 1 1 * B 1 0) := by ring
        _ = x * 1 + y * 0 := by rw [e00, e10]
        _ = x := by ring
    have hwy : (x * A 0 0 + y * A 1 0) * B 0 1
        + (x * A 0 1 + y * A 1 1) * B 1 1 = y := by
      calc (x * A 0 0 + y * A 1 0) * B 0 1
            + (x * A 0 1 + y * A 1 1) * B 1 1
          = x * (A 0 0 * B 0 1 + A 0 1 * B 1 1)
            + y * (A 1 0 * B 0 1 + A 1 1 * B 1 1) := by ring
        _ = x * 0 + y * 1 := by rw [e01, e11]
        _ = y := by ring
    have key := hrow (x * A 0 0 + y * A 1 0) (x * A 0 1 + y * A 1 1)
    rw [hwx, hwy] at key
    exact key.symm

variable (K)

/-- The subgroup of row-isometries in `GL (Fin 2) K`. -/
def rowIsometrySubgroup : Subgroup (GL (Fin 2) K) where
  carrier := {k : GL (Fin 2) K | IsRowIsometry k}
  one_mem' := isRowIsometry_one
  mul_mem' := fun hk hk' => IsRowIsometry.mul hk hk'
  inv_mem' := fun hk => IsRowIsometry.inv hk

variable {K}

theorem mem_rowIsometrySubgroup_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup K ↔ IsRowIsometry k :=
  Iff.rfl

variable (K)

/-- The subgroup of row-isometries of determinant `1`. -/
def rowIsometrySubgroup₀ : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.det).ker ⊓ rowIsometrySubgroup K

theorem mem_rowIsometrySubgroup₀_iff {k : GL (Fin 2) K} :
    k ∈ rowIsometrySubgroup₀ K ↔
      (k : Matrix (Fin 2) (Fin 2) K).det = 1 ∧ IsRowIsometry k := by
  unfold rowIsometrySubgroup₀
  constructor
  · rintro ⟨hd, hi⟩
    exact ⟨Units.val_eq_one.mpr hd, hi⟩
  · rintro ⟨hd, hi⟩
    refine ⟨?_, hi⟩
    ext
    exact hd

end RowIsometry

section ArchimedeanInclusion

variable (F : Type*) [Field F] [NumberField F]

abbrev archMatrixPiEquiv :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ≃+*
      Π w : InfinitePlace F, Matrix (Fin 2) (Fin 2) w.Completion :=
  Matrix.piRingEquiv

def archMatrixUpdate (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  (archMatrixPiEquiv F).symm (Function.update 1 w m)

omit [NumberField F] in
private theorem archMatrixPiEquiv_archMatrixUpdate (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixPiEquiv F (archMatrixUpdate F w m)
      = Function.update
          (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
  (archMatrixPiEquiv F).apply_symm_apply _

private theorem archMatrixUpdate_apply_self (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2) :
    archMatrixUpdate F w m i j w = m i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hw := congrFun h w
  simp only [Function.update_self] at hw
  exact congrFun (congrFun hw i) j

private theorem archMatrixUpdate_apply_of_ne (w : InfinitePlace F)
    (m : Matrix (Fin 2) (Fin 2) w.Completion) (i j : Fin 2)
    {v : InfinitePlace F} (hvw : v ≠ w) :
    archMatrixUpdate F w m i j v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  have h := archMatrixPiEquiv_archMatrixUpdate F w m
  have hv := congrFun h v
  simp only [Function.update_of_ne hvw, Pi.one_apply] at hv
  exact congrFun (congrFun hv i) j

public theorem archMatrixUpdate_one (w : InfinitePlace F) :
    archMatrixUpdate F w (1 : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_one]
  exact Function.update_eq_self_iff.mpr rfl

public theorem archMatrixUpdate_mul (w : InfinitePlace F)
    (a b : Matrix (Fin 2) (Fin 2) w.Completion) :
    archMatrixUpdate F w (a * b)
      = archMatrixUpdate F w a * archMatrixUpdate F w b := by
  apply (archMatrixPiEquiv F).injective
  rw [archMatrixPiEquiv_archMatrixUpdate, map_mul,
    archMatrixPiEquiv_archMatrixUpdate, archMatrixPiEquiv_archMatrixUpdate]
  funext v
  by_cases hv : v = w
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

def archMatrixInclHom (w : InfinitePlace F) :
    Matrix (Fin 2) (Fin 2) w.Completion →*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) where
  toFun := archMatrixUpdate F w
  map_one' := archMatrixUpdate_one F w
  map_mul' := archMatrixUpdate_mul F w

def archGLIncl (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  Units.map (archMatrixInclHom F w)

def adelicMatrixProdEquiv :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) ≃+*
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) ×
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) where
  toFun M := ((RingHom.fst _ _).mapMatrix M, (RingHom.snd _ _).mapMatrix M)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j; rfl
  right_inv p := by ext i j <;> rfl
  map_mul' M N := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]; exact map_mul _ M N
    · simp only [Prod.snd_mul]; exact map_mul _ M N
  map_add' _ _ := rfl

def adelicArchGLIncl :
    GL (Fin 2) (InfiniteAdeleRing F) →* AdelicGL2 (𝓞 F) F :=
  (Units.mapEquiv (adelicMatrixProdEquiv F).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (MonoidHom.id _) (1 : _ →* GL (Fin 2) _)

/-- Inclusion of a local archimedean matrix into the adelic group. -/
def adelicArchGLInclAt (w : InfinitePlace F) :
    GL (Fin 2) w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (archGLIncl F w)

/-- **Inclusions at distinct infinite places commute.** For distinct infinite places `w ≠ w'`,
the adelic inclusions of a matrix `a` at `w` and of a matrix `b` at `w'` commute. -/
public theorem adelicArchGLInclAt_commute {w w' : InfinitePlace F} (h : w ≠ w')
    (a : GL (Fin 2) w.Completion) (b : GL (Fin 2) w'.Completion) :
    Commute (adelicArchGLInclAt F w a) (adelicArchGLInclAt F w' b) := by
  have hm : Commute (archMatrixUpdate F w a) (archMatrixUpdate F w' b) := by
    apply (archMatrixPiEquiv F).injective
    rw [map_mul, map_mul, archMatrixPiEquiv_archMatrixUpdate,
      archMatrixPiEquiv_archMatrixUpdate]
    exact (Pi.mulSingle_commute h _ _).eq
  have hg : Commute (archGLIncl F w a) (archGLIncl F w' b) := Commute.units_of_val hm
  exact hg.map (adelicArchGLIncl F)

private def adeleArch : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def adeleFin : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem adeleArch_apply (a : AdeleRing (𝓞 F) F) :
    adeleArch F a = a.1 :=
  rfl

private theorem adeleFin_apply (a : AdeleRing (𝓞 F) F) :
    adeleFin F a = a.2 :=
  rfl

private def glArch :
    GL (Fin 2) (AdeleRing (𝓞 F) F) →* GL (Fin 2) (InfiniteAdeleRing F) :=
  Matrix.GeneralLinearGroup.map (adeleArch F)

private def glFin :
    GL (Fin 2) (AdeleRing (𝓞 F) F) →*
      GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.GeneralLinearGroup.map (adeleFin F)

private theorem glArch_adelicArchGLIncl
    (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glArch F (adelicArchGLIncl F k) = k := by
  ext i j
  rfl

private theorem glFin_adelicArchGLIncl
    (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    glFin F (adelicArchGLIncl F k) = 1 := by
  ext i j
  rfl

private theorem det_adelicArchGLInclAt_eq_one (w : InfinitePlace F)
    (k : GL (Fin 2) w.Completion)
    (hk : (k : Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    Matrix.GeneralLinearGroup.det (adelicArchGLInclAt F w k) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  set A : AdelicGL2 (𝓞 F) F := adelicArchGLInclAt F w k with hA
  have hAdef : A = adelicArchGLIncl F (archGLIncl F w k) := hA
  refine Prod.ext ?_ ?_
  · have h1 : ((A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det).1
        = ((adeleArch F).mapMatrix
            (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).det :=
      (adeleArch_apply F _).symm.trans (RingHom.map_det (adeleArch F) _)
    have h2 : (adeleArch F).mapMatrix
          (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glArch F A : GL (Fin 2) (InfiniteAdeleRing F)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
      ext i j; rfl
    rw [show (1 : AdeleRing (𝓞 F) F).1 = 1 from rfl, h1, h2, hAdef,
      glArch_adelicArchGLIncl]
    funext v
    have h3 : (((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det) v
        = ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
            ((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) :
              Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))).det :=
      (Pi.evalRingHom_apply (fun v : InfinitePlace F => v.Completion) v _).symm.trans
        (RingHom.map_det (Pi.evalRingHom
          (fun v : InfinitePlace F => v.Completion) v) _)
    rw [h3, show (1 : InfiniteAdeleRing F) v = 1 from rfl]
    have h4 : ((archGLIncl F w k : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
    by_cases hv : v = w
    · subst hv
      have h5 : (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
          (archMatrixUpdate F v (k : Matrix (Fin 2) (Fin 2) v.Completion))
          = (k : Matrix (Fin 2) (Fin 2) v.Completion) := by
        ext i j
        simp [RingHom.mapMatrix_apply, Matrix.map_apply,
          archMatrixUpdate_apply_self]
      rw [h4, h5, hk]
    · have h5 : (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) v).mapMatrix
          (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion)) = 1 := by
        ext i j
        simp [RingHom.mapMatrix_apply, Matrix.map_apply,
          archMatrixUpdate_apply_of_ne F w _ i j hv]
      rw [h4, h5, Matrix.det_one]
  · have h1 : ((A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det).2
        = ((adeleFin F).mapMatrix
            (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).det :=
      (adeleFin_apply F _).symm.trans (RingHom.map_det (adeleFin F) _)
    have h2 : (adeleFin F).mapMatrix
          (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = ((glFin F A : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
      ext i j; rfl
    rw [show (1 : AdeleRing (𝓞 F) F).2 = 1 from rfl, h1, h2, hAdef,
      glFin_adelicArchGLIncl, Units.val_one, Matrix.det_one]

end ArchimedeanInclusion

section HasArchTypeZero

variable (F : Type*) [Field F] [NumberField F]

/-- The archimedean character condition at one infinite place, for
determinant-one row-isometries. -/
def HasArchCharacterAt₀ (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))
      = (χ k : ℂ) * φ g

/-- The archimedean type condition at every infinite place, for
determinant-one row-isometries. -/
def HasArchType₀
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, HasArchCharacterAt₀ F w (χ w) φ

/-- Twisting by a determinant character preserves a prescribed
archimedean type for determinant-one row-isometries. -/
public theorem hasArchType₀_fnTwist
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasArchType₀ F χ φ) :
    HasArchType₀ F χ (fnTwist F η φ) := by
  intro w k g
  have hk : ((k : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  have hdet := det_adelicArchGLInclAt_eq_one F w (k : GL (Fin 2) w.Completion) hk
  simp only [fnTwist_apply, chiDet, map_mul, hdet, mul_one, hφ w k g]
  ring

end HasArchTypeZero

end AutomorphicForm

end
