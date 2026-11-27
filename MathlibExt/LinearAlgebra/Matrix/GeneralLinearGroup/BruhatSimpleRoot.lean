/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMonomialUniqueness
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryDiagonal
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import Mathlib.Order.Cover
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Elementary Weyl and torus representatives

For finite index sets, elementary matrices over a ring give Weyl and torus
representatives in `GL`. Over a commutative ring we also record their monomial
descriptions and determinant-one realizations in `SL`, with coefficient-map
compatibility and the Weyl-product formula for torus elements.
-/

@[expose] public section

open Matrix
open Equiv
open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

section WeylGL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [Ring R]

def weylGL (i j : ι) (hij : i ≠ j) : GL ι R :=
  elementary i j hij (1 : R) *
    elementary j i hij.symm (-1 : R) *
    elementary i j hij (1 : R)

def weylGLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) : GL ι R :=
  elementary i j hij (u : R) *
    elementary j i hij.symm (-(↑u⁻¹ : R)) *
    elementary i j hij (u : R)

variable {S : Type*} [Ring S]

theorem weylGLUnit_mapRingHom (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    mapRingHom (n := ι) f (weylGLUnit (R := R) i j hij u) =
      weylGLUnit i j hij (Units.map f.toMonoidHom u) := by
  simp [weylGLUnit, mapRingHom_elementary, Units.coe_map,
    Units.coe_map_inv, map_neg]

theorem weylGL_mapRingHom (f : R →+* S)
    (i j : ι) (hij : i ≠ j) :
    mapRingHom (n := ι) f (weylGL (R := R) i j hij) =
      weylGL (R := S) i j hij := by
  simp [weylGL, mapRingHom_elementary]

private lemma units_val_mul_inv_aux {R : Type*} [Ring R] (u : Rˣ) :
    (u : R) * (↑u⁻¹ : R) = 1 := by
  calc (u : R) * (↑u⁻¹ : R) = ((u * u⁻¹ : Rˣ) : R) := by
        rw [Units.val_mul]
    _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
    _ = 1 := rfl

private lemma units_inv_val_mul_aux {R : Type*} [Ring R] (u : Rˣ) :
    (↑u⁻¹ : R) * (u : R) = 1 := by
  calc (↑u⁻¹ : R) * (u : R) = ((u⁻¹ * u : Rˣ) : R) := by
        rw [Units.val_mul]
    _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
    _ = 1 := rfl

theorem weylGLUnit_inv (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (weylGLUnit i j hij u)⁻¹ = weylGLUnit i j hij (-u) := by
  have h1 : (elementary i j hij (u : R))⁻¹ =
      elementary i j hij (-(u : R)) := by
    rw [elementary_inv]
  have h2 : (elementary j i hij.symm (-(↑u⁻¹ : R)))⁻¹ =
      elementary j i hij.symm (↑u⁻¹ : R) := by
    rw [elementary_inv, neg_neg]
  calc (weylGLUnit i j hij u)⁻¹
      = (elementary i j hij (u : R) *
          elementary j i hij.symm (-(↑u⁻¹ : R)) *
          elementary i j hij (u : R))⁻¹ := rfl
    _ = (elementary i j hij (u : R) *
          (elementary j i hij.symm (-(↑u⁻¹ : R)) *
            elementary i j hij (u : R)))⁻¹ := by
        rw [mul_assoc]
    _ = (elementary j i hij.symm (-(↑u⁻¹ : R)) *
          elementary i j hij (u : R))⁻¹ *
          (elementary i j hij (u : R))⁻¹ := by
        rw [_root_.mul_inv_rev]
    _ = ((elementary i j hij (u : R))⁻¹ *
            (elementary j i hij.symm (-(↑u⁻¹ : R)))⁻¹) *
          (elementary i j hij (u : R))⁻¹ := by
        rw [_root_.mul_inv_rev]
    _ = (elementary i j hij (-(u : R)) *
            elementary j i hij.symm (↑u⁻¹ : R)) *
          elementary i j hij (-(u : R)) := by
        rw [h1, h2]
    _ = elementary i j hij (-(u : R)) *
          elementary j i hij.symm (↑u⁻¹ : R) *
          elementary i j hij (-(u : R)) := by
        rw [mul_assoc]
    _ = weylGLUnit i j hij (-u) := by
        simp [weylGLUnit, Units.val_neg]

theorem weylGL_inv (i j : ι) (hij : i ≠ j) :
    (weylGL (R := R) i j hij)⁻¹ = weylGLUnit i j hij (-1 : Rˣ) := by
  have h : weylGL (R := R) i j hij = weylGLUnit i j hij (1 : Rˣ) := rfl
  rw [h, weylGLUnit_inv]

end WeylGL

section WeylSL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

def weylSL (i j : ι) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup ι R :=
  Matrix.SpecialLinearGroup.transvection hij (1 : R) *
    Matrix.SpecialLinearGroup.transvection hij.symm (-1 : R) *
    Matrix.SpecialLinearGroup.transvection hij (1 : R)

def weylSLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup ι R :=
  Matrix.SpecialLinearGroup.transvection hij (u : R) *
    Matrix.SpecialLinearGroup.transvection hij.symm (-(↑u⁻¹ : R)) *
    Matrix.SpecialLinearGroup.transvection hij (u : R)

variable {S : Type*} [CommRing S]

theorem weylSLUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup.map f (weylSLUnit i j hij u) =
      weylSLUnit i j hij (Units.map f.toMonoidHom u) := by
  apply Subtype.ext
  calc (Matrix.SpecialLinearGroup.map f (weylSLUnit i j hij u) :
      Matrix ι ι S)
      = f.mapMatrix
          ((1 + Matrix.single i j (u : R)) *
            (1 + Matrix.single j i (-(↑u⁻¹ : R))) *
            (1 + Matrix.single i j (u : R))) := by
        simp [weylSLUnit,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.SpecialLinearGroup.coe_mul]
    _ = f.mapMatrix (1 + Matrix.single i j (u : R)) *
          f.mapMatrix (1 + Matrix.single j i (-(↑u⁻¹ : R))) *
          f.mapMatrix (1 + Matrix.single i j (u : R)) := by
        rw [map_mul, map_mul]
    _ = (1 + Matrix.single i j (f (u : R))) *
          (1 + Matrix.single j i (f (-(↑u⁻¹ : R)))) *
          (1 + Matrix.single i j (f (u : R))) := by
        simp [map_add, map_one, Matrix.map_single]
    _ = (1 + Matrix.single i j (↑(Units.map f.toMonoidHom u) : S)) *
          (1 + Matrix.single j i (-(↑(Units.map f.toMonoidHom u)⁻¹ : S))) *
          (1 + Matrix.single i j (↑(Units.map f.toMonoidHom u) : S)) := by
        simp [Units.coe_map, Units.coe_map_inv, map_neg]
    _ = (weylSLUnit i j hij (Units.map f.toMonoidHom u) :
          Matrix ι ι S) := by
        simp [weylSLUnit,
          Matrix.SpecialLinearGroup.transvection_coe]

theorem weylSL_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map f (weylSL (R := R) i j hij) =
      weylSL (R := S) i j hij := by
  apply Subtype.ext
  calc (Matrix.SpecialLinearGroup.map f (weylSL i j hij) :
      Matrix ι ι S)
      = f.mapMatrix
          ((1 + Matrix.single i j (1 : R)) *
            (1 + Matrix.single j i (-1 : R)) *
            (1 + Matrix.single i j (1 : R))) := by
        simp [weylSL,
          Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.SpecialLinearGroup.coe_mul]
    _ = f.mapMatrix (1 + Matrix.single i j (1 : R)) *
          f.mapMatrix (1 + Matrix.single j i (-1 : R)) *
          f.mapMatrix (1 + Matrix.single i j (1 : R)) := by
        rw [map_mul, map_mul]
    _ = (1 + Matrix.single i j (1 : S)) *
          (1 + Matrix.single j i (-1 : S)) *
          (1 + Matrix.single i j (1 : S)) := by
        simp [Matrix.map_single, map_add, map_one, map_neg]
    _ = (weylSL (R := S) i j hij : Matrix ι ι S) := by
        simp [weylSL,
          Matrix.SpecialLinearGroup.transvection_coe]

private theorem toGL_weylSLUnit_eq (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (Matrix.SpecialLinearGroup.toGL
        (weylSLUnit (R := R) i j hij u) : GL ι R) =
      weylGLUnit (R := R) i j hij u := by
  apply Units.ext
  simp only [weylSLUnit, weylGLUnit,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe,
    coe_elementary]

private theorem toGL_weylSL_eq (i j : ι) (hij : i ≠ j) :
    (Matrix.SpecialLinearGroup.toGL
        (weylSL (R := R) i j hij) : GL ι R) =
      weylGL (R := R) i j hij := by
  apply Units.ext
  simp only [weylSL, weylGL,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe,
    coe_elementary]

theorem weylSLUnit_inv (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (weylSLUnit i j hij u)⁻¹ = weylSLUnit i j hij (-u) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij u)⁻¹
      = (Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij u))⁻¹ := by
        rw [map_inv]
    _ = (weylGLUnit (R := R) i j hij u)⁻¹ := by
        rw [toGL_weylSLUnit_eq]
    _ = weylGLUnit (R := R) i j hij (-u) := by
        rw [weylGLUnit_inv]
    _ = Matrix.SpecialLinearGroup.toGL (weylSLUnit i j hij (-u)) := by
        rw [toGL_weylSLUnit_eq]

theorem weylSL_inv (i j : ι) (hij : i ≠ j) :
    (weylSL (R := R) i j hij)⁻¹ = weylSLUnit i j hij (-1 : Rˣ) := by
  have h : weylSL (R := R) i j hij = weylSLUnit i j hij (1 : Rˣ) := rfl
  rw [h, weylSLUnit_inv]

end WeylSL

section WeylMonomial

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

def weylWeightUnit (i j : ι) (_hij : i ≠ j) (u : Rˣ) : ι → Rˣ :=
  fun k => if k = i then u else if k = j then -u⁻¹ else 1

def torusWeightUnit (i j : ι) (_hij : i ≠ j) (u : Rˣ) : ι → Rˣ :=
  fun k => if k = i then u else if k = j then u⁻¹ else 1

def weylPerm (i j : ι) (_hij : i ≠ j) : Equiv.Perm ι :=
  Equiv.swap i j

def torusPerm (ι : Type*) [DecidableEq ι] : Equiv.Perm ι :=
  1

def weylMonomialBaseUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialBase Rˣ ι :=
  ⟨weylWeightUnit i j hij u, weylPerm i j hij⟩

def torusMonomialBaseUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialBase Rˣ ι :=
  ⟨torusWeightUnit i j hij u, torusPerm ι⟩

def weylMonomialBase (i j : ι) (hij : i ≠ j) :
    MonomialBase Rˣ ι :=
  weylMonomialBaseUnit i j hij 1

def torusMonomialBase (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialBase Rˣ ι :=
  torusMonomialBaseUnit i j hij u

private lemma val_mul_inv_unit (u : Rˣ) :
    (u : R) * (↑u⁻¹ : R) = 1 := by
  calc (u : R) * (↑u⁻¹ : R) = ((u * u⁻¹ : Rˣ) : R) := by
        rw [Units.val_mul]
    _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
    _ = 1 := rfl

private lemma inv_val_mul_unit (u : Rˣ) :
    (↑u⁻¹ : R) * (u : R) = 1 := by
  calc (↑u⁻¹ : R) * (u : R) = ((u⁻¹ * u : Rˣ) : R) := by
        rw [Units.val_mul]
    _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
    _ = 1 := rfl

private lemma weylWeightUnit_prod_val (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (Finset.univ : Finset ι).prod
      (fun k => (weylWeightUnit (R := R) i j hij u k : R)) = -1 := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hj_mem_erase : j ∈ (Finset.univ : Finset ι).erase i := by
    simp [Finset.mem_erase, hij.symm]
  calc (Finset.univ : Finset ι).prod
        (fun k => (weylWeightUnit i j hij u k : R))
      = (weylWeightUnit i j hij u i : R) *
          ((Finset.univ : Finset ι).erase i).prod
            (fun k => (weylWeightUnit i j hij u k : R)) :=
        (Finset.mul_prod_erase _ _ hi).symm
    _ = (u : R) *
          ((Finset.univ : Finset ι).erase i).prod
            (fun k => (weylWeightUnit i j hij u k : R)) := by
        simp [weylWeightUnit]
    _ = (u : R) * ((weylWeightUnit i j hij u j : R) *
          (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (weylWeightUnit i j hij u k : R))) := by
        have h_eq :
            ((Finset.univ : Finset ι).erase i).prod
              (fun k => (weylWeightUnit i j hij u k : R)) =
              (weylWeightUnit i j hij u j : R) *
                (((Finset.univ : Finset ι).erase i).erase j).prod
                  (fun k => (weylWeightUnit i j hij u k : R)) :=
          (Finset.mul_prod_erase _ _ hj_mem_erase).symm
        rw [h_eq]
    _ = (u : R) * (-(↑u⁻¹ : R) *
          (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (weylWeightUnit i j hij u k : R))) := by
        have hj_ne_i : j ≠ i := hij.symm
        simp [weylWeightUnit, hj_ne_i]
    _ = (u : R) * (-(↑u⁻¹ : R) * 1) := by
        have h_rest : (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (weylWeightUnit i j hij u k : R)) = 1 := by
          apply Finset.prod_eq_one
          intro k hk
          have hk_ne_i : k ≠ i := by
            have : k ∈ (Finset.univ : Finset ι).erase i :=
              Finset.mem_of_mem_erase hk
            exact (Finset.mem_erase.mp this).1
          have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
          simp [weylWeightUnit, hk_ne_i, hk_ne_j]
        rw [h_rest]
    _ = -1 := by
        rw [mul_one, mul_neg, val_mul_inv_unit]

private lemma torusWeightUnit_prod_val (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (Finset.univ : Finset ι).prod
      (fun k => (torusWeightUnit (R := R) i j hij u k : R)) = 1 := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hj_mem_erase : j ∈ (Finset.univ : Finset ι).erase i := by
    simp [Finset.mem_erase, hij.symm]
  calc (Finset.univ : Finset ι).prod
        (fun k => (torusWeightUnit i j hij u k : R))
      = (torusWeightUnit i j hij u i : R) *
          ((Finset.univ : Finset ι).erase i).prod
            (fun k => (torusWeightUnit i j hij u k : R)) :=
        (Finset.mul_prod_erase _ _ hi).symm
    _ = (u : R) *
          ((Finset.univ : Finset ι).erase i).prod
            (fun k => (torusWeightUnit i j hij u k : R)) := by
        simp [torusWeightUnit]
    _ = (u : R) * ((torusWeightUnit i j hij u j : R) *
          (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (torusWeightUnit i j hij u k : R))) := by
        have h_eq :
            ((Finset.univ : Finset ι).erase i).prod
              (fun k => (torusWeightUnit i j hij u k : R)) =
              (torusWeightUnit i j hij u j : R) *
                (((Finset.univ : Finset ι).erase i).erase j).prod
                  (fun k => (torusWeightUnit i j hij u k : R)) :=
          (Finset.mul_prod_erase _ _ hj_mem_erase).symm
        rw [h_eq]
    _ = (u : R) * ((↑u⁻¹ : R) *
          (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (torusWeightUnit i j hij u k : R))) := by
        have hj_ne_i : j ≠ i := hij.symm
        simp [torusWeightUnit, hj_ne_i]
    _ = (u : R) * ((↑u⁻¹ : R) * 1) := by
        have h_rest : (((Finset.univ : Finset ι).erase i).erase j).prod
            (fun k => (torusWeightUnit i j hij u k : R)) = 1 := by
          apply Finset.prod_eq_one
          intro k hk
          have hk_ne_i : k ≠ i := by
            have : k ∈ (Finset.univ : Finset ι).erase i :=
              Finset.mem_of_mem_erase hk
            exact (Finset.mem_erase.mp this).1
          have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
          simp [torusWeightUnit, hk_ne_i, hk_ne_j]
        rw [h_rest]
    _ = 1 := by
        rw [mul_one, val_mul_inv_unit]

theorem weylMonomialBaseUnit_det (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialDetHom R ι (weylMonomialBaseUnit i j hij u) = 1 := by
  have h_coe : (monomialDetHom R ι (weylMonomialBaseUnit i j hij u) : R) = 1 := by
    rw [monomialDetHom_coe]
    have h_prod : (Finset.univ.prod fun k =>
        ((weylMonomialBaseUnit i j hij u).left k : R)) = -1 := by
      calc (Finset.univ.prod fun k =>
          ((weylMonomialBaseUnit i j hij u).left k : R))
          = (Finset.univ.prod fun k =>
            (weylWeightUnit i j hij u k : R)) := rfl
        _ = -1 := weylWeightUnit_prod_val i j hij u
    have h_sign : (Equiv.Perm.sign
        (weylMonomialBaseUnit i j hij u).right : R) = -1 := by
      have : (weylMonomialBaseUnit i j hij u).right =
          Equiv.swap i j := rfl
      rw [this, Equiv.Perm.sign_swap hij]
      simp
    rw [h_prod, h_sign]
    simp
  exact Units.ext h_coe

theorem torusMonomialBaseUnit_det (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialDetHom R ι (torusMonomialBaseUnit i j hij u) = 1 := by
  have h_coe : (monomialDetHom R ι (torusMonomialBaseUnit i j hij u) : R) = 1 := by
    rw [monomialDetHom_coe]
    have h_prod : (Finset.univ.prod fun k =>
        ((torusMonomialBaseUnit i j hij u).left k : R)) = 1 := by
      calc (Finset.univ.prod fun k =>
          ((torusMonomialBaseUnit i j hij u).left k : R))
          = (Finset.univ.prod fun k =>
            (torusWeightUnit i j hij u k : R)) := rfl
        _ = 1 := torusWeightUnit_prod_val i j hij u
    have h_sign : (Equiv.Perm.sign
        (torusMonomialBaseUnit i j hij u).right : R) = 1 := by
      have : (torusMonomialBaseUnit i j hij u).right = 1 := rfl
      rw [this]
      simp
    rw [h_prod, h_sign, one_mul]
  exact Units.ext h_coe

theorem weylMonomialBase_det (i j : ι) (hij : i ≠ j) :
    monomialDetHom R ι (weylMonomialBase i j hij) = 1 :=
  weylMonomialBaseUnit_det i j hij 1

theorem torusMonomialBase_det (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialDetHom R ι (torusMonomialBase i j hij u) = 1 :=
  torusMonomialBaseUnit_det i j hij u

def weylMonomialSLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialSL R ι :=
  ⟨weylMonomialBaseUnit i j hij u,
    weylMonomialBaseUnit_det i j hij u⟩

def weylMonomialSL (i j : ι) (hij : i ≠ j) :
    MonomialSL R ι :=
  weylMonomialSLUnit i j hij 1

def torusMonomialSLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialSL R ι :=
  ⟨torusMonomialBaseUnit i j hij u,
    torusMonomialBaseUnit_det i j hij u⟩

def torusMonomialSL (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    MonomialSL R ι :=
  torusMonomialSLUnit i j hij u

@[simp]
theorem weylMonomialSLUnit_coe (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (weylMonomialSLUnit (R := R) i j hij u : MonomialBase Rˣ ι) =
      weylMonomialBaseUnit i j hij u := rfl

@[simp]
theorem torusMonomialSLUnit_coe (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    (torusMonomialSLUnit (R := R) i j hij u : MonomialBase Rˣ ι) =
      torusMonomialBaseUnit i j hij u := rfl

end WeylMonomial

section TorusGL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [Ring R]

def torusGLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) : GL ι R :=
  weylGLUnit i j hij u * weylGLUnit i j hij (-1 : Rˣ)

def torusGL (i j : ι) (hij : i ≠ j) : GL ι R :=
  torusGLUnit i j hij 1

variable {S : Type*} [Ring S]

theorem torusGLUnit_mapRingHom (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    mapRingHom (n := ι) f (torusGLUnit (R := R) i j hij u) =
      torusGLUnit i j hij (Units.map f.toMonoidHom u) := by
  simp only [torusGLUnit, map_mul, weylGLUnit_mapRingHom]
  have h : Units.map f.toMonoidHom (-1 : Rˣ) = (-1 : Sˣ) := by
    apply Units.ext
    simp
  rw [h]

theorem torusGL_mapRingHom (f : R →+* S)
    (i j : ι) (hij : i ≠ j) :
    mapRingHom (n := ι) f (torusGL (R := R) i j hij) =
      torusGL (R := S) i j hij := by
  simp [torusGL, torusGLUnit_mapRingHom]

end TorusGL

section TorusSL

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

def torusSLUnit (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup ι R :=
  weylSLUnit i j hij u * weylSLUnit i j hij (-1 : Rˣ)

def torusSL (i j : ι) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup ι R :=
  torusSLUnit i j hij 1

variable {S : Type*} [CommRing S]

theorem torusSLUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    Matrix.SpecialLinearGroup.map f (torusSLUnit i j hij u) =
      torusSLUnit i j hij (Units.map f.toMonoidHom u) := by
  simp only [torusSLUnit, map_mul, weylSLUnit_map]
  have h : Units.map f.toMonoidHom (-1 : Rˣ) = (-1 : Sˣ) := by
    apply Units.ext
    simp
  rw [h]

theorem torusSL_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.map f (torusSL (R := R) i j hij) =
      torusSL (R := S) i j hij := by
  simp [torusSL, torusSLUnit_map]

end TorusSL

section MonomialNaturality

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

omit [Fintype ι] in
theorem weylMonomialBaseUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialBaseHom (ι := ι) (Units.map f.toMonoidHom)
        (weylMonomialBaseUnit (R := R) i j hij u) =
      weylMonomialBaseUnit i j hij (Units.map f.toMonoidHom u) := by
  apply SemidirectProduct.ext
  · ext k
    by_cases hk_i : k = i
    · simp [hk_i, weylMonomialBaseUnit, weylWeightUnit]
    · by_cases hk_j : k = j
      · simp [hk_j, hij.symm, weylMonomialBaseUnit, weylWeightUnit,
          Units.coe_map_inv]
      · simp [hk_i, hk_j, weylMonomialBaseUnit, weylWeightUnit]
  · rfl

omit [Fintype ι] in
theorem torusMonomialBaseUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialBaseHom (ι := ι) (Units.map f.toMonoidHom)
        (torusMonomialBaseUnit (R := R) i j hij u) =
      torusMonomialBaseUnit i j hij (Units.map f.toMonoidHom u) := by
  apply SemidirectProduct.ext
  · ext k
    by_cases hk_i : k = i
    · simp [hk_i, torusMonomialBaseUnit, torusWeightUnit]
    · by_cases hk_j : k = j
      · simp [hk_j, hij.symm, torusMonomialBaseUnit, torusWeightUnit,
          Units.coe_map_inv]
      · simp [hk_i, hk_j, torusMonomialBaseUnit, torusWeightUnit]
  · rfl

theorem weylMonomialSLUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialSLMap R S ι f (weylMonomialSLUnit i j hij u) =
      weylMonomialSLUnit i j hij (Units.map f.toMonoidHom u) := by
  apply Subtype.ext
  exact weylMonomialBaseUnit_map f i j hij u

theorem torusMonomialSLUnit_map (f : R →+* S)
    (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    monomialSLMap R S ι f (torusMonomialSLUnit i j hij u) =
      torusMonomialSLUnit i j hij (Units.map f.toMonoidHom u) := by
  apply Subtype.ext
  exact torusMonomialBaseUnit_map f i j hij u

end MonomialNaturality

section MonomialProduct

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

omit [Fintype ι] in
theorem torusMonomialBaseUnit_eq_mul (i j : ι) (hij : i ≠ j) (u : Rˣ) :
    torusMonomialBaseUnit (R := R) i j hij u =
      weylMonomialBaseUnit i j hij u *
        weylMonomialBaseUnit i j hij (-1 : Rˣ) := by
  apply SemidirectProduct.ext
  · ext k
    by_cases hk_i : k = i
    · subst hk_i
      simp [torusMonomialBaseUnit, torusWeightUnit,
        weylMonomialBaseUnit, weylWeightUnit, weylPerm,
        SemidirectProduct.mul_left, permute_apply,
        Equiv.swap_apply_left, hij.symm]
    · by_cases hk_j : k = j
      · subst hk_j
        simp [torusMonomialBaseUnit, torusWeightUnit,
          weylMonomialBaseUnit, weylWeightUnit, weylPerm,
          SemidirectProduct.mul_left, permute_apply,
          Equiv.swap_apply_right, hk_i]
      · simp [hk_i, hk_j, torusMonomialBaseUnit, torusWeightUnit,
          weylMonomialBaseUnit, weylWeightUnit, weylPerm,
          SemidirectProduct.mul_left, permute_apply,
          Equiv.swap_apply_of_ne_of_ne]
  · simp [weylMonomialBaseUnit, torusMonomialBaseUnit, weylPerm,
      torusPerm]

end MonomialProduct

end Matrix.GeneralLinearGroup
