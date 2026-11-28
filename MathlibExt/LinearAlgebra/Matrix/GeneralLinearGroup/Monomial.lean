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

public import MathlibExt.GroupTheory.PermutationBilinearMonomialExtension
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Determinant
public import MathlibExt.LinearAlgebra.Matrix.PermutationEntry
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section

open PermutationBilinearCocycle
open Matrix

namespace Matrix
namespace GeneralLinearGroup

universe uR vR wR uι

section Helpers

variable {R : Type uR} [Semiring R] {ι : Type uι} [DecidableEq ι]

/-- Deprecated alias kept for downstream users of the previous
`Matrix.GeneralLinearGroup.permMatrix_entry_eq` API. -/
@[deprecated "Use `Matrix.permMatrix_entry_eq` instead." (since := "2026-10-11")]
theorem permMatrix_entry_eq (σ : Equiv.Perm ι) (i j : ι) :
    (σ.permMatrix R : Matrix ι ι R) i j = if σ i = j then 1 else 0 :=
  _root_.Matrix.permMatrix_entry_eq σ i j

theorem diag_mul_perm_eq (d : ι → R) (τ : Equiv.Perm ι) (i j : ι)
    [Fintype ι] :
    (Matrix.diagonal d * τ.permMatrix R) i j = if τ i = j then d i else 0 := by
  calc (Matrix.diagonal d * τ.permMatrix R) i j
      = d i * (τ.permMatrix R) i j := by rw [Matrix.diagonal_mul]
    _ = d i * (if τ i = j then (1 : R) else 0) := by
      rw [_root_.Matrix.permMatrix_entry_eq]
    _ = if τ i = j then d i else 0 := by
          by_cases h : τ i = j <;> simp [h]

theorem perm_mul_diag_eq (τ : Equiv.Perm ι) (d : ι → R) (i j : ι)
    [Fintype ι] :
    (τ.permMatrix R * Matrix.diagonal d) i j = if τ i = j then d j else 0 := by
  calc (τ.permMatrix R * Matrix.diagonal d) i j
      = (τ.permMatrix R) i j * d j := by rw [Matrix.mul_diagonal]
    _ = (if τ i = j then (1 : R) else 0) * d j := by
      rw [_root_.Matrix.permMatrix_entry_eq]
    _ = if τ i = j then d j else 0 := by
          by_cases h : τ i = j <;> simp [h]

theorem perm_diag_mul_perm_eq (d : ι → R) (σ : Equiv.Perm ι) (i j : ι)
    [Fintype ι] :
    ((σ⁻¹).permMatrix R * Matrix.diagonal d * σ.permMatrix R) i j =
      if i = j then d (σ⁻¹ i) else 0 := by
  classical
  have h_mul : ∀ k : ι,
      (((σ⁻¹).permMatrix R * Matrix.diagonal d) i k) *
        ((σ.permMatrix R) k j) =
        (if σ⁻¹ i = k then d k else 0) * (if σ k = j then (1 : R) else 0) := by
    intro k
    have h1 : ((σ⁻¹).permMatrix R * Matrix.diagonal d) i k =
        if σ⁻¹ i = k then d k else 0 := perm_mul_diag_eq _ _ _ _
    have h2 : (σ.permMatrix R) k j = if σ k = j then (1 : R) else 0 :=
      _root_.Matrix.permMatrix_entry_eq _ _ _
    rw [h1, h2]
  have h_eq : ((σ⁻¹).permMatrix R * Matrix.diagonal d * σ.permMatrix R) i j =
      ∑ k : ι, (if σ⁻¹ i = k then d k else 0) * (if σ k = j then (1 : R) else 0) := by
    calc ((σ⁻¹).permMatrix R * Matrix.diagonal d * σ.permMatrix R) i j
        = ∑ k : ι, (((σ⁻¹).permMatrix R * Matrix.diagonal d) i k) *
          ((σ.permMatrix R) k j) := by
            simp [Matrix.mul_apply]
      _ = _ := by
          apply Fintype.sum_congr
          intro k
          rw [h_mul k]
  rw [h_eq]
  have hs : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
  have h1 : ∀ b : ι, b ≠ σ⁻¹ i →
      (if σ⁻¹ i = b then d b else (0 : R)) * (if σ b = j then (1 : R) else 0) = 0 := by
    intro b hb
    rw [ite_eq_right (Ne.symm hb), zero_mul]
  calc (∑ k : ι, (if σ⁻¹ i = k then d k else 0) * (if σ k = j then (1 : R) else 0))
      = (if σ⁻¹ i = σ⁻¹ i then d (σ⁻¹ i) else 0) *
          (if σ (σ⁻¹ i) = j then 1 else 0) := by
          rw [Fintype.sum_eq_single (σ⁻¹ i) h1]
    _ = if σ (σ⁻¹ i) = j then d (σ⁻¹ i) else 0 := by simp
    _ = if i = j then d (σ⁻¹ i) else 0 := by
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]

end Helpers

/-- Send a tuple of units to its diagonal matrix in the general linear group. -/
def diagonalUnitsHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] : (ι → Rˣ) →* GL ι R :=
  (Units.map (Matrix.diagonalRingHom (n := ι) (α := R)).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom)

@[simp]
theorem coe_diagonalUnitsHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (u : ι → Rˣ) :
    (↑(diagonalUnitsHom R ι u) : Matrix ι ι R) =
      Matrix.diagonal (fun i => (u i : R)) :=
  rfl

/-- Embed permutations in the general linear group using inverse permutation matrices. -/
def permutationUnitsHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] : Equiv.Perm ι →* GL ι R :=
  (Matrix.permMatrixHom (R := R) (n := ι)).toHomUnits

@[simp]
theorem coe_permutationUnitsHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    (↑(permutationUnitsHom R ι σ) : Matrix ι ι R) =
      (σ⁻¹).permMatrix R :=
  rfl

theorem coe_permutationUnitsHom_GL_inv (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    (↑((permutationUnitsHom R ι σ)⁻¹) : Matrix ι ι R) =
      σ.permMatrix R := by
  have h : (permutationUnitsHom R ι σ)⁻¹ =
      permutationUnitsHom R ι σ⁻¹ :=
    (map_inv (permutationUnitsHom R ι) σ).symm
  calc (↑((permutationUnitsHom R ι σ)⁻¹) : Matrix ι ι R)
      = (↑(permutationUnitsHom R ι σ⁻¹) : Matrix ι ι R) := by rw [h]
    _ = (σ⁻¹)⁻¹.permMatrix R := rfl
    _ = σ.permMatrix R := by simp [inv_inv]

theorem diagonalUnitsHom_permute (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) (u : ι → Rˣ) :
    diagonalUnitsHom R ι (permute σ u) =
      permutationUnitsHom R ι σ * diagonalUnitsHom R ι u *
        (permutationUnitsHom R ι σ)⁻¹ := by
  apply Units.ext
  have h_left : ((diagonalUnitsHom R ι (permute σ u)).val : Matrix ι ι R) =
      Matrix.diagonal (fun k => (permute σ u k : Rˣ).val) := by
    simp [coe_diagonalUnitsHom]
  have h_right : ((permutationUnitsHom R ι σ * diagonalUnitsHom R ι u *
      (permutationUnitsHom R ι σ)⁻¹).val : Matrix ι ι R) =
      (σ⁻¹).permMatrix R * Matrix.diagonal (fun k => (u k : Rˣ).val) *
        σ.permMatrix R := by
    simp [coe_diagonalUnitsHom, coe_permutationUnitsHom,
      coe_permutationUnitsHom_GL_inv]
  rw [h_left, h_right]
  ext i j
  simp [permute_apply, perm_diag_mul_perm_eq, Matrix.diagonal_apply]

/-- Realize monomial data as a diagonal unit matrix times an inverse permutation matrix. -/
def monomialMatrixHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] : MonomialBase Rˣ ι →* GL ι R :=
  SemidirectProduct.lift
    (diagonalUnitsHom R ι)
    (permutationUnitsHom R ι)
    (by
      intro σ
      apply MonoidHom.ext
      intro u
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, tupleActionHom_apply,
        MulEquiv.coe_toMonoidHom]
      exact diagonalUnitsHom_permute R ι σ u)

@[simp]
theorem monomialMatrixHom_mk (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (u : ι → Rˣ) (σ : Equiv.Perm ι) :
    monomialMatrixHom R ι ⟨u, σ⟩ =
      diagonalUnitsHom R ι u * permutationUnitsHom R ι σ :=
  rfl

@[simp]
theorem coe_monomialMatrixHom (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (x : MonomialBase Rˣ ι) :
    (↑(monomialMatrixHom R ι x) : Matrix ι ι R) =
      (↑(diagonalUnitsHom R ι x.left) : Matrix ι ι R) *
        (↑(permutationUnitsHom R ι x.right) : Matrix ι ι R) := by
  cases x with
  | mk l r => rfl

theorem coe_monomialMatrixHom_mk (R : Type uR) (ι : Type uι) [Semiring R]
    [DecidableEq ι] [Fintype ι] (u : ι → Rˣ) (σ : Equiv.Perm ι) :
    (↑(monomialMatrixHom R ι ⟨u, σ⟩) : Matrix ι ι R) =
      Matrix.diagonal (fun i => (u i : R)) * (σ⁻¹).permMatrix R := by
  simp

section CoeffNaturality

variable {R : Type uR} {S : Type vR} [Semiring R] [Semiring S]
variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
theorem permMatrix_map (f : R →+* S) (σ : Equiv.Perm ι) :
    (σ.permMatrix R).map f = σ.permMatrix S := by
  ext i j
  simp only [Matrix.map_apply, _root_.Matrix.permMatrix_entry_eq]
  by_cases h : σ i = j <;> simp [h]

theorem permutationUnitsHom_mapRingHom (f : R →+* S) (σ : Equiv.Perm ι) :
    mapRingHom (n := ι) f (permutationUnitsHom R ι σ) =
      permutationUnitsHom S ι σ := by
  apply Units.ext
  simp only [coe_permutationUnitsHom, coe_mapRingHom]
  exact permMatrix_map f σ⁻¹

theorem diagonalUnitsHom_mapRingHom (f : R →+* S) (u : ι → Rˣ) :
    mapRingHom (n := ι) f (diagonalUnitsHom R ι u) =
      diagonalUnitsHom S ι (fun i => Units.map f (u i)) := by
  apply Units.ext
  simp [coe_diagonalUnitsHom, coe_mapRingHom, Matrix.diagonal_map, Units.coe_map]

theorem monomialMatrixHom_mapRingHom (f : R →+* S) :
    (mapRingHom (n := ι) f).comp (monomialMatrixHom R ι) =
      (monomialMatrixHom S ι).comp (monomialBaseHom (ι := ι) (Units.map f)) := by
  apply MonoidHom.ext
  intro x
  cases x with
  | mk u σ =>
    calc mapRingHom _ (monomialMatrixHom R ι ⟨u, σ⟩)
        = mapRingHom _ (diagonalUnitsHom R ι u * permutationUnitsHom R ι σ) := rfl
      _ = _ * _ := by rw [map_mul]
      _ = diagonalUnitsHom S ι (fun i => Units.map f (u i)) *
          permutationUnitsHom S ι σ := by
          rw [diagonalUnitsHom_mapRingHom, permutationUnitsHom_mapRingHom]
      _ = _ := rfl

theorem monomialMatrixHom_mapRingHom_apply (f : R →+* S)
    (x : MonomialBase Rˣ ι) :
    mapRingHom (n := ι) f (monomialMatrixHom R ι x) =
      monomialMatrixHom S ι (monomialBaseHom (ι := ι) (Units.map f) x) :=
  DFunLike.congr_fun (monomialMatrixHom_mapRingHom (f := f)) x

end CoeffNaturality

/-- The determinant homomorphism on monomial data over a commutative ring. -/
def monomialDetHom (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] : MonomialBase Rˣ ι →* Rˣ :=
  (Matrix.GeneralLinearGroup.det (n := ι)).comp (monomialMatrixHom R ι)

theorem det_diagonalUnitsHom (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (u : ι → Rˣ) :
    Matrix.GeneralLinearGroup.det (diagonalUnitsHom R ι u) =
      Finset.univ.prod (fun i => u i) := by
  apply Units.ext
  simp [coe_diagonalUnitsHom, Matrix.det_diagonal]

theorem det_permutationUnitsHom (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (σ : Equiv.Perm ι) :
    Matrix.GeneralLinearGroup.det (permutationUnitsHom R ι σ) =
      Units.map (Int.castRingHom R) (Equiv.Perm.sign σ) := by
  apply Units.ext
  change ((σ⁻¹).permMatrix R).det =
    (Units.map (Int.castRingHom R) (Equiv.Perm.sign σ)).val
  calc ((σ⁻¹).permMatrix R).det
      = (Equiv.Perm.sign (σ⁻¹) : R) := Matrix.det_permutation _
    _ = (Equiv.Perm.sign σ : R) := by rw [Equiv.Perm.sign_inv]
    _ = (Units.map (Int.castRingHom R) (Equiv.Perm.sign σ)).val := by
        simp [Units.coe_map]

theorem monomialDetHom_mk (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (u : ι → Rˣ) (σ : Equiv.Perm ι) :
    monomialDetHom R ι ⟨u, σ⟩ =
      (Finset.univ.prod (fun i => u i)) *
        Units.map (Int.castRingHom R) (Equiv.Perm.sign σ) := by
  calc monomialDetHom R ι ⟨u, σ⟩
      = Matrix.GeneralLinearGroup.det
          (diagonalUnitsHom R ι u * permutationUnitsHom R ι σ) := rfl
    _ = _ := by rw [map_mul, det_diagonalUnitsHom, det_permutationUnitsHom]

theorem monomialDetHom_coe (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (x : MonomialBase Rˣ ι) :
    (monomialDetHom R ι x : R) =
      (Finset.univ.prod (fun i => (x.left i : R))) *
        (Equiv.Perm.sign x.right : R) := by
  cases x with
  | mk u σ =>
    calc (monomialDetHom R ι ⟨u, σ⟩ : R)
        = ((Finset.univ.prod (fun i => u i)) *
          Units.map (Int.castRingHom R) (Equiv.Perm.sign σ) : Rˣ) := by
            rw [monomialDetHom_mk]
      _ = _ := by simp [Units.val_mul, Units.coe_map]

/-- The subgroup of monomial data with determinant one. -/
abbrev MonomialSL (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] := (monomialDetHom R ι).ker

/-- The inclusion of the determinant kernel into the full monomial data group. -/
def monomialSLToMonomialBase (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] : MonomialSL R ι →* MonomialBase Rˣ ι :=
  Subgroup.subtype _

/-- Realize monomial data with determinant one as a special linear matrix. -/
def monomialSLHom (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] : MonomialSL R ι →* Matrix.SpecialLinearGroup ι R where
  toFun x :=
    ⟨(monomialMatrixHom R ι (x : MonomialBase Rˣ ι)).val,
      by
        have hdet : monomialDetHom R ι (x : MonomialBase Rˣ ι) = 1 := x.prop
        have h1 :
            Matrix.GeneralLinearGroup.det
              (monomialMatrixHom R ι (x : MonomialBase Rˣ ι)) = 1 := hdet
        have : (Matrix.GeneralLinearGroup.det
            (monomialMatrixHom R ι (x : MonomialBase Rˣ ι)) : Rˣ).val = 1 := by
          rw [h1]
          rfl
        exact this⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change (monomialMatrixHom R ι ((x * y : MonomialSL R ι).1)).val =
      (monomialMatrixHom R ι x.1).val * (monomialMatrixHom R ι y.1).val
    rw [Subgroup.coe_mul]
    have h_mul :
        monomialMatrixHom R ι (x.1 * y.1) =
          monomialMatrixHom R ι x.1 * monomialMatrixHom R ι y.1 :=
      map_mul (monomialMatrixHom R ι) x.1 y.1
    exact congrArg Units.val h_mul

@[simp]
theorem coe_monomialSLHom (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (x : MonomialSL R ι) :
    (↑(monomialSLHom R ι x) : Matrix ι ι R) =
      (↑(monomialMatrixHom R ι (x : MonomialBase Rˣ ι)) : Matrix ι ι R) :=
  rfl

@[simp]
theorem monomialSLHom_toGL (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] (x : MonomialSL R ι) :
    (monomialSLHom R ι x : Matrix.GeneralLinearGroup ι R) =
      monomialMatrixHom R ι (x : MonomialBase Rˣ ι) := by
  apply Units.ext
  rfl

variable {R : Type uR} {S : Type vR} [CommRing R] [CommRing S]
variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

theorem monomialDetHom_mapRingHom {R : Type uR} {S : Type vR} {ι : Type uι}
    [CommRing R] [CommRing S] [DecidableEq ι] [Fintype ι]
    (f : R →+* S) (x : MonomialBase Rˣ ι) :
    Units.map f (monomialDetHom R ι x) =
      monomialDetHom S ι (monomialBaseHom (ι := ι) (Units.map f) x) := by
  apply Units.ext
  have h1 : (monomialDetHom R ι x : R) =
      (monomialMatrixHom R ι x).val.det := by
    simp [monomialDetHom, GeneralLinearGroup.val_det_apply]
  have h2 : (monomialDetHom S ι (monomialBaseHom (Units.map f) x) : S) =
      (monomialMatrixHom S ι (monomialBaseHom (Units.map f) x)).val.det := by
    simp [monomialDetHom, GeneralLinearGroup.val_det_apply]
  calc (Units.map f (monomialDetHom R ι x)).val
      = f (monomialDetHom R ι x : R) := by simp [Units.coe_map]
    _ = f ((monomialMatrixHom R ι x).val.det) := by rw [h1]
    _ = (f.mapMatrix (monomialMatrixHom R ι x).val).det := by
        rw [RingHom.map_det]
    _ = (((monomialMatrixHom R ι x).val).map f).det := rfl
    _ = ((mapRingHom (n := ι) f (monomialMatrixHom R ι x)).val.det) := by
        rw [← coe_mapRingHom]
    _ = ((monomialMatrixHom S ι
          (monomialBaseHom (Units.map f) x)).val.det) := by
        rw [monomialMatrixHom_mapRingHom_apply]
    _ = (monomialDetHom S ι (monomialBaseHom (Units.map f) x)).val := by
        rw [h2]

/-- Map monomial data with determinant one along a coefficient ring homomorphism,
keeping the permutation unchanged. -/
def monomialSLMap (R : Type uR) (S : Type vR) (ι : Type uι) [CommRing R]
    [CommRing S] [DecidableEq ι] [Fintype ι] (f : R →+* S) :
    MonomialSL R ι →* MonomialSL S ι where
  toFun x :=
    ⟨monomialBaseHom (ι := ι) (Units.map f) (x : MonomialBase Rˣ ι),
      by
        calc monomialDetHom S ι
              (monomialBaseHom (Units.map f) (x : MonomialBase Rˣ ι))
            = Units.map f (monomialDetHom R ι (x : MonomialBase Rˣ ι)) := by
                rw [← monomialDetHom_mapRingHom]
          _ = 1 := by rw [x.prop, map_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [monomialBaseHom, mapTuple_one]
  map_mul' x y := by
    apply Subtype.ext
    simp

@[simp]
theorem coe_monomialSLMap (R : Type uR) (S : Type vR) (ι : Type uι) [CommRing R]
    [CommRing S] [DecidableEq ι] [Fintype ι] (f : R →+* S) (x : MonomialSL R ι) :
    (↑(monomialSLMap R S ι f x) : MonomialBase Sˣ ι) =
      monomialBaseHom (ι := ι) (Units.map f) (x : MonomialBase Rˣ ι) :=
  rfl

theorem monomialSLMap_id (R : Type uR) (ι : Type uι) [CommRing R]
    [DecidableEq ι] [Fintype ι] :
    monomialSLMap R R ι (RingHom.id R) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  have hid : monomialBaseHom (ι := ι) (MonoidHom.id (Rˣ)) (x : MonomialBase Rˣ ι) =
      (x : MonomialBase Rˣ ι) := by
    have h := monomialBaseHom_id (A := Rˣ) (ι := ι)
    exact DFunLike.congr_fun h (x : MonomialBase Rˣ ι)
  have hmap : Units.map (RingHom.id R : R →+* R) = MonoidHom.id (Rˣ) := rfl
  calc monomialBaseHom (ι := ι) (Units.map (RingHom.id R)) (x : MonomialBase Rˣ ι)
      = monomialBaseHom (ι := ι) (MonoidHom.id (Rˣ)) (x : MonomialBase Rˣ ι) := by
          rw [hmap]
    _ = _ := hid

theorem monomialSLMap_comp (R : Type uR) (S : Type vR) (T : Type wR) (ι : Type uι)
    [CommRing R] [CommRing S] [CommRing T] [DecidableEq ι] [Fintype ι]
    (f : R →+* S) (g : S →+* T) :
    monomialSLMap R T ι (g.comp f) =
      (monomialSLMap S T ι g).comp (monomialSLMap R S ι f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_monomialSLMap]
  have h_units : Units.map (g.comp f).toMonoidHom =
      (Units.map g.toMonoidHom).comp (Units.map f.toMonoidHom) := by
    calc Units.map (g.comp f).toMonoidHom
        = Units.map (g.toMonoidHom.comp f.toMonoidHom) := rfl
      _ = (Units.map g.toMonoidHom).comp (Units.map f.toMonoidHom) :=
          Units.map_comp f.toMonoidHom g.toMonoidHom
  change monomialBaseHom (ι := ι) (Units.map (g.comp f).toMonoidHom)
      (x : MonomialBase Rˣ ι) =
    ((monomialBaseHom (ι := ι) (Units.map g.toMonoidHom)).comp
      (monomialBaseHom (ι := ι) (Units.map f.toMonoidHom))) (x : MonomialBase Rˣ ι)
  rw [h_units, monomialBaseHom_comp]

/-- Conjugation by the actual permutation unit is the original reindexing
of both matrix indices, over arbitrary semirings. This is a whole matrix
formula, using the existing partial-equivalence multiplication laws. -/
theorem permutationUnitsHom_conjugate
    (R : Type uR) [Semiring R] (Index : Type uι)
    [DecidableEq Index] [Fintype Index] (σ : Equiv.Perm Index)
    (g : GL Index R) :
    permutationUnitsHom R Index σ * g * (permutationUnitsHom R Index σ)⁻¹ =
      reindexMulEquiv σ g := by
  apply Units.ext
  simp only [Units.val_mul, coe_permutationUnitsHom,
    coe_permutationUnitsHom_GL_inv, coe_reindexMulEquiv]
  change (σ⁻¹).toPEquiv.toMatrix * (↑g : Matrix Index Index R) *
      σ.toPEquiv.toMatrix = Matrix.reindex σ σ (↑g : Matrix Index Index R)
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- Reindexing the actual permutation unit is the permutation unit of the
same conjugated index permutation, across independent index universes. -/
theorem permutationUnitsHom_reindex
    (R : Type uR) [Semiring R] {Index₁ : Type uι} {Index₂ : Type vR}
    [DecidableEq Index₁] [DecidableEq Index₂] [Fintype Index₁] [Fintype Index₂]
    (e : Index₁ ≃ Index₂) (σ : Equiv.Perm Index₁) :
    reindexMulEquiv e (permutationUnitsHom R Index₁ σ) =
      permutationUnitsHom R Index₂ (e.permCongr σ) := by
  have hinv : (e.permCongr σ)⁻¹ = e.permCongr σ⁻¹ :=
    (map_inv e.permCongrHom σ).symm
  apply Units.ext
  rw [coe_reindexMulEquiv, coe_permutationUnitsHom, coe_permutationUnitsHom, hinv]
  ext i j
  dsimp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [Matrix.permMatrix_entry_eq,
    Matrix.permMatrix_entry_eq, Equiv.permCongr_apply]
  have he : e (σ⁻¹ (e.symm i)) = j ↔ σ⁻¹ (e.symm i) = e.symm j := by
    constructor
    · intro h
      have hh := congrArg e.symm h
      simpa only [e.symm_apply_apply] using hh
    · intro h
      exact (congrArg e h).trans (e.apply_symm_apply j)
  exact if_congr he.symm rfl rfl

/-- The permutation unit of a sum permutation is the original finite
two-block diagonal of both permutation units. -/
theorem permutationUnitsHom_sumCongr
    (R : Type uR) [Semiring R] (Index₁ : Type uι) (Index₂ : Type vR)
    [DecidableEq Index₁] [DecidableEq Index₂] [Fintype Index₁] [Fintype Index₂]
    (σ : Equiv.Perm Index₁) (τ : Equiv.Perm Index₂) :
    permutationUnitsHom R (Index₁ ⊕ Index₂) (Equiv.sumCongr σ τ) =
      blockDiagonalHom Index₁ Index₂ R
        (permutationUnitsHom R Index₁ σ, permutationUnitsHom R Index₂ τ) := by
  apply Units.ext
  rw [coe_permutationUnitsHom, coe_blockDiagonalHom,
    coe_permutationUnitsHom, coe_permutationUnitsHom]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.permMatrix_entry_eq, Equiv.Perm.inv_def, Equiv.sumCongr_symm]

end GeneralLinearGroup
end Matrix

universe uActive vInactive uCoeff

namespace Matrix.GeneralLinearGroup

/-- Reindexing by an original permutation fixing every active index
leaves the entire active matrix block unchanged. The inactive block is
the actual identity, not a supplied centralizer witness. -/
public theorem reindex_blockDiagonalOne_of_fixed_left
    {Active : Type uActive} {Inactive : Type vInactive}
    [DecidableEq Active] [DecidableEq Inactive] [Fintype Active] [Fintype Inactive]
    (R : Type uCoeff) [Semiring R] (σ : Equiv.Perm (Active ⊕ Inactive))
    (hfix : ∀ i : Active, σ (Sum.inl i) = Sum.inl i)
    (g : GL Active R) :
    reindexMulEquiv σ (blockDiagonalOne Active Inactive R g) =
      blockDiagonalOne Active Inactive R g := by
  have hleft (i : Active) : σ.symm (Sum.inl i) = Sum.inl i :=
    (congrArg σ.symm (hfix i)).symm.trans (σ.symm_apply_apply (Sum.inl i))
  have hright (i : Inactive) : ∃ j : Inactive, σ.symm (Sum.inr i) = Sum.inr j := by
    have hpreimage :
        ∀ q : Active ⊕ Inactive, σ q = Sum.inr i →
          ∃ j : Inactive, q = Sum.inr j := by
      intro q hq
      rcases q with a | b
      · have he : Sum.inl a = Sum.inr i :=
          (hfix a).symm.trans hq
        cases he
      · exact ⟨b, rfl⟩
    exact hpreimage (σ.symm (Sum.inr i))
      (σ.apply_symm_apply (Sum.inr i))
  apply Units.ext
  simp only [coe_reindexMulEquiv, coe_blockDiagonalOne]
  ext i j
  dsimp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [hleft i, hleft j]
  · obtain ⟨j', hj⟩ := hright j
    rw [hleft i, hj]
    rfl
  · obtain ⟨i', hi⟩ := hright i
    rw [hi, hleft j]
    rfl
  · obtain ⟨i', hi⟩ := hright i
    obtain ⟨j', hj⟩ := hright j
    rw [hi, hj]
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    have he : i' = j' ↔ i = j := by
      constructor
      · intro h
        exact Sum.inr.inj (σ.symm.injective
          (hi.trans ((congrArg Sum.inr h).trans hj.symm)))
      · intro h
        cases h
        exact Sum.inr.inj (hi.symm.trans hj)
    exact if_congr he rfl rfl

/-- The actual permutation unit fixing the whole active block commutes
with every original active general-linear matrix. This is a full matrix
family equation over every semiring, not elementary-subgroup membership
or pointwise homotopy information. -/
public theorem commute_blockDiagonalOne_permutation_of_fixed_left
    {Active : Type uActive} {Inactive : Type vInactive}
    [DecidableEq Active] [DecidableEq Inactive] [Fintype Active] [Fintype Inactive]
    (R : Type uCoeff) [Semiring R] (σ : Equiv.Perm (Active ⊕ Inactive))
    (hfix : ∀ i : Active, σ (Sum.inl i) = Sum.inl i)
    (g : GL Active R) :
    Commute (blockDiagonalOne Active Inactive R g)
      (permutationUnitsHom R (Active ⊕ Inactive) σ) := by
  let q := permutationUnitsHom R (Active ⊕ Inactive) σ
  let b := blockDiagonalOne Active Inactive R g
  have hc : q * b * q⁻¹ = b :=
    (permutationUnitsHom_conjugate R (Active ⊕ Inactive) σ b).trans
      (reindex_blockDiagonalOne_of_fixed_left R σ hfix g)
  have h := congrArg (fun z : GL (Active ⊕ Inactive) R => z * q) hc
  have he : q * b = b * q := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  exact he.symm

end Matrix.GeneralLinearGroup
