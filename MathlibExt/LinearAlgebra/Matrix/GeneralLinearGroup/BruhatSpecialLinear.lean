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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousBruhat
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.GeneralLinearEquiv
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Determinant
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

section UpperToSL

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

namespace UpperElementary

/-- Inclusion `U_ι(R) →* SL_ι(R)` via `det = 1` from elementary subgroup. -/
def toSLHom : upperElementarySubgroup ι R →* Matrix.SpecialLinearGroup ι R where
  toFun g :=
    ⟨(g : GL ι R).val,
      by
        have hMem : (g : GL ι R) ∈ elementarySubgroup ι R :=
          upperElementarySubgroup_le_elementarySubgroup g.2
        have hDet : det (g : GL ι R) = 1 :=
          det_of_mem_elementarySubgroup hMem
        have hVal : (det (g : GL ι R)).val = 1 := by
          rw [hDet]
          rfl
        exact hVal⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    rfl

@[simp]
theorem coe_toSLHom (g : upperElementarySubgroup ι R) :
    (↑(toSLHom (R := R) g) : Matrix ι ι R) =
      (↑(g : GL ι R) : Matrix ι ι R) :=
  rfl

@[simp]
theorem toGL_toSLHom (g : upperElementarySubgroup ι R) :
    (Matrix.SpecialLinearGroup.toGL (toSLHom g) : GL ι R) =
      (g : GL ι R) := by
  apply Units.ext
  rfl

theorem toSLHom_mapRingHom (f : R →+* S)
    (g : upperElementarySubgroup ι R) :
    Matrix.SpecialLinearGroup.map f (toSLHom g) =
      toSLHom (mapRingHom (ι := ι) f g) := by
  apply Subtype.ext
  rfl

end UpperElementary

end UpperToSL

section SLBruhat

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]
variable {K : Type*} [Field K]

open Matrix.SpecialLinearGroup

/-- Bundled Bruhat decomposition for `g : SL_ι(F)` with upper-elementary
left/right and middle `MonomialSL`. Both GL and SL factorizations are recorded. -/
structure SpecialLinearBruhatDecomposition
    (g : Matrix.SpecialLinearGroup ι F) where
  left : upperElementarySubgroup ι F
  middle : MonomialSL F ι
  right : upperElementarySubgroup ι F
  factorizationGL :
    (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
      (left : GL ι F) *
        (monomialMatrixHom F ι (middle : MonomialBase Fˣ ι)) *
        (right : GL ι F)
  factorizationSL :
    g = UpperElementary.toSLHom left *
      monomialSLHom F ι middle *
      UpperElementary.toSLHom right

namespace SpecialLinearBruhatDecomposition

variable {g : Matrix.SpecialLinearGroup ι F}

theorem val_eq (d : SpecialLinearBruhatDecomposition g) :
    (g : Matrix ι ι F) =
      (d.left : GL ι F).val *
        (monomialMatrixHom F ι (d.middle : MonomialBase Fˣ ι)).val *
        (d.right : GL ι F).val := by
  have hGL := d.factorizationGL
  have h1 : ((Matrix.SpecialLinearGroup.toGL g : GL ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F) := rfl
  calc (g : Matrix ι ι F) =
      ((Matrix.SpecialLinearGroup.toGL g : GL ι F) : Matrix ι ι F) := h1.symm
    _ = ((d.left : GL ι F) *
          (monomialMatrixHom F ι (d.middle : MonomialBase Fˣ ι)) *
          (d.right : GL ι F) : GL ι F).val := by rw [hGL]
    _ = _ := by simp

theorem middle_det_one (d : SpecialLinearBruhatDecomposition g) :
    monomialDetHom F ι (d.middle : MonomialBase Fˣ ι) = 1 :=
  d.middle.2

theorem middle_GL_det_one (d : SpecialLinearBruhatDecomposition g) :
    det (monomialMatrixHom F ι (d.middle : MonomialBase Fˣ ι)) = 1 :=
  d.middle.2

end SpecialLinearBruhatDecomposition

/-- Canonical (choice-based) SL Bruhat decomposition from heterogeneous one. -/
noncomputable def specialLinearBruhatDecomposition
    (g : Matrix.SpecialLinearGroup ι F) :
    SpecialLinearBruhatDecomposition g := by
  classical
  let eGL : GL ι F := Matrix.SpecialLinearGroup.toGL g
  let eEquiv : GeneralLinearEquiv ι ι F := GeneralLinearEquiv.ofGL eGL
  let d := GeneralLinearEquiv.heterogeneousBruhatDecomposition eEquiv
  let base : MonomialBase Fˣ ι := ⟨d.weights, d.perm⟩
  let monomialGL : GL ι F := monomialMatrixHom F ι base
  have hMonoVal :
      (GeneralLinearEquiv.monomialEquiv d.weights d.perm).val =
        (monomialMatrixHom F ι base : Matrix ι ι F) := by
    have h := GeneralLinearEquiv.monomialEquiv_eq_monomialMatrixHom
      (R := F) d.weights d.perm
    exact h
  have hValEq : eGL.val =
      (d.left : GL ι F).val * monomialGL.val * (d.right : GL ι F).val := by
    have hDecompVal := d.val_eq
    calc eGL.val = eEquiv.val := rfl
      _ = (d.left : GL ι F).val *
            (GeneralLinearEquiv.monomialEquiv d.weights d.perm).val *
            (d.right : GL ι F).val := hDecompVal
      _ = (d.left : GL ι F).val * monomialGL.val *
            (d.right : GL ι F).val := by rw [hMonoVal]
  have hGLEq : eGL =
      (d.left : GL ι F) * monomialGL * (d.right : GL ι F) := by
    apply Units.ext
    simp only [coe_mul, hValEq]
  have hDet_eGL : det eGL = 1 := by
    apply Units.ext
    calc (det eGL).val = (eGL : Matrix ι ι F).det := rfl
      _ = (g : Matrix ι ι F).det := rfl
      _ = 1 := g.2
  have hDetLeft : det (d.left : GL ι F) = 1 := by
    have hMem : (d.left : GL ι F) ∈ elementarySubgroup ι F :=
      upperElementarySubgroup_le_elementarySubgroup d.left.2
    exact det_of_mem_elementarySubgroup hMem
  have hDetRight : det (d.right : GL ι F) = 1 := by
    have hMem : (d.right : GL ι F) ∈ elementarySubgroup ι F :=
      upperElementarySubgroup_le_elementarySubgroup d.right.2
    exact det_of_mem_elementarySubgroup hMem
  have hDetMono : det monomialGL = 1 := by
    have hProd :
        det ((d.left : GL ι F) * monomialGL * (d.right : GL ι F)) =
          det (d.left : GL ι F) * det monomialGL *
            det (d.right : GL ι F) := by
      simp [map_mul]
    calc det monomialGL = 1 * det monomialGL * 1 := by simp
      _ = det (d.left : GL ι F) * det monomialGL *
            det (d.right : GL ι F) := by
        rw [hDetLeft, hDetRight]
      _ = det ((d.left : GL ι F) * monomialGL *
            (d.right : GL ι F)) := hProd.symm
      _ = det eGL := by rw [← hGLEq]
      _ = 1 := hDet_eGL
  have hBaseDet : monomialDetHom F ι base = 1 := hDetMono
  let middle : MonomialSL F ι := ⟨base, hBaseDet⟩
  have hGLEqMiddle : eGL =
      (d.left : GL ι F) *
        (monomialMatrixHom F ι (middle : MonomialBase Fˣ ι)) *
        (d.right : GL ι F) := hGLEq
  have hToGLLeft :
      (Matrix.SpecialLinearGroup.toGL
        (UpperElementary.toSLHom d.left) : GL ι F) =
        (d.left : GL ι F) :=
    UpperElementary.toGL_toSLHom d.left
  have hToGLRight :
      (Matrix.SpecialLinearGroup.toGL
        (UpperElementary.toSLHom d.right) : GL ι F) =
        (d.right : GL ι F) :=
    UpperElementary.toGL_toSLHom d.right
  have hToGLMiddle :
      (Matrix.SpecialLinearGroup.toGL
        (monomialSLHom F ι middle) : GL ι F) =
        monomialMatrixHom F ι (middle : MonomialBase Fˣ ι) := by
    rw [monomialSLHom_toGL]
  have hToGLProd :
      Matrix.SpecialLinearGroup.toGL
          (UpperElementary.toSLHom d.left *
            monomialSLHom F ι middle *
            UpperElementary.toSLHom d.right) =
        (d.left : GL ι F) *
          (monomialMatrixHom F ι (middle : MonomialBase Fˣ ι)) *
          (d.right : GL ι F) := by
    simp [map_mul, hToGLLeft, hToGLMiddle, hToGLRight]
  have hSLEq : g =
      UpperElementary.toSLHom d.left *
        monomialSLHom F ι middle *
        UpperElementary.toSLHom d.right := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    calc Matrix.SpecialLinearGroup.toGL g = eGL := rfl
      _ = (d.left : GL ι F) *
            (monomialMatrixHom F ι (middle : MonomialBase Fˣ ι)) *
            (d.right : GL ι F) := hGLEqMiddle
      _ = Matrix.SpecialLinearGroup.toGL
            (UpperElementary.toSLHom d.left *
              monomialSLHom F ι middle *
              UpperElementary.toSLHom d.right) := hToGLProd.symm
  exact
    { left := d.left
      middle := middle
      right := d.right
      factorizationGL := hGLEqMiddle
      factorizationSL := hSLEq }

theorem exists_specialLinearBruhatDecomposition
    (g : Matrix.SpecialLinearGroup ι F) :
    ∃ (left : upperElementarySubgroup ι F) (middle : MonomialSL F ι)
      (right : upperElementarySubgroup ι F),
      (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
          (left : GL ι F) *
            (monomialMatrixHom F ι (middle : MonomialBase Fˣ ι)) *
            (right : GL ι F) ∧
        g = UpperElementary.toSLHom left *
          monomialSLHom F ι middle *
          UpperElementary.toSLHom right := by
  let d := specialLinearBruhatDecomposition g
  exact ⟨d.left, d.middle, d.right, d.factorizationGL, d.factorizationSL⟩

/-- The selected left upper-elementary factor of the original special linear matrix. -/
noncomputable def bruhatLeft
    (g : Matrix.SpecialLinearGroup ι F) : upperElementarySubgroup ι F :=
  (specialLinearBruhatDecomposition g).left

/-- The selected determinant-one monomial factor of the original special linear matrix. -/
noncomputable def bruhatMiddle
    (g : Matrix.SpecialLinearGroup ι F) : MonomialSL F ι :=
  (specialLinearBruhatDecomposition g).middle

/-- The selected right upper-elementary factor of the original special linear matrix. -/
noncomputable def bruhatRight
    (g : Matrix.SpecialLinearGroup ι F) : upperElementarySubgroup ι F :=
  (specialLinearBruhatDecomposition g).right

theorem bruhat_factorizationGL
    (g : Matrix.SpecialLinearGroup ι F) :
    (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
      (bruhatLeft g : GL ι F) *
        (monomialMatrixHom F ι (bruhatMiddle g : MonomialBase Fˣ ι)) *
        (bruhatRight g : GL ι F) :=
  (specialLinearBruhatDecomposition g).factorizationGL

theorem bruhat_factorizationSL
    (g : Matrix.SpecialLinearGroup ι F) :
    g = UpperElementary.toSLHom (bruhatLeft g) *
      monomialSLHom F ι (bruhatMiddle g) *
      UpperElementary.toSLHom (bruhatRight g) :=
  (specialLinearBruhatDecomposition g).factorizationSL

omit [LinearOrder ι] in
theorem toGL_map (f : F →+* K)
    (g : Matrix.SpecialLinearGroup ι F) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
        (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rfl

omit [LinearOrder ι] in
theorem map_monomialSLHom (f : F →+* K)
    (x : MonomialSL F ι) :
    Matrix.SpecialLinearGroup.map f (monomialSLHom F ι x) =
      monomialSLHom K ι (monomialSLMap F K ι f x) := by
  apply Subtype.ext
  have h := monomialMatrixHom_mapRingHom_apply (R := F) (S := K)
    (f := f) (x := (x : MonomialBase Fˣ ι))
  have hMat : ((Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
      (monomialMatrixHom F ι (x : MonomialBase Fˣ ι)) : GL ι K) : Matrix ι ι K) =
      ((monomialMatrixHom K ι
        (monomialBaseHom (ι := ι) (Units.map f)
          (x : MonomialBase Fˣ ι)) : GL ι K) : Matrix ι ι K) :=
    congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h
  calc ((Matrix.SpecialLinearGroup.map f (monomialSLHom F ι x) :
        Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) =
      ((monomialMatrixHom F ι (x : MonomialBase Fˣ ι) : GL ι F).val.map f) := rfl
    _ = ((Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
          (monomialMatrixHom F ι (x : MonomialBase Fˣ ι)) : GL ι K) :
          Matrix ι ι K) := rfl
    _ = ((monomialMatrixHom K ι
          (monomialBaseHom (ι := ι) (Units.map f)
            (x : MonomialBase Fˣ ι)) : GL ι K) : Matrix ι ι K) := hMat
    _ = ((monomialSLHom K ι (monomialSLMap F K ι f x) :
          Matrix.SpecialLinearGroup ι K) : Matrix ι ι K) := rfl

/-- Map a given SL Bruhat decomposition along `f : F →+* K`. This is
functorial on the decomposition, but the canonical choice
`specialLinearBruhatDecomposition` is not itself natural. -/
noncomputable def SpecialLinearBruhatDecomposition.map
    (f : F →+* K) {g : Matrix.SpecialLinearGroup ι F}
    (d : SpecialLinearBruhatDecomposition g) :
    SpecialLinearBruhatDecomposition (Matrix.SpecialLinearGroup.map f g) where
  left := UpperElementary.mapRingHom f d.left
  middle := monomialSLMap F K ι f d.middle
  right := UpperElementary.mapRingHom f d.right
  factorizationGL := by
    have hOrig := d.factorizationGL
    have hToGLMap : Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map f g) =
        Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
          (Matrix.SpecialLinearGroup.toGL g) := toGL_map f g
    calc (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map f g) : GL ι K) =
        Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
          (Matrix.SpecialLinearGroup.toGL g) := hToGLMap
      _ = Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
            ((d.left : GL ι F) *
              (monomialMatrixHom F ι (d.middle : MonomialBase Fˣ ι)) *
              (d.right : GL ι F)) := by rw [hOrig]
      _ = (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f (d.left : GL ι F)) *
            (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
              (monomialMatrixHom F ι (d.middle : MonomialBase Fˣ ι))) *
            (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f
              (d.right : GL ι F)) := by simp [map_mul]
      _ = (UpperElementary.mapRingHom f d.left : GL ι K) *
            (monomialMatrixHom K ι
              (monomialBaseHom (ι := ι) (Units.map f)
                (d.middle : MonomialBase Fˣ ι))) *
            (UpperElementary.mapRingHom f d.right : GL ι K) := by
          simp only [UpperElementary.coe_mapRingHom,
            monomialMatrixHom_mapRingHom_apply]
      _ = (UpperElementary.mapRingHom f d.left : GL ι K) *
            (monomialMatrixHom K ι
              ((monomialSLMap F K ι f d.middle : MonomialSL K ι) :
                MonomialBase Kˣ ι)) *
            (UpperElementary.mapRingHom f d.right : GL ι K) := rfl
  factorizationSL := by
    have hOrigSL := d.factorizationSL
    calc Matrix.SpecialLinearGroup.map f g =
        Matrix.SpecialLinearGroup.map f
          (UpperElementary.toSLHom d.left *
            monomialSLHom F ι d.middle *
            UpperElementary.toSLHom d.right) :=
          congrArg (Matrix.SpecialLinearGroup.map f) hOrigSL
      _ = Matrix.SpecialLinearGroup.map f (UpperElementary.toSLHom d.left) *
            Matrix.SpecialLinearGroup.map f (monomialSLHom F ι d.middle) *
            Matrix.SpecialLinearGroup.map f (UpperElementary.toSLHom d.right) := by
          simp [map_mul]
      _ = UpperElementary.toSLHom (UpperElementary.mapRingHom f d.left) *
            monomialSLHom K ι (monomialSLMap F K ι f d.middle) *
            UpperElementary.toSLHom (UpperElementary.mapRingHom f d.right) := by
          rw [UpperElementary.toSLHom_mapRingHom, map_monomialSLHom,
            UpperElementary.toSLHom_mapRingHom]

@[simp]
theorem SpecialLinearBruhatDecomposition.map_left
    (f : F →+* K) {g : Matrix.SpecialLinearGroup ι F}
    (d : SpecialLinearBruhatDecomposition g) :
    (d.map f).left = UpperElementary.mapRingHom f d.left := rfl

@[simp]
theorem SpecialLinearBruhatDecomposition.map_middle
    (f : F →+* K) {g : Matrix.SpecialLinearGroup ι F}
    (d : SpecialLinearBruhatDecomposition g) :
    (d.map f).middle = monomialSLMap F K ι f d.middle := rfl

@[simp]
theorem SpecialLinearBruhatDecomposition.map_right
    (f : F →+* K) {g : Matrix.SpecialLinearGroup ι F}
    (d : SpecialLinearBruhatDecomposition g) :
    (d.map f).right = UpperElementary.mapRingHom f d.right := rfl

end SLBruhat

end Matrix.GeneralLinearGroup
