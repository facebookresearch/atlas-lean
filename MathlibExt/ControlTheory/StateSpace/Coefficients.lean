/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# State-space coefficients

`ControlTheory.StateSpaceCoeffs` is the coefficient view of a linear
state-space system: continuous linear maps `A`, `B`, `C`, and `D` over
normed spaces. It carries no trajectory semantics.

On finite coordinate spaces, `StateSpaceCoeffs.ofMatrix` builds the
coefficients from matrices by matrix-vector multiplication, and
`StateSpaceCoeffs.toMatrix` extracts the representing matrices in the
canonical bases.
-/

open Matrix

@[expose] public section

namespace ControlTheory

/-- The coefficient record of a linear state-space system: bounded linear
maps `A : X →L[𝕜] X`, `B : U →L[𝕜] X`, `C : X →L[𝕜] Y`, and
`D : U →L[𝕜] Y` over normed spaces. This is only the coefficient view;
it carries no trajectory semantics. -/
structure StateSpaceCoeffs (𝕜 X U Y : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] where
  /-- The state-transition map. -/
  A : X →L[𝕜] X
  /-- The input map. -/
  B : U →L[𝕜] X
  /-- The output map. -/
  C : X →L[𝕜] Y
  /-- The direct feedthrough map. -/
  D : U →L[𝕜] Y

namespace StateSpaceCoeffs

/-- Build state-space coefficients from matrices on finite coordinate
spaces: the maps are matrix-vector multiplication. Empty index types are
allowed. -/
noncomputable def ofMatrix {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) :
    StateSpaceCoeffs 𝕜 (n → 𝕜) (m → 𝕜) (p → 𝕜) where
  A := (Matrix.mulVecLin A).toContinuousLinearMap
  B := (Matrix.mulVecLin B).toContinuousLinearMap
  C := (Matrix.mulVecLin C).toContinuousLinearMap
  D := (Matrix.mulVecLin D).toContinuousLinearMap

/-- The matrices representing coefficients on finite coordinate spaces in
the canonical bases. -/
def toMatrix {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    [DecidableEq n] [DecidableEq m]
    (S : StateSpaceCoeffs 𝕜 (n → 𝕜) (m → 𝕜) (p → 𝕜)) :
    Matrix n n 𝕜 × Matrix n m 𝕜 × Matrix p n 𝕜 × Matrix p m 𝕜 :=
  (LinearMap.toMatrix' S.A.toLinearMap, LinearMap.toMatrix' S.B.toLinearMap,
    LinearMap.toMatrix' S.C.toLinearMap, LinearMap.toMatrix' S.D.toLinearMap)

theorem ofMatrix_A_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) (x : n → 𝕜) :
    (ofMatrix A B C D).A x = A *ᵥ x := by
  simp [ofMatrix]

theorem ofMatrix_B_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) (u : m → 𝕜) :
    (ofMatrix A B C D).B u = B *ᵥ u := by
  simp [ofMatrix]

theorem ofMatrix_C_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) (x : n → 𝕜) :
    (ofMatrix A B C D).C x = C *ᵥ x := by
  simp [ofMatrix]

theorem ofMatrix_D_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) (u : m → 𝕜) :
    (ofMatrix A B C D).D u = D *ᵥ u := by
  simp [ofMatrix]

private theorem toMatrix'_mulVecLin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (M : Matrix a b 𝕜) : LinearMap.toMatrix' (Matrix.mulVecLin M) = M := by
  have h : Matrix.mulVecLin M = Matrix.toLin' M := by
    ext v
    simp
  rw [h]
  exact LinearMap.toMatrix'_toLin' M

/-- Extracting the matrices of matrix-built coefficients returns the
original matrices. -/
theorem toMatrix_ofMatrix {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {n m p : Type*} [Fintype n] [Fintype m] [Fintype p]
    [DecidableEq n] [DecidableEq m]
    (A : Matrix n n 𝕜) (B : Matrix n m 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p m 𝕜) :
    toMatrix (ofMatrix A B C D) = (A, B, C, D) := by
  simp only [toMatrix, ofMatrix]
  simp only [LinearMap.coe_toContinuousLinearMap]
  rw [toMatrix'_mulVecLin, toMatrix'_mulVecLin, toMatrix'_mulVecLin, toMatrix'_mulVecLin]

end StateSpaceCoeffs

end ControlTheory
