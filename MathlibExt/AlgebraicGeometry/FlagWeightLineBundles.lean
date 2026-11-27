/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchubertDiagonalFamilies
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Homogeneous weight lines with actual adapted-frame transitions

An adapted frame is an actual invertible matrix sending the standard
coordinate flag to the given native flag. A weight line is an actual
invertible module sheaf, with its trivializing section in every adapted
frame. Sections pull back by the native module pullback, and change of an
upper triangular frame acts by the literal inverse weight character. These
conditions determine the line globally; unrelated fibrewise isomorphisms
would not suffice.

Convention: positive fundamental weight gives the dual determinant of the
tautological subspace, hence the Plücker O(1). This is the normalization of
Brion, math/0410240v1, Proposition 1.4.3 and the Plücker discussion after
Definition 1.4.4. The preceding displayed associated-quotient action in v1
uses the opposite character sign; the inverse character here records the
adaptation needed for its positive Chevalley coefficients.

Native matrix, pullback and tilde definitions are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0); imported ordinary
tensor/pullback support retains its Stacks/Mathlib credits.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FlagWeightLineBundles

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralFlagSchemes SchubertDiagonalFamilies LineBundleTaskContracts
open CoherentCurveLinearSeries
open scoped TensorProduct

def matrixLinear (A : CommAlgCat.{0} ℂ) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) A) :
    ExtendedSpace A n →ₗ[A] ExtendedSpace A n :=
  let e := TensorProduct.piScalarRight ℂ A A (Fin n)
  e.symm.toLinearMap ∘ₗ Matrix.toLin' (g : Matrix (Fin n) (Fin n) A) ∘ₗ e.toLinearMap

def IsAdaptedFrame (A : CommAlgCat.{0} ℂ) {n : ℕ}
    (F : AffineFlag A n (fullShape n)) (g : Matrix.GeneralLinearGroup (Fin n) A) : Prop :=
  ∀ d : Step (fullShape n), (F.term d).toSubmodule =
    (coordinateSubmodule A n 1 d.val).map (matrixLinear A g)

structure BorelMatrix (A : CommAlgCat.{0} ℂ) (n : ℕ) where
  matrix : Matrix.GeneralLinearGroup (Fin n) A
  upper : ∀ i j : Fin n, j < i → matrix i j = 0
  diagonal : Fin n → Aˣ
  diagonal_value : ∀ i, (diagonal i : A) = matrix i i

def weightCharacter {A : CommAlgCat.{0} ℂ} {n : ℕ}
    (b : BorelMatrix A n) (weight : Fin n → ℤ) : Aˣ := ∏ i, b.diagonal i ^ weight i

/-- Actual scalar multiplication on the affine structure sheaf, obtained
by applying native tilde to multiplication on A. -/
def scalarUnit (A : CommAlgCat.{0} ℂ) (c : A) :
    structureModule (affineScheme A).left ⟶ structureModule (affineScheme A).left :=
  (tildeSelf (R := CommRingCat.of A)).inv ≫
    (tilde.functor (CommRingCat.of A)).map
      (ModuleCat.ofHom (Algebra.lsmul A A A c)) ≫
        (tildeSelf (R := CommRingCat.of A)).hom

/-- Full actual frame, scalar and base-change normalizations of the line. -/
structure WeightLine {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (weight : Fin n → ℤ) where
  object : F.scheme.left.Modules
  line : IsLineBundle object
  frame : ∀ (A : CommAlgCat.{0} ℂ) (f : affineScheme A ⟶ F.scheme)
      (g : Matrix.GeneralLinearGroup (Fin n) A), IsAdaptedFrame A (F.points A f) g →
    Section ((Scheme.Modules.pullback f.left).obj object)
  frame_iso : ∀ A f g hg, IsIso (frame A f g hg)
  change_frame : ∀ (A : CommAlgCat.{0} ℂ) (f : affineScheme A ⟶ F.scheme)
      (g : Matrix.GeneralLinearGroup (Fin n) A) (hg : IsAdaptedFrame A (F.points A f) g)
      (b : BorelMatrix A n) (hgb : IsAdaptedFrame A (F.points A f) (g * b.matrix)),
    frame A f (g * b.matrix) hgb = scalarUnit A ((weightCharacter b weight)⁻¹ : Aˣ) ≫ frame A f g hg
  baseChange : ∀ {A B : CommAlgCat.{0} ℂ} (phi : A ⟶ B) (f : affineScheme A ⟶ F.scheme)
      (g : Matrix.GeneralLinearGroup (Fin n) A) (hg : IsAdaptedFrame A (F.points A f) g)
      (gB : Matrix.GeneralLinearGroup (Fin n) B)
      (hB : IsAdaptedFrame B (F.points B (affineMap phi ≫ f)) gB),
    (∀ i j, gB i j = phi.hom (g i j)) →
    pullbackSection (affineMap phi).left (frame A f g hg) ≫
        (Scheme.Modules.pullbackComp (affineMap phi).left f.left).hom.app object =
      frame B (affineMap phi ≫ f) gB hB

end MathlibExt.AlgebraicGeometry.FlagWeightLineBundles
