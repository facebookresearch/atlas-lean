/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BottSamelsonFlagSchemes
public import MathlibExt.AlgebraicGeometry.GeometricChow
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import MathlibExt.AlgebraicGeometry.RelativeLefschetz
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual translated diagonal and its schematic closure

The torus parameter is the unit X in C[X,X^{-1}], realized as the native
localization away from X. The action is fixed on every affine test algebra
by the actual diagonal linear map with entries t^a_i. The graph map and its
scheme-theoretic image are then native scheme constructions. Fibres are
pullbacks of its actual ideal, and the finite union of Schubert products is
an intersection of the actual product ideals. No set-theoretic closure or
equality of cycle counts replaces an equality of subschemes.

The projective parameter is the literal Proj C[z0,z1]. Its two chart maps
are the native `Proj.fromOfGlobalSections` maps for [1:X] and [X:1].
Ordinary chart proofs are separate from the diagonal degeneration theorem.

Source: Brion, math/0410240v1, section 3.1 and Theorem 3.1.2;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0,
ProjectiveSpectrum/Basic (Andrew Yang and Mathlib contributors),
TensorProduct/Pi (Judith Ludwig, Christian Merten, 2024).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchubertDiagonalFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralFlagSchemes SchubertRankSchemes PerverseSheaves
open scoped TensorProduct

abbrev TorusRing := Localization.Away (Polynomial.X : Polynomial ℂ)

def parameterUnit : TorusRingˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := TorusRing) (Polynomial.X : Polynomial ℂ)).unit

def multiplicativeLine : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ TorusRing)))

def torusToAffine : multiplicativeLine ⟶ GeometricChow.affineLine :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℂ) TorusRing))) (by
    simp only [multiplicativeLine, GeometricChow.affineLine, Over.mk_hom, ← Spec.map_comp]
    congr 1)

def parameterAt (A : CommAlgCat.{0} ℂ) (f : affineScheme A ⟶ multiplicativeLine) : Aˣ :=
  Units.map (Spec.preimage f.left).hom parameterUnit

/-- The literal diagonal map, transported through the native scalar-tensor
coordinate equivalence. It fixes every basis tensor's scaling. -/
def diagonalLinear (A : CommAlgCat.{0} ℂ) {n : ℕ} (a : Fin n → ℤ) (t : Aˣ) :
    ExtendedSpace A n →ₗ[A] ExtendedSpace A n :=
  let e := TensorProduct.piScalarRight ℂ A A (Fin n)
  e.symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i : Fin n ↦ ((t ^ a i : Aˣ) : A) • LinearMap.proj i) ∘ₗ e.toLinearMap

def product (X Y : ComplexScheme) : ComplexScheme :=
  Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)

def first (X Y : ComplexScheme) : product X Y ⟶ X := Over.homMk (pullback.fst X.hom Y.hom) rfl

def second (X Y : ComplexScheme) : product X Y ⟶ Y :=
  Over.homMk (pullback.snd X.hom Y.hom) pullback.condition.symm

def productLift {T X Y : ComplexScheme} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ product X Y :=
  Over.homMk (pullback.lift f.left g.left (by rw [Over.w f, Over.w g])) (by
    change pullback.lift f.left g.left _ ≫ (pullback.fst X.hom Y.hom ≫ X.hom) = T.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w f)

def flagTorus {n : ℕ} (F : FlagSchemeModel n (fullShape n)) := product F.scheme multiplicativeLine
def flagSquare {n : ℕ} (F : FlagSchemeModel n (fullShape n)) := product F.scheme F.scheme

structure Translation {n : ℕ} (F : FlagSchemeModel n (fullShape n)) (a : Fin n → ℤ) where
  hom : flagTorus F ⟶ F.scheme
  normalization : ∀ (A : CommAlgCat.{0} ℂ) (x : affineScheme A ⟶ flagTorus F)
      (d : Step (fullShape n)),
    ((F.points A (x ≫ hom)).term d).toSubmodule =
      (((F.points A (x ≫ first F.scheme multiplicativeLine)).term d).toSubmodule).map
        (diagonalLinear A a (parameterAt A (x ≫ second F.scheme multiplicativeLine)))

def affineGraph {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (T : Translation F a) : flagTorus F ⟶ product (flagSquare F) GeometricChow.affineLine :=
  productLift (productLift (first F.scheme multiplicativeLine) T.hom)
    (second F.scheme multiplicativeLine ≫ torusToAffine)

def affineClosureIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (T : Translation F a) : (product (flagSquare F) GeometricChow.affineLine).left.IdealSheafData :=
  (affineGraph T).left.ker

def affineFibreIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (T : Translation F a) (t : ℂ) : (flagSquare F).left.IdealSheafData :=
  (affineClosureIdeal T).comap (GeometricChow.parameterSection (flagSquare F) t)

abbrev ProjectiveGrading := MvPolynomial.homogeneousSubmodule (Fin 2) ℂ
instance projectiveGradedAlgebra : GradedAlgebra ProjectiveGrading := MvPolynomial.gradedAlgebra

def projectiveLine : ComplexScheme :=
  Over.mk (ProjectiveSpace.projToSpec ProjectiveGrading)

def chartPolynomial (infinity : Bool) : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.C) (fun i ↦
    if infinity then (if i = 0 then Polynomial.X else 1)
    else (if i = 0 then 1 else Polynomial.X))

def chartSections (infinity : Bool) :
    MvPolynomial (Fin 2) ℂ →+* Γ(GeometricChow.affineLine.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv.hom.comp (chartPolynomial infinity)

/-- Only ordinary proofs about the fully displayed Proj charts. In particular
this package contains no degeneration or Schubert conclusion. -/
structure ProjectiveLineChartProofs : Prop where
  irrelevant : ∀ side : Bool, (HomogeneousIdeal.irrelevant ProjectiveGrading).toIdeal.map
    (chartSections side) = ⊤
  overBase : ∀ side : Bool,
    Proj.fromOfGlobalSections ProjectiveGrading (chartSections side) (irrelevant side) ≫
      projectiveLine.hom = GeometricChow.affineLine.hom

def lineChart (C : ProjectiveLineChartProofs) (side : Bool) :
    GeometricChow.affineLine ⟶ projectiveLine :=
  Over.homMk (Proj.fromOfGlobalSections ProjectiveGrading (chartSections side) (C.irrelevant side))
    (C.overBase side)

def projectiveGraph {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (C : ProjectiveLineChartProofs) (T : Translation F a) :
    flagTorus F ⟶ product (flagSquare F) projectiveLine :=
  affineGraph T ≫ productLift (first (flagSquare F) GeometricChow.affineLine)
    (second (flagSquare F) GeometricChow.affineLine ≫ lineChart C false)

/-- The actual global schematic closure in X×X×P1. -/
def projectiveClosureIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (C : ProjectiveLineChartProofs) (T : Translation F a) :
    (product (flagSquare F) projectiveLine).left.IdealSheafData :=
  (projectiveGraph C T).left.ker

def projectiveClosure {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (C : ProjectiveLineChartProofs) (T : Translation F a) : ComplexScheme :=
  Over.mk ((projectiveClosureIdeal C T).subschemeι ≫
    (product (flagSquare F) projectiveLine).hom)

def boundarySection {n : ℕ} (F : FlagSchemeModel n (fullShape n))
    (C : ProjectiveLineChartProofs) (infinity : Bool) :
    (flagSquare F).left ⟶ (product (flagSquare F) projectiveLine).left :=
  pullback.lift (𝟙 _)
    ((flagSquare F).hom ≫ GeometricChow.affinePoint 0 ≫ (lineChart C infinity).left)
    (by
      rw [Category.assoc, Category.assoc, Over.w (lineChart C infinity)]
      have h : GeometricChow.affinePoint 0 ≫ GeometricChow.affineLine.hom = 𝟙 _ := by
        have hr : CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)) ≫
            CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ)) = 𝟙 (CommRingCat.of ℂ) := by
          ext z
          simp
        change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) = 𝟙 _
        rw [← Spec.map_comp, hr, Spec.map_id]
      simp only [h, Category.comp_id, Category.id_comp])

def projectiveBoundaryIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)} {a : Fin n → ℤ}
    (C : ProjectiveLineChartProofs) (T : Translation F a) (infinity : Bool) :
    (flagSquare F).left.IdealSheafData :=
  (projectiveClosureIdeal C T).comap (boundarySection F C infinity)

def schubertProductIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    {w : Equiv.Perm (Fin n)} (S : SchubertIdealModel F w false)
    (O : SchubertIdealModel F w true) (infinity : Bool) : (flagSquare F).left.IdealSheafData :=
  if infinity then
    O.ideal.comap (first F.scheme F.scheme).left ⊔ S.ideal.comap (second F.scheme F.scheme).left
  else S.ideal.comap (first F.scheme F.scheme).left ⊔ O.ideal.comap (second F.scheme F.scheme).left

/-- Finite scheme union is the intersection of the actual product ideals. -/
def schubertUnionIdeal {n : ℕ} {F : FlagSchemeModel n (fullShape n)}
    (S : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w false)
    (O : ∀ w : Equiv.Perm (Fin n), SchubertIdealModel F w true)
    (infinity : Bool) : (flagSquare F).left.IdealSheafData :=
  ⨅ w, schubertProductIdeal (S w) (O w) infinity

end MathlibExt.AlgebraicGeometry.SchubertDiagonalFamilies
