/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual twisted bundles, Higgs-family arrows and characteristic comparison

The underlying object is a native vector-bundle module and an O-linear
map E -> E tensor L. On a smooth curve with L=Omega1 this is a Higgs field.
For arbitrary schemes this file calls it a twisted endomorphism and does
not silently drop higher-dimensional Higgs integrability.

Characteristic coefficients are actual global line-power sections. Their
normalization is the characteristic polynomial on every genuine affine
frame, and existence of frames is required. The untwisting isomorphism is
fixed on all pure tensors with the chosen line generator. Thus neither
coefficient values nor a named characteristic-polynomial map are oracles.

References: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2,
(1.3.1)--(1.3.5); Donagi--Gaitsgory, arXiv:math/0005132v3, 17.2.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open scoped BigOperators

universe u

export NativeTensorComparisons (tensorIso)

/-- A native locally free sheaf with an actual line-valued endomorphism. -/
structure TwistedBundle (X : Scheme.{u}) (L : X.Modules) (r : ℕ) where
  module : X.Modules
  twistLine : IsLineBundle L
  bundle : IsVectorBundle module r
  field : module ⟶ moduleTensor X module L

namespace TwistedBundle
variable {X : Scheme.{u}} {L : X.Modules} {r : ℕ}

/-- Isomorphisms preserve the actual twisted field. -/
structure Hom (E F : TwistedBundle X L r) where
  iso : E.module ≅ F.module
  field_eq : iso.hom ≫ F.field = E.field ≫ tensorMap iso.hom (𝟙 L)

@[ext] theorem Hom.ext {E F : TwistedBundle X L r} {f g : Hom E F}
    (h : f.iso = g.iso) : f = g := by cases f; cases g; cases h; rfl

instance : Groupoid (TwistedBundle X L r) where
  Hom E F := Hom E F
  id E := ⟨Iso.refl _, by simp⟩
  comp f g := ⟨f.iso ≪≫ g.iso, by
    simp only [Iso.trans_hom, Category.assoc, g.field_eq]
    rw [← Category.assoc, f.field_eq]
    simp only [Category.assoc, ← tensorMap_comp, Category.comp_id]⟩
  inv f := ⟨f.iso.symm, by
    have h := f.field_eq
    apply (cancel_mono (tensorIso f.iso (Iso.refl L)).hom).1
    change (f.iso.inv ≫ _ ≫ tensorMap f.iso.hom (𝟙 L)) =
      (_ ≫ tensorMap f.iso.inv (𝟙 L)) ≫ tensorMap f.iso.hom (𝟙 L)
    rw [← h]
    simp only [Category.assoc, ← tensorMap_comp, Iso.inv_hom_id, Category.comp_id,
      tensorMap_id]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]⟩
  id_comp f := by apply Hom.ext; ext; simp
  comp_id f := by apply Hom.ext; ext; simp
  assoc f g h := by apply Hom.ext; ext; simp
  inv_comp f := by apply Hom.ext; ext; simp
  comp_inv f := by apply Hom.ext; ext; simp

end TwistedBundle

/-- Local pure tensors enter the actual sheafified tensor through its unit. -/
def localTensor {X : Scheme.{u}} (E F : X.Modules) (U : X.Opens)
    (e : Γ(E, U)) (f : Γ(F, U)) : Γ(moduleTensor X E F, U) :=
  (((moduleAdjunction X).unit.app
    (((forgetModules X).obj E) ⊗ ((forgetModules X).obj F))).app (op U)).hom
      (TensorProduct.tmul (Γ(X, U)) e f)

/-- The actual local tensor power of a local line section. -/
def localPower {X : Scheme.{u}} (L : X.Modules) (U : X.Opens) (s : Γ(L,U)) :
    (n : ℕ) → Γ(power L n,U)
  | 0 => (1 : Γ(X,U))
  | n+1 => localTensor (power L n) L U (localPower L U s n) s

/-- Genuine affine coordinates, including the fixed tensor and power images. -/
structure AffineTwistedFrame {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (E : TwistedBundle X L r) (U : X.Opens) where
  affine : IsAffineOpen U
  basis : Module.Basis (Fin r) Γ(X,U) Γ(E.module,U)
  lineBasis : Module.Basis Unit Γ(X,U) Γ(L,U)
  untwist : Γ(moduleTensor X E.module L,U) ≃ₗ[Γ(X,U)] Γ(E.module,U)
  untwist_normalization : ∀ e,
    untwist (localTensor E.module L U e (lineBasis ())) = e
  powerBasis : ∀ n, Module.Basis Unit Γ(X,U) Γ(power L n,U)
  power_normalization : ∀ n,
    powerBasis n () = localPower L U (lineBasis ()) n

/-- The actual local endomorphism in a fixed affine line frame. -/
def framedEnd {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (E : TwistedBundle X L r) {U : X.Opens} (F : AffineTwistedFrame E U) :
    Module.End Γ(X,U) Γ(E.module,U) :=
  F.untwist.toLinearMap.comp (E.field.val.app (op U)).hom

/-- The actual local characteristic polynomial matrix. -/
def framedCharpoly {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (E : TwistedBundle X L r) {U : X.Opens} (F : AffineTwistedFrame E U) :
    Polynomial Γ(X,U) :=
  (LinearMap.toMatrix F.basis F.basis (framedEnd E F)).charpoly

/-- Source-normalized global elementary characteristic coefficients.
Frames cover every point, preventing a vacuous coefficient condition. -/
structure CharacteristicSections {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (E : TwistedBundle X L r) where
  frameCover : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Nonempty (AffineTwistedFrame E U)
  coefficient : ∀ n : ℕ, Section (power L n)
  higher_zero : ∀ n, r < n → coefficient n = 0
  local_normalization : ∀ (U : X.Opens) (F : AffineTwistedFrame E U) (i : ℕ), i ≤ r →
    (F.powerBasis i).repr (((coefficient i).val.app (op U)).hom (1 : Γ(X,U))) () =
      (-1 : Γ(X,U)) ^ i * (framedCharpoly E F).coeff (r-i)

/-- The rank-two trace is the first actual elementary coefficient. -/
abbrev traceSection {X : Scheme.{u}} {L : X.Modules}
    {E : TwistedBundle X L 2} (K : CharacteristicSections E) := K.coefficient 1

/-- The rank-two determinant is the second actual elementary coefficient. -/
abbrev determinantSection {X : Scheme.{u}} {L : X.Modules}
    {E : TwistedBundle X L 2} (K : CharacteristicSections E) := K.coefficient 2

/-- An invariant subobject has an actual restricted twisted field. -/
def FieldInvariant {X : Scheme.{u}} {L : X.Modules} {r : ℕ}
    (E : TwistedBundle X L r) (F : X.Modules) (i : F ⟶ E.module) : Prop :=
  ∃ theta : F ⟶ moduleTensor X F L,
    i ≫ E.field = theta ≫ tensorMap i (𝟙 L)

/-- Slope stability of a twisted bundle on a smooth proper integral curve, tested on the
actual invariant subbundles. On such a curve a saturated subsheaf of a vector bundle is a
subbundle with locally free quotient (finitely generated torsion-free modules over a discrete
valuation ring are free), so these are the saturated invariant subsheaves of the slope condition. -/
def IsStableCurve {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] {L : C.left.Modules} {r : ℕ}
    (E : TwistedBundle C.left L r) : Prop :=
  0 < r ∧ ∀ s : ℕ, 0 < s → s < r → ∀ (F : C.left.Modules) (i : F ⟶ E.module),
    Mono i → ∀ hF : IsVectorBundle F s, IsVectorBundle (cokernel i) (r-s) →
    FieldInvariant E F i →
      (bundleDegree C.hom F s hF : ℚ) / s < (bundleDegree C.hom E.module r E.bundle : ℚ) / r

/-- Semistability tests the same invariant subbundles, on a smooth proper integral curve. -/
def IsSemistableCurve {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] {L : C.left.Modules} {r : ℕ}
    (E : TwistedBundle C.left L r) : Prop :=
  0 < r ∧ ∀ s : ℕ, 0 < s → s < r → ∀ (F : C.left.Modules) (i : F ⟶ E.module),
    Mono i → ∀ hF : IsVectorBundle F s, IsVectorBundle (cokernel i) (r-s) →
    FieldInvariant E F i →
      (bundleDegree C.hom F s hF : ℚ) / s ≤ (bundleDegree C.hom E.module r E.bundle : ℚ) / r

/-- Polystability of a twisted bundle $E$ of rank $r$ (a rank-$r$ vector bundle with a field
$E \to E \otimes L$, for a line bundle $L$) on a smooth proper integral curve $C$ over a field: $E$
is isomorphic, compatibly with the fields, to a finite direct sum of stable twisted bundles $F_i$
whose ranks add up to $r$ and which all have the slope of $E$,
$\deg F_i / \operatorname{rk} F_i = \deg E / r$. -/
def IsPolystableCurve {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProperCurve C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [IsIntegral C.left] {L : C.left.Modules} {r : ℕ}
    (E : TwistedBundle C.left L r) : Prop :=
  let : HasFiniteBiproducts C.left.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  ∃ (n : ℕ) (rank : Fin n → ℕ)
    (F : ∀ i, TwistedBundle C.left L (rank i)),
    (∑ i, rank i) = r ∧
    ∃ b : (biproduct fun i => (F i).module) ≅ E.module,
      (∀ i, IsStableCurve C (F i)) ∧
      (∀ i, (bundleDegree C.hom (F i).module (rank i) (F i).bundle : ℚ) / rank i =
        (bundleDegree C.hom E.module r E.bundle : ℚ) / r) ∧
      ∀ i, biproduct.ι (fun j => (F j).module) i ≫ b.hom ≫ E.field =
        (F i).field ≫ tensorMap
          (biproduct.ι (fun j => (F j).module) i ≫ b.hom) (𝟙 L)

/-- The actual ordinary parameter family; its twist is pulled from C. -/
abbrev CurveFamily {k : Type u} [Field k] (C T : Over (Spec (.of k)))
    (L : C.left.Modules) (r : ℕ) :=
  TwistedBundle (prod C T).left ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj L) r

end MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
