/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicFinitePowerCycles
public import MathlibExt.AlgebraicGeometry.MotivicBundleModels
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The actual free quotients in the finite power construction

The source quotient has the fixed total scheme X^n times U, and its
action permutes every X coordinate and acts through the original U
torsor. Normalizations hold on every scheme-valued constant component,
including nonreduced tests. Finite constant-group components give the
full clopen decomposition of an arbitrary group-valued test.

The vector quotient is the actual associated permutation module with
its original torsor frame. Its quotient map is fixed on every pulled
universal section and every original polynomial coordinate. Global
quotient existence on arbitrary smooth X is not asserted: the source
factory is on affine X, where relative affine descent is effective.
Affine tests suffice for the subsequent Nisnevich sheaf construction.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3. This retains
the same original free quotient U/G and representation r throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerQuotientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open MotivicFinitePermutationModels MotivicPermutationBundleModels MotivicFinitePowerCycles
open MotivicBundleModels GeneralModuleTotalSpaces

variable {k H : Type} [Field k] [Group H] [Fintype H]
  [C : ConstantGroupGeometry (k := k) (H := H)]
  (P : SmoothProductSystem k) (U : FreeQuotient (k := k) (H := H))
  {n : ℕ} (r : H →* Equiv.Perm (Fin n))

/-- The component-valued point over an arbitrary original parameter scheme. -/
def componentPoint (T : Over (Spec (.of k))) (h : H) :
    T ⟶ constantScheme (k := k) (H := H) :=
  Over.homMk T.hom (by simp) ≫ constantPoint (k := k) h

/-- The original product with U before any quotient. -/
def powerTotal (X : SmoothScheme k) : SmoothScheme k :=
  P.obj (powerObj P X n) U.total

/-- The literal coordinate of the original n-fold source. -/
def sourceCoordinate (X : SmoothScheme k) (j : Fin n) : powerTotal P U (n := n) X ⟶ X :=
  (P.geometry (powerObj P X n) U.total).fst ≫ powerProjection P X n j

/-- The same whole product's original U-coordinate. -/
def totalU (X : SmoothScheme k) : powerTotal P U (n := n) X ⟶ U.total :=
  (P.geometry (powerObj P X n) U.total).snd

/-- An actual free quotient of the fixed source, normalized on all finite components. -/
structure PowerQuotient (X : SmoothScheme k) where
  quotient : FreeQuotient (k := k) (H := H)
  sourceIso : (powerTotal P U (n := n) X).scheme ≅ quotient.total.scheme
  baseMap : quotient.base ⟶ U.base
  baseEquation : sourceIso.hom ≫ quotient.projection ≫ baseMap =
    totalU P U (n := n) X ≫ U.projection
  actionX : ∀ (T : Over (Spec (.of k))) (h : H)
    (v : T ⟶ (powerTotal P U (n := n) X).scheme) (j : Fin n),
    quotient.actPoint T (componentPoint T h) (v ≫ sourceIso.hom) ≫
      sourceIso.inv ≫ sourceCoordinate P U (n := n) X j =
        v ≫ sourceCoordinate P U (n := n) X ((r h).symm j)
  actionU : ∀ (T : Over (Spec (.of k))) (h : H)
    (v : T ⟶ (powerTotal P U (n := n) X).scheme),
    quotient.actPoint T (componentPoint T h) (v ≫ sourceIso.hom) ≫
      sourceIso.inv ≫ totalU P U (n := n) X =
        U.actPoint T (componentPoint T h) (v ≫ totalU P U (n := n) X)

/-- The quotient arrow is the same original total-space map. -/
def PowerQuotient.map {X : SmoothScheme k} (Q : PowerQuotient P U r X) :
    powerTotal P U (n := n) X ⟶ Q.quotient.base :=
  Q.sourceIso.hom ≫ Q.quotient.projection

/-- Repeat the original representation in all i affine coordinates. -/
def repeatedRepresentation (i : ℕ) : H →* Equiv.Perm (Fin (n * i)) where
  toFun h := finProdFinEquiv.symm.trans
    (((r h).prodCongr (Equiv.refl (Fin i))).trans finProdFinEquiv)
  map_one' := by
    ext j
    simp
    exact Nat.mod_add_div _ _
  map_mul' h g := by ext j; simp [Equiv.Perm.mul_apply]

/-- The original affine coordinate is native polynomial evaluation on global sections. -/
def powerAffineCoordinate (A : StandardSchemes P) (i : ℕ)
    (T : Over (Spec (.of k))) (v : T ⟶ (powerObj P (A.affine i) n).scheme)
    (j : Fin (n * i)) : Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (affineRing k i))).inv ≫
    ((v ≫ powerProjection P (A.affine i) n (finProdFinEquiv.symm j).1).left ≫
      (A.affineIso i).hom).appTop).hom (MvPolynomial.X (finProdFinEquiv.symm j).2)

/-- The vector quotient has the actual source module and bundle total. -/
structure VectorQuotient (A : StandardSchemes P) (i : ℕ) where
  quotient : PowerQuotient P U r (A.affine i)
  module : AssociatedPermutationModule U (repeatedRepresentation r i)
  bundle : BundleGeometry U.base module.module (n * i)
  totalIso : quotient.quotient.base ≅ bundle.smoothTotal
  baseEquation : totalIso.hom ≫ bundle.projection = quotient.baseMap

/-- The whole vector quotient map uses only the actual quotient and total-space identifications. -/
def VectorQuotient.map {A : StandardSchemes P} {i : ℕ} (V : VectorQuotient P U r A i) :
    powerTotal P U (n := n) (A.affine i) ⟶ V.bundle.smoothTotal :=
  V.quotient.map P U r ≫ V.totalIso.hom

/-- The original U-coordinate is its actual quotient base. -/
theorem VectorQuotient.map_over {A : StandardSchemes P} {i : ℕ}
    (V : VectorQuotient P U r A i) :
    V.map P U r ≫ V.bundle.projection = totalU P U (n := n) (A.affine i) ≫ U.projection := by
  apply Over.OverMorphism.ext
  change (V.quotient.sourceIso.hom.left ≫ V.quotient.quotient.projection.left) ≫
    (V.totalIso.hom.left ≫ V.bundle.projection.left) =
      (totalU P U (n := n) (A.affine i)).left ≫ U.projection.left
  have h := congrArg Over.Hom.left V.baseEquation
  change V.totalIso.hom.left ≫ V.bundle.projection.left = V.quotient.baseMap.left at h
  rw [h]
  have hQ := congrArg Over.Hom.left V.quotient.baseEquation
  change V.quotient.sourceIso.hom.left ≫
    (V.quotient.quotient.projection.left ≫ V.quotient.baseMap.left) =
      (totalU P U (n := n) (A.affine i)).left ≫ U.projection.left at hQ
  simpa only [Category.assoc] using hQ

/-- The same represented universal section is pulled to the original U-base. -/
def VectorQuotient.section {A : StandardSchemes P} {i : ℕ} (V : VectorQuotient P U r A i)
    (T : Over (Spec (.of k))) (v : T ⟶ (powerTotal P U (n := n) (A.affine i)).scheme) :
    Γ((Scheme.Modules.pullback (v ≫ totalU P U (n := n) (A.affine i) ≫
      U.projection).left).obj V.module.module, ⊤) :=
  pulledSection V.module.module V.bundle.total.projection V.bundle.total.universalSection
    (v ≫ totalU P U (n := n) (A.affine i) ≫ U.projection).left
    ((v ≫ V.map P U r).left ≫ V.bundle.totalIso.hom) (by
      change (v.left ≫ (V.map P U r).left) ≫
        (V.bundle.totalIso.hom ≫ V.bundle.total.projection) =
          v.left ≫ ((totalU P U (n := n) (A.affine i)).left ≫ U.projection.left)
      have h := congrArg Over.Hom.left (V.map_over P U r)
      change (V.map P U r).left ≫
        (V.bundle.totalIso.hom ≫ V.bundle.total.projection) =
          (totalU P U (n := n) (A.affine i)).left ≫ U.projection.left at h
      simpa only [Category.assoc] using congrArg (fun f => v.left ≫ f) h)

/-- Every associated coordinate equals the original affine vector coordinate on all test schemes. -/
def VectorQuotient.IsNormalized {A : StandardSchemes P} {i : ℕ}
    (V : VectorQuotient P U r A i) : Prop :=
  ∀ (T : Over (Spec (.of k))) (v : T ⟶ (powerTotal P U (n := n) (A.affine i)).scheme)
    (j : Fin (n * i)),
    V.module.toPermutationFrame.coordinate T
      (v ≫ totalU P U (n := n) (A.affine i)) j (V.section P U r T v) =
      powerAffineCoordinate P A i T
        (v ≫ (P.geometry (powerObj P (A.affine i) n) U.total).fst) j

end MathlibExt.AlgebraicGeometry.MotivicPowerQuotientModels
