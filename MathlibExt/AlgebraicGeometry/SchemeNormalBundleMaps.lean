/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SchemeNormalConeCharts
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Actual normal-bundle algebras and canonical cone maps

The normal bundle is locally Spec of the symmetric algebra of the actual
conormal module I/I². Its transitions are fixed on coefficients and every
kernel generator. The actual conormal sheaf, its restriction maps, the zero
section and the map from the Rees normal cone are retained. Closed-immersion
squares use the actual section maps on every pair of affine opens.

Sources: Mathlib, 56a005855ea17e0b0958f73ec801ae140b0a1679,
ReesAlgebra and Extension/Cotangent (Andrew Yang, 2022/2024), Apache 2.0;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Conormal/DegreeOne, Divisors/NormalCone/NormalBundle and
Chow/BivariantLemmas/VirtualNormalBundleConeEmbedding, Apache 2.0.
The global normalized constructions are source integration dependencies;
their existence is not claimed or re-requested as a new theorem here.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeNormalBundleMaps

open CategoryTheory _root_.AlgebraicGeometry Opposite
open AffineConeAtlas AffineNormalConeMaps SchemeNormalConeCharts

variable {k l B C : Type} [CommRing k] [CommRing l] [CommRing B] [CommRing C]
  [Algebra k B] [Algebra l C]

def coneAlgebraMap (P : Algebra.Extension.{0} k B) :
    SymmetricAlgebra B P.Cotangent →ₐ[B] normalAlgebra P :=
  SymmetricAlgebra.lift (normalCotangent P)

@[simp] theorem coneAlgebraMap_generator (P : Algebra.Extension.{0} k B)
    (x : P.Cotangent) :
    coneAlgebraMap P (SymmetricAlgebra.ι B P.Cotangent x) = normalCotangent P x :=
  SymmetricAlgebra.lift_ι_apply _ _

structure BundleMap (P : Algebra.Extension.{0} k B) (Q : Algebra.Extension.{0} l C)
    (phi : P.Ring →+* Q.Ring) (beta : B →+* C)
    (h : (algebraMap Q.Ring C).comp phi = beta.comp (algebraMap P.Ring B)) where
  map : SymmetricAlgebra B P.Cotangent →+* SymmetricAlgebra C Q.Cotangent
  coefficient : ∀ b : B, map (algebraMap B _ b) = algebraMap C _ (beta b)
  degreeOne : ∀ x : P.ker,
    map (SymmetricAlgebra.ι B P.Cotangent (Algebra.Extension.Cotangent.mk x)) =
      SymmetricAlgebra.ι C Q.Cotangent
        (Algebra.Extension.Cotangent.mk (kernelImage P Q phi beta h x))

variable {Z Y : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i]

abbrev bundleAlgebra (U : Y.affineOpens) : Type := by
  letI := sectionAlgebra i U
  exact SymmetricAlgebra Γ(Z, i ⁻¹ᵁ U.val) (sectionExtension i U).Cotangent

def bundleCoefficient (U : Y.affineOpens) : Γ(Z, i ⁻¹ᵁ U.val) →+* bundleAlgebra i U := by
  letI := sectionAlgebra i U
  exact algebraMap _ _

abbrev chartKernel (U : Y.affineOpens) : Type := by
  letI := sectionAlgebra i U
  exact ↥((sectionExtension i U).ker)

def bundleGenerator (U : Y.affineOpens) (x : chartKernel i U) :
    bundleAlgebra i U := by
  letI := sectionAlgebra i U
  exact SymmetricAlgebra.ι _ _ (Algebra.Extension.Cotangent.mk x)

def chartConeMap (U : Y.affineOpens) : bundleAlgebra i U →+* normalRing i U := by
  letI := sectionAlgebra i U
  exact (coneAlgebraMap (sectionExtension i U)).toRingHom

abbrev BundleRestriction (U V : Y.affineOpens) (h : V ≤ U) : Type := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra i V
  exact BundleMap (sectionExtension i U) (sectionExtension i V)
    (baseRestriction (Y := Y) h) (closedRestriction i h) (restrictionSquare i h)

def bundleRestrictionRingMap {U V : Y.affineOpens} {h : V ≤ U}
    (R : BundleRestriction i U V h) : bundleAlgebra i U →+* bundleAlgebra i V := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra i V
  exact R.map

/-- This is the actual regular-sequence condition in the section-map kernel. -/
def RegularEmbedding (c : ℕ) : Prop :=
  ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.val ∧
    letI := sectionAlgebra i U
    ∃ f : Fin c → Γ(Y, U.val),
      (sectionExtension i U).ker = Ideal.span (Set.range f) ∧
        RingTheory.Sequence.IsRegular Γ(Y, U.val) (List.ofFn f)

structure NormalBundleModel (c : ℕ) where
  conormal : Z.Modules
  conormal_rank : AlgebraicBundleGeometry.IsBundle conormal c
  conormalChart : ∀ U : Y.affineOpens,
    letI := sectionAlgebra i U
    conormal.val.obj (op (i ⁻¹ᵁ U.val)) ≃ₗ[Γ(Z, i ⁻¹ᵁ U.val)]
      (sectionExtension i U).Cotangent
  total : Scheme.{0}
  projection : total ⟶ Z
  affine : ∀ U : Y.affineOpens, IsAffineOpen (projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))
  chart : ∀ U : Y.affineOpens,
    Γ(total, projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)) ≃+* bundleAlgebra i U
  coefficients : ∀ (U : Y.affineOpens) (a : Γ(Z, i ⁻¹ᵁ U.val)),
    chart U ((projection.app (i ⁻¹ᵁ U.val)).hom a) = bundleCoefficient i U a
  transition : ∀ U V : Y.affineOpens, ∀ h : V ≤ U, BundleRestriction i U V h
  restrictions : ∀ (U V : Y.affineOpens) (h : V ≤ U)
      (a : Γ(total, projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))),
    chart V ((total.presheaf.map
      (homOfLE (show projection ⁻¹ᵁ (i ⁻¹ᵁ V.val) ≤ projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)
        from fun _ hx ↦ h hx)).op).hom a) =
      bundleRestrictionRingMap i (transition U V h) (chart U a)
  conormalRestrictions : ∀ (U V : Y.affineOpens) (h : V ≤ U)
      (a : conormal.val.obj (op (i ⁻¹ᵁ U.val))),
    letI := sectionAlgebra i U
    letI := sectionAlgebra i V
    SymmetricAlgebra.ι _ _ (conormalChart V
      ((conormal.val.map (homOfLE
        (show i ⁻¹ᵁ V.val ≤ i ⁻¹ᵁ U.val from fun _ hx ↦ h hx)).op).hom a)) =
      bundleRestrictionRingMap i (transition U V h)
        (SymmetricAlgebra.ι _ _ (conormalChart U a))
  zero : Z ⟶ total
  zero_projection : zero ≫ projection = 𝟙 Z
  zeroGenerators : ∀ (U : Y.affineOpens)
      (x : chartKernel i U),
    (zero.appLE (projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)) (i ⁻¹ᵁ U.val)
      (by
        intro z hz
        change projection (zero z) ∈ i ⁻¹ᵁ U.val
        have he : projection (zero z) = z := by
          change (zero ≫ projection) z = z
          rw [zero_projection]
          rfl
        rw [he]
        exact hz)).hom
      ((chart U).symm (bundleGenerator i U x)) = 0

variable {c : ℕ} (N : NormalBundleModel i c) (C : NormalConeModel i)

theorem coneEmbeddingOpenLE (f : C.cone ⟶ N.total) (h : f ≫ N.projection = C.projection)
    (U : Y.affineOpens) :
    C.projection ⁻¹ᵁ (i ⁻¹ᵁ U.val) ≤ f ⁻¹ᵁ (N.projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)) := by
  intro x hx
  change C.projection x ∈ i ⁻¹ᵁ U.val at hx
  change N.projection (f x) ∈ i ⁻¹ᵁ U.val
  simpa only [← Scheme.Hom.comp_apply, h] using hx

structure ConeEmbedding where
  map : C.cone ⟶ N.total
  overBase : map ≫ N.projection = C.projection
  [closed : IsClosedImmersion map]
  normalized : ∀ (U : Y.affineOpens)
      (a : Γ(N.total, N.projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))),
    C.chart U ((map.appLE _ _ (coneEmbeddingOpenLE i N C map overBase U)).hom a) =
      chartConeMap i U (N.chart U a)

attribute [instance] ConeEmbedding.closed

variable {W T : Scheme.{0}} (j : W ⟶ T) [IsClosedImmersion j]
  (a : W ⟶ Z) (b : T ⟶ Y) (h : j ≫ b = a ≫ i)

theorem sectionMapCongr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

omit [IsClosedImmersion i] [IsClosedImmersion j] in
include h in
theorem squareOpenLE (U : Y.affineOpens) (V : T.affineOpens) (hv : V.val ≤ b ⁻¹ᵁ U.val) :
    j ⁻¹ᵁ V.val ≤ a ⁻¹ᵁ (i ⁻¹ᵁ U.val) := by
  intro x hx
  change i (a x) ∈ U.val
  rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  exact hv hx

def squareBaseMap (U : Y.affineOpens) (V : T.affineOpens) (hv : V.val ≤ b ⁻¹ᵁ U.val) :
    Γ(Y, U.val) →+* Γ(T, V.val) := (b.appLE U.val V.val hv).hom

def squareClosedMap (U : Y.affineOpens) (V : T.affineOpens)
    (hv : V.val ≤ b ⁻¹ᵁ U.val) : Γ(Z, i ⁻¹ᵁ U.val) →+* Γ(W, j ⁻¹ᵁ V.val) :=
  (a.appLE _ _ (squareOpenLE i j a b h U V hv)).hom

theorem sectionSquare (U : Y.affineOpens) (V : T.affineOpens)
    (hv : V.val ≤ b ⁻¹ᵁ U.val) :
    letI := sectionAlgebra i U
    letI := sectionAlgebra j V
    (algebraMap (sectionExtension j V).Ring Γ(W, j ⁻¹ᵁ V.val)).comp
      (squareBaseMap b U V hv) =
        (squareClosedMap i j a b h U V hv).comp
          (algebraMap (sectionExtension i U).Ring Γ(Z, i ⁻¹ᵁ U.val)) := by
  let := sectionAlgebra i U
  let := sectionAlgebra j V
  change (j.app V.val).hom.comp (b.appLE U.val V.val hv).hom =
    (a.appLE _ _ (squareOpenLE i j a b h U V hv)).hom.comp (i.app U.val).hom
  have hc : b.appLE U.val V.val hv ≫ j.app V.val =
      i.app U.val ≫ a.appLE _ _ (squareOpenLE i j a b h U V hv) := by
    rw [j.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    exact sectionMapCongr h _ _ _ _
  exact congrArg (fun f : Γ(Y, U.val) ⟶ Γ(W, j ⁻¹ᵁ V.val) ↦ f.hom) hc

abbrev SquareNormalMap (U : Y.affineOpens) (V : T.affineOpens)
    (hv : V.val ≤ b ⁻¹ᵁ U.val) : Type := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra j V
  exact NormalMap (sectionExtension i U) (sectionExtension j V)
    (squareBaseMap b U V hv) (squareClosedMap i j a b h U V hv)
      (sectionSquare i j a b h U V hv)

def squareNormalRingMap {U : Y.affineOpens} {V : T.affineOpens}
    {hv : V.val ≤ b ⁻¹ᵁ U.val} (R : SquareNormalMap i j a b h U V hv) :
    normalRing i U →+* normalRing j V := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra j V
  exact R.map

variable (D : NormalConeModel j)

include h in
theorem coneSquareOpenLE (f : D.cone ⟶ C.cone)
    (hf : f ≫ C.projection = D.projection ≫ a)
    (U : Y.affineOpens) (V : T.affineOpens) (hv : V.val ≤ b ⁻¹ᵁ U.val) :
    D.projection ⁻¹ᵁ (j ⁻¹ᵁ V.val) ≤ f ⁻¹ᵁ (C.projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)) := by
  intro x hx
  change D.projection x ∈ j ⁻¹ᵁ V.val at hx
  change C.projection (f x) ∈ i ⁻¹ᵁ U.val
  rw [← Scheme.Hom.comp_apply, hf, Scheme.Hom.comp_apply]
  exact squareOpenLE i j a b h U V hv hx

/-- The global natural cone map is fixed by every actual affine Rees map. -/
structure ConeSquare where
  map : D.cone ⟶ C.cone
  overBase : map ≫ C.projection = D.projection ≫ a
  affine : ∀ (U : Y.affineOpens) (V : T.affineOpens) (hv : V.val ≤ b ⁻¹ᵁ U.val),
    SquareNormalMap i j a b h U V hv
  normalized : ∀ (U : Y.affineOpens) (V : T.affineOpens) (hv : V.val ≤ b ⁻¹ᵁ U.val)
      (s : Γ(C.cone, C.projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))),
    D.chart V ((map.appLE _ _
      (coneSquareOpenLE i C j a b h D map overBase U V hv)).hom s) =
      squareNormalRingMap i j a b h (affine U V hv) (C.chart U s)

open CategoryTheory.Limits

/-- The target is the actual pullback of the original normal bundle.
Its map is forced by the canonical cone square and symmetric-to-Rees map. -/
def refinedConeEmbedding (E : ConeEmbedding i N C) (S : ConeSquare i C j a b h D) :
    D.cone ⟶ pullback N.projection a :=
  pullback.lift (S.map ≫ E.map) D.projection (by
    rw [Category.assoc, E.overBase, S.overBase])

@[simp] theorem refinedConeEmbedding_toBase (E : ConeEmbedding i N C)
    (S : ConeSquare i C j a b h D) :
    refinedConeEmbedding i N C j a b h D E S ≫ pullback.snd N.projection a = D.projection :=
  pullback.lift_snd _ _ _

end MathlibExt.AlgebraicGeometry.SchemeNormalBundleMaps
