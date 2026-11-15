/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# The actual Cox open, gauge action and character-normalized projection

The open is the union of the actual irrelevant basic opens in Spec of the
Cox polynomial ring. Its gauge group on every test algebra is Hom(Cl,A^×),
with the literal ray-degree diagonal action. Projection maps are pinned
on all localized affine charts. Categorical universality is a separate
Wanted result; simpliciality is required only for the orbit-fibre result.

Reference: Cox, alg-geom/9210008v3, Theorem 2.1. The basic-open/localization
dictionary is completed Mathlib support, not a fan-gluing request.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

open CategoryTheory _root_.AlgebraicGeometry FiniteToricCoordinates CoxGradedSheaves
  CoxNormalizedSheafification

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

def ambient : SchemeOver ℂ := Over.mk (Spec.algebraMap ℂ (CoxRing R))

def coxOpen : (ambient R).left.Opens :=
  ⨆ σ : F.Face, PrimeSpectrum.basicOpen (denominator R σ.val)

def openScheme : SchemeOver ℂ :=
  Over.mk ((coxOpen R).ι ≫ (ambient R).hom)

def inclusion : openScheme R ⟶ ambient R := Over.homMk (coxOpen R).ι

def localScheme (σ : F.Face) : SchemeOver ℂ :=
  Over.mk (Spec.algebraMap ℂ (LocalRing R σ.val))

/-- The complete ordinary localization dictionary. The maps are fixed by
their composition with the actual open immersion and their covering images. -/
structure LocalCover where
  map : ∀ σ : F.Face, localScheme R σ ⟶ openScheme R
  normalized : ∀ σ : F.Face,
    (map σ).left ≫ (inclusion R).left =
      Spec.map (CommRingCat.ofHom (algebraMap (CoxRing R) (LocalRing R σ.val)))
  [openCharts : ∀ σ : F.Face, IsOpenImmersion (map σ).left]
  cover : ∀ x : (openScheme R).left, ∃ σ : F.Face, x ∈ Set.range (map σ).left

attribute [instance] LocalCover.openCharts

def chartProjection (C : ChartComparison R) (σ : F.Face) :
    (localScheme R σ).left ⟶ (affineChart ℂ σ.val).left :=
  Spec.map (CommRingCat.ofHom
    (((degreeZeroAlgebra R σ.val).val.comp (C.iso σ).toAlgHom).toRingHom))

/-- Projection is determined on all characters through its actual affine cover. -/
structure Projection (L : LocalCover R) (C : ChartComparison R) (T : Realization ℂ F) where
  map : openScheme R ⟶ T.scheme
  charts : ∀ σ : F.Face, (L.map σ).left ≫ map.left =
    chartProjection R C σ ≫ (T.chartMap σ).left

def testScheme (A : CommAlgCat.{0} ℂ) : SchemeOver ℂ :=
  Over.mk (Spec.algebraMap ℂ A)

abbrev Gauge (A : CommAlgCat.{0} ℂ) := DegreeGroup R →+ Additive Aˣ

def coordinate (A : CommAlgCat.{0} ℂ) (p : testScheme A ⟶ openScheme R)
    (i : Fin R.count) : A :=
  ((Scheme.ΓSpecIso (.of (CoxRing R))).inv ≫
    (p.left ≫ (inclusion R).left).appTop ≫
    (Scheme.ΓSpecIso (.of A)).hom) (MvPolynomial.X i)

/-- The action is determined on every coordinate of every affine test
point. Since the open immersion is mono, these equations pin the maps. -/
structure GaugeAction where
  act : ∀ A : CommAlgCat.{0} ℂ, Gauge R A →
    (testScheme A ⟶ openScheme R) → (testScheme A ⟶ openScheme R)
  coordinate : ∀ A g p i, CoxQuotientGeometry.coordinate R A (act A g p) i =
    ((g (rayDegree R i)).toMul : A) * CoxQuotientGeometry.coordinate R A p i
  zero : ∀ A p, act A 0 p = p
  add : ∀ A g h p, act A (g + h) p = act A g (act A h p)

def IsInvariant (G : GaugeAction R) {W : SchemeOver ℂ}
    (q : openScheme R ⟶ W) : Prop :=
  ∀ (A : CommAlgCat.{0} ℂ) (g : Gauge R A) (p : testScheme A ⟶ openScheme R),
    G.act A g p ≫ q = p ≫ q

end MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

