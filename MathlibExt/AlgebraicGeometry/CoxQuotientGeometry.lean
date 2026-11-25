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
dictionary `localCover` is built from Mathlib's identification of a
localization at one element with its basic open; it is not a fan-gluing request.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoxQuotientGeometry

open CategoryTheory _root_.AlgebraicGeometry FiniteToricCoordinates CoxGradedSheaves
  CoxNormalizedSheafification

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

def ambient : SchemeOver ℂ := Over.mk (Spec.algebraMap ℂ (CoxRing R))

def coxOpen : (Spec (.of (CoxRing R))).Opens :=
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

/-- The localization of the Cox ring at the denominator of `σ`, as a map of spectra. -/
abbrev chartSpecMap (σ : F.Face) : Spec (.of (LocalRing R σ.val)) ⟶ Spec (.of (CoxRing R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (CoxRing R) (LocalRing R σ.val)))

/-- Its image is the basic open of the denominator. -/
theorem chartSpecMap_opensRange (σ : F.Face) :
    (chartSpecMap R σ).opensRange = PrimeSpectrum.basicOpen (denominator R σ.val) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (CoxRing R)) _

theorem range_chartSpecMap_subset (σ : F.Face) :
    Set.range (chartSpecMap R σ) ⊆ Set.range (coxOpen R).ι := by
  rw [Scheme.Opens.range_ι]
  change ((chartSpecMap R σ).opensRange : Set (Spec (.of (CoxRing R)))) ⊆ _
  rw [chartSpecMap_opensRange]
  exact le_iSup (fun σ : F.Face ↦ PrimeSpectrum.basicOpen (denominator R σ.val)) σ

/-- The chart of `σ`, landing in the Cox open. -/
def chartLift (σ : F.Face) : Spec (.of (LocalRing R σ.val)) ⟶ (coxOpen R).toScheme :=
  IsOpenImmersion.lift (coxOpen R).ι (chartSpecMap R σ) (range_chartSpecMap_subset R σ)

@[reassoc]
theorem chartLift_ι (σ : F.Face) : chartLift R σ ≫ (coxOpen R).ι = chartSpecMap R σ :=
  IsOpenImmersion.lift_fac _ _ _

instance (σ : F.Face) : IsOpenImmersion (chartLift R σ) := by
  have : IsOpenImmersion (chartLift R σ ≫ (coxOpen R).ι) := by
    rw [chartLift_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (coxOpen R).ι

/-- The localization charts of the Cox open $U = \bigcup_\sigma D(x^{\hat\sigma})$ in
$\operatorname{Spec} S$, for the Cox ring $S$ and
$x^{\hat\sigma} = \prod_{\rho \notin \sigma} x_\rho$. For every face $\sigma$ of the fan, the
chart is the open immersion $\operatorname{Spec} S_{x^{\hat\sigma}} \to U$ whose composite with
the inclusion of $U$ is induced by the localization $S \to S_{x^{\hat\sigma}}$; its image is the
basic open $D(x^{\hat\sigma})$. These charts cover $U$. -/
def localCover : LocalCover R where
  map σ := Over.homMk (chartLift R σ) (by
    change chartLift R σ ≫ (coxOpen R).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoxRing R))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (LocalRing R σ.val)))
    rw [chartLift_ι_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])
  normalized σ := chartLift_ι R σ
  openCharts σ := by
    change IsOpenImmersion (chartLift R σ)
    infer_instance
  cover x := by
    have hx : (coxOpen R).ι x ∈ (coxOpen R : Set (Spec (.of (CoxRing R)))) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self x
    obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hr : (coxOpen R).ι x ∈ ((chartSpecMap R σ).opensRange : Set (Spec (.of (CoxRing R)))) := by
      rw [chartSpecMap_opensRange]
      exact hσ
    obtain ⟨y, hy⟩ := hr
    refine ⟨σ, y, (coxOpen R).ι.isOpenEmbedding.injective ?_⟩
    change (chartLift R σ ≫ (coxOpen R).ι) y = _
    rw [chartLift_ι]
    exact hy

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

