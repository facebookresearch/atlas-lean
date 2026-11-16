/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
public import MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces

/-!
# New holomorphic frames and the normalized harmonic Higgs map

The new frames solve the full bar-connection equation in actual original
smooth coordinates. Their section coordinates are multiplication by the
inverse gauge matrix. Tensor coordinates are fixed on the native pure
tensor/sheafification unit. The Higgs map and its exterior square use the
actual extracted theta and its commutator on every local section.

These are construction contracts. Metric existence, polystability,
Chern vanishing and correspondence are not input fields. Simpson,
alg-geom/9604005v1, section 2, printed pages 9--11.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels

open CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicHolomorphicSectionKernels HarmonicHolomorphicModuleModels
open HolomorphicCotangentModuleModels
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)

/-- The matrix equation includes the full projected derivative of the proposed frame. -/
def barGaugeValue (i : Fin B.count) (U : Opens M) (Q : M → Matrices r)
    (x : U) (u : Coordinates n) : Matrices r :=
  (1 / 2 : ℂ) •
    ((show Matrices r from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r)
      Q (U : Set M) x.val u) +
      Complex.I • (show Matrices r from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r)
        Q (U : Set M) x.val (Complex.I • u))) +
    extractedBarConnection B h A i x.val u * Q x.val

/-- A local new frame is an actual smooth invertible gauge solving that equation. -/
structure LocalHolomorphicFrame (x : M) where
  domain : Opens M
  contains : x ∈ domain
  originalFrame : Fin B.count
  inFrame : domain ≤ frameOpen B originalFrame
  gauge : M → Matrices r
  smooth : ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) ∞ gauge domain
  invertible : ∀ y : domain, IsUnit (gauge y.val)
  bar : ∀ (y : domain) (u : Coordinates n),
    barGaugeValue B h A originalFrame domain gauge y u = 0
  initial : gauge x = 1

variable [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]

/-- Full local freeness of the actual bar kernel, normalized on every section and restriction. -/
structure KernelFrameModel {x : M} (F : LocalHolomorphicFrame B h A x) where
  coordinates : ∀ (U : Opens M), U ≤ F.domain →
    holomorphicKernel B h A U ≃ₗ[HolomorphicScalars (n := n) U]
      (Fin r → HolomorphicScalars (n := n) U)
  formula : ∀ (U : Opens M) (a : U ≤ F.domain) (s : holomorphicKernel B h A U) (y : U) (j : Fin r),
    ((coordinates U a s) j).val y =
      ((F.gauge y.val)⁻¹ *ᵥ coordinateSection B F.originalFrame U s.val y.val) j
  restriction : ∀ (U V : Opens M) (a : U ≤ F.domain) (b : V ≤ F.domain) (c : V ≤ U)
    (s : holomorphicKernel B h A U) (y : V) (j : Fin r),
    ((coordinates V b (holomorphicRestriction B h A c s)) j).val y =
      ((coordinates U a s) j).val ⟨y.val, c y.property⟩

variable [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [KernelSheafCondition B h A]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Tensor coordinates are fixed by the actual native sheafification unit on every pure tensor. -/
structure TensorFrameModel {x : M} {F : LocalHolomorphicFrame B h A x}
    (C : KernelFrameModel B h A F) (p : ℕ) where
  coordinates : ∀ (U : Opens M), U ≤ F.domain →
    (holomorphicTensor (holomorphicModule B h A) (holomorphicOmega (n := n) (M := M) p)).val.obj (op U)
      ≃ₗ[HolomorphicScalars (n := n) U]
        (Fin r → holomorphicFormModule (n := n) (M := M) U p)
  formula : ∀ (U : Opens M) (a : U ≤ F.domain)
    (s : holomorphicKernel B h A U) (α : holomorphicFormModule (n := n) (M := M) U p) (j : Fin r),
    coordinates U a (holomorphicTensorSection (holomorphicModule B h A)
      (holomorphicOmega (n := n) (M := M) p) U s α) j =
        scaleHolomorphicForm (n := n) (M := M) (C.coordinates U a s j) α

/-- An actual O-linear Higgs map, with a nonempty covering family of normalized holomorphic frames. -/
structure HarmonicHiggsModel where
  frames : ∀ x : M, LocalHolomorphicFrame B h A x
  kernelFrames : ∀ x : M, KernelFrameModel B h A (frames x)
  tensorFrames : ∀ (x : M) (p : ℕ), TensorFrameModel B h A (kernelFrames x) p
  theta : holomorphicModule B h A ⟶
    holomorphicTensor (holomorphicModule B h A) (holomorphicOmega (n := n) (M := M) 1)
  theta_formula : ∀ (x : M) (U : Opens M) (a : U ≤ (frames x).domain)
    (s : holomorphicKernel B h A U) (y : U) (u : Coordinates n) (j : Fin r),
    (((tensorFrames x 1).coordinates U a ((theta.val.app (op U)).hom s) j).val y) ![u] =
      (((frames x).gauge y.val)⁻¹ *ᵥ
        (extractedTheta B h A (frames x).originalFrame y.val u *ᵥ
          coordinateSection B (frames x).originalFrame U s.val y.val)) j

/-- The exterior square uses theta on the bundle factor and the actual alternating wedge on cotangent factors. -/
structure HiggsExteriorSquare (H : HarmonicHiggsModel B h A) where
  map : holomorphicModule B h A ⟶
    holomorphicTensor (holomorphicModule B h A) (holomorphicOmega (n := n) (M := M) 2)
  formula : ∀ (x : M) (U : Opens M) (a : U ≤ (H.frames x).domain)
    (s : holomorphicKernel B h A U) (y : U) (u v : Coordinates n) (j : Fin r),
    (((H.tensorFrames x 2).coordinates U a ((map.val.app (op U)).hom s) j).val y) ![u, v] =
      (((H.frames x).gauge y.val)⁻¹ *ᵥ
        ((extractedTheta B h A (H.frames x).originalFrame y.val u *
            extractedTheta B h A (H.frames x).originalFrame y.val v -
          extractedTheta B h A (H.frames x).originalFrame y.val v *
            extractedTheta B h A (H.frames x).originalFrame y.val u) *ᵥ
          coordinateSection B (H.frames x).originalFrame U s.val y.val)) j

/-- Integrability is zero of the actual normalized O-linear exterior-square map. -/
def IsIntegrable {H : HarmonicHiggsModel B h A} (S : HiggsExteriorSquare B h A H) : Prop := S.map = 0

end MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels
