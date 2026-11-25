/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentKahlerHiggsStability
public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicFrameModels

/-!
# Actual smooth realizations of general holomorphic Higgs sheaves

The underlying bundle realizes the native smooth scalar extension of
the same O-module. Its frames are required to be holomorphic after this
realization is constructed from the given holomorphic sheaf. Local
coordinates fix every section through the native scalar-extension unit;
tensor coordinates fix every native pure tensor. The Higgs matrices are
fixed by the actual O-linear theta map.

The harmonic output adapter uses the actual bar-kernel O-module and
actual theta. It does not assume the old smooth frames are holomorphic.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HiggsSmoothRealizationModels

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels HolomorphicSmoothScalarModels
open HarmonicHolomorphicFrameModels
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  {T : TensorAssociatorSource (n := n) (M := M)} {W : CotangentWedgeSource (n := n) (M := M)}

/-- Physical realization retains native scalar extension and all section and tensor coordinates. -/
structure HiggsRealization (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (E : HiggsModule T W) where
  physical : SmoothModuleRealization (r := E.rank) S E.module
  geometry : HolomorphicHiggsField physical.bundle
  coordinates : ∀ (i : Fin physical.bundle.count) (U : Opens M), U ≤ frameOpen physical.bundle i →
    E.module.val.obj (op U) ≃ₗ[HolomorphicScalars (n := n) U]
      (Fin E.rank → HolomorphicScalars (n := n) U)
  coordinates_normalized : letI := physical.calculus; letI := physical.multiplication; letI := physical.gluing
    ∀ (i : Fin physical.bundle.count) (U : Opens M) (a : U ≤ frameOpen physical.bundle i)
      (s : E.module.val.obj (op U)) (x : U) (j : Fin E.rank),
    (coordinates i U a s j).val x = coordinateSection physical.bundle i U
      (((physical.comparison.hom.val.app (op U)).hom (smoothExtensionSection S E.module U s)).val) x.val j
  tensorCoordinates : ∀ (i : Fin physical.bundle.count) (U : Opens M), U ≤ frameOpen physical.bundle i →
    ∀ p : ℕ, (holomorphicTensor E.module (holomorphicOmega (n := n) (M := M) p)).val.obj (op U)
      ≃ₗ[HolomorphicScalars (n := n) U]
        (Fin E.rank → holomorphicFormModule (n := n) (M := M) U p)
  tensor_normalized : ∀ (i : Fin physical.bundle.count) (U : Opens M)
    (a : U ≤ frameOpen physical.bundle i) (p : ℕ) (s : E.module.val.obj (op U))
    (α : holomorphicFormModule (n := n) (M := M) U p) (j : Fin E.rank),
      tensorCoordinates i U a p (holomorphicTensorSection E.module
        (holomorphicOmega (n := n) (M := M) p) U s α) j =
          scaleHolomorphicForm (n := n) (M := M) (coordinates i U a s j) α
  theta_normalized : ∀ (i : Fin physical.bundle.count) (U : Opens M)
    (a : U ≤ frameOpen physical.bundle i) (s : E.module.val.obj (op U))
    (x : U) (u : Coordinates n) (j : Fin E.rank),
      ((tensorCoordinates i U a 1 ((E.theta.val.app (op U)).hom s) j).val x) ![u] =
        ((geometry.theta i x.val u) *ᵥ (fun k => (coordinates i U a s k).val x)) j

variable {r : ℕ} (B : SmoothComplexBundle n M r) (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)] [BarMultiplicationCalculus B h A]
  [KernelSheafCondition B h A]

/-- Harmonic output is the exact bar-kernel module and exact theta map. -/
structure HarmonicKernelHiggsAdapter (H : HarmonicHiggsModel B h A) where
  object : HiggsModule T W
  module_eq : object.module = holomorphicModule B h A
  rank_eq : object.rank = r
  theta_eq : HEq object.theta H.theta

variable (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
  [SectionCalculus B 0] [SmoothSectionMultiplication B] [SmoothBundleSheafCondition B]

/-- Scalar-extension unit identifies actual kernel sections with the same original smooth sections. -/
structure KernelSmoothExtensionSource where
  iso : (smoothScalarExtension S).obj (holomorphicModule B h A) ≅ smoothBundleModule B
  normalized : ∀ (U : Opens M) (s : holomorphicKernel B h A U),
    ((iso.hom.val.app (op U)).hom (smoothExtensionSection S (holomorphicModule B h A) U s)).val = s.val

/-- The actual smooth action of an O-linear kernel arrow on the original bundle. -/
def kernelSmoothMap {h' : HermitianMetric B} {A' : SmoothConnection B}
    [SectionCalculus B (unitaryPart B h' A')] [BarMultiplicationCalculus B h' A']
    [KernelSheafCondition B h' A']
    (I : KernelSmoothExtensionSource B h A S) (J : KernelSmoothExtensionSource B h' A' S)
    (e : holomorphicModule B h A ⟶ holomorphicModule B h' A') : smoothBundleModule B ⟶ smoothBundleModule B :=
  I.iso.inv ≫ (smoothScalarExtension S).map e ≫ J.iso.hom

/-- Parallel bundle automorphisms obey native frame transitions and the differentiated connection equation. -/
structure ParallelMatrixAutomorphism where
  matrix : Fin B.count → M → Matrices r
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) ∞ (matrix i) (B.core.baseSet i)
  invertible : ∀ i x, x ∈ B.core.baseSet i → IsUnit (matrix i x)
  transition : ∀ i j x, x ∈ B.core.baseSet i ∩ B.core.baseSet j →
    matrix j x = (transitionMatrix B i j x)⁻¹ * matrix i x * transitionMatrix B i j x
  parallel : ∀ i x, x ∈ B.core.baseSet i → ∀ u : Coordinates n,
    matrixDifferential B i (matrix i) x u + A.matrix i x u * matrix i x - matrix i x * A.matrix i x u = 0

/-- Parallel matrices are tied to the actual native scalar extension of the specified kernel arrow. -/
structure KernelParallelMapSource {h' : HermitianMetric B}
    [SectionCalculus B (unitaryPart B h' A)] [BarMultiplicationCalculus B h' A]
    [KernelSheafCondition B h' A]
    (I : KernelSmoothExtensionSource B h A S) (J : KernelSmoothExtensionSource B h' A S)
    (e : holomorphicModule B h A ⟶ holomorphicModule B h' A) where
  automorphism : ParallelMatrixAutomorphism B A
  normalized : ∀ (i : Fin B.count) (U : Opens M) (s : smoothSectionModule B U)
    (x : U), x.val ∈ B.core.baseSet i →
      coordinateSection B i U (((kernelSmoothMap B h A S I J e).val.app (op U)).hom s).val x.val =
        automorphism.matrix i x.val *ᵥ coordinateSection B i U s.val x.val

end MathlibExt.AlgebraicGeometry.HiggsSmoothRealizationModels
