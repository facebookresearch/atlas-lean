/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HiggsKernelComparisonModels

/-!
# Actual connection isomorphisms for harmonic Higgs reconstruction

The connection is the literal Chern-plus-theta-plus-adjoint reconstruction.
Its isomorphisms are invertible smooth matrices satisfying the actual
differentiated source/target connection equation. They are fixed by the
native smooth scalar extension of an actual O-linear Higgs automorphism.
This is the target of inverse uniqueness, not an assumed equivalence.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HiggsReconstructionIsomorphisms

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicReconstructionInterfaces HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels HolomorphicSmoothScalarModels HiggsSmoothRealizationModels
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- The native realized reconstruction is flat when its literal curvature vanishes. -/
theorem reconstructed_flat (h : HermitianMetric B) (H : HolomorphicHiggsField B)
    (C : ConnectionRealization B (reconstructedConnection B h H.value))
    (hh : IsHarmonicMetric B h H) : IsFlat B C.connection := by
  intro i x hx u v
  rw [C.normalized]
  exact hh i x hx u v

/-- A genuine isomorphism between the two actual connections on the same original bundle. -/
structure ParallelConnectionIsomorphism (C D : SmoothConnection B) where
  matrix : Fin B.count → M → Matrices r
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) ∞ (matrix i) (B.core.baseSet i)
  invertible : ∀ i x, x ∈ B.core.baseSet i → IsUnit (matrix i x)
  transition : ∀ i j x, x ∈ B.core.baseSet i ∩ B.core.baseSet j →
    matrix j x = (transitionMatrix B i j x)⁻¹ * matrix i x * transitionMatrix B i j x
  parallel : ∀ i x, x ∈ B.core.baseSet i → ∀ u : Coordinates n,
    matrixDifferential B i (matrix i) x u + D.matrix i x u * matrix i x - matrix i x * C.matrix i x u = 0

variable [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  {T : TensorAssociatorSource (n := n) (M := M)} {W : CotangentWedgeSource (n := n) (M := M)}

/-- Inverse uniqueness uses the actual Higgs automorphism and its actual parallel native smooth extension. -/
structure HiggsReconstructionIsomorphism (S : HolomorphicSmoothInclusionSource (n := n) (M := M))
    (E : HiggsModule T W) (R : HiggsRealization S E) (C D : SmoothConnection R.physical.bundle) where
  iso : E.module ≅ E.module
  theta : iso.hom ≫ E.theta = E.theta ≫ tensorMap iso.hom (𝟙 _)
  parallel : ParallelConnectionIsomorphism R.physical.bundle C D
  normalized : letI := R.physical.calculus; letI := R.physical.multiplication; letI := R.physical.gluing
    ∀ (i : Fin R.physical.bundle.count) (U : Opens M) (s : smoothSectionModule R.physical.bundle U)
      (x : U), x.val ∈ R.physical.bundle.core.baseSet i →
      coordinateSection R.physical.bundle i U
        (((R.physical.comparison.inv ≫ (smoothScalarExtension S).map iso.hom ≫
          R.physical.comparison.hom).val.app (op U)).hom s).val x.val =
        parallel.matrix i x.val *ᵥ coordinateSection R.physical.bundle i U s.val x.val

end MathlibExt.AlgebraicGeometry.HiggsReconstructionIsomorphisms
