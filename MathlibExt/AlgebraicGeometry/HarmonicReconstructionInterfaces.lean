/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Normalized harmonic reconstruction and semisimple horizontal sheaves

Realizations are actual smooth connections with the displayed matrix formula.
A local flat frame is an invertible smooth matrix solving the actual local
parallel equation, with identity initial value. Its comparison with constant
sections is fixed by multiplying actual bundle coordinates by its inverse.

Finite locally constant sheaves are defined by natural local equivalences
with the actual locally constant functions. Semisimplicity requires every
such horizontal subsheaf to have a retraction. No arbitrary representation,
local-system functor, harmonic predicate, or correspondence is supplied.

Source: Carlos Simpson, alg-geom/9604005v1, section 2 and Theorem 2.3,
printed pages 9–11. Native locally constant functions, sheafification and
module-category primitives: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0. The metric/connection/degree source credits are retained in the
three imported geometric modules.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces

open _root_.CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

structure ConnectionRealization (value : OneFormValue B) where
  connection : SmoothConnection B
  normalized : connection.value = value

structure LocalFlatFrame (A : SmoothConnection B) (x : M) where
  domain : Opens M
  index : Fin B.count
  inFrame : domain ≤ frameOpen B index
  contains : x ∈ domain
  matrix : M → Matrices r
  smooth : ContMDiffOn 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r) ∞ matrix domain
  invertible : ∀ y, y ∈ domain → IsUnit (matrix y)
  parallel : ∀ y, y ∈ domain → ∀ u : Coordinates n,
    (show Matrices r from mfderivWithin 𝓘(ℝ, Coordinates n) 𝓘(ℝ, Matrices r)
      matrix (domain : Set M) y u) + A.matrix index y u * matrix y = 0
  initial : matrix x = 1

variable (A : SmoothConnection B) [SectionCalculus B A.value]

structure LocalHorizontalComparison (x : M) (F : LocalFlatFrame B A x) where
  iso : ∀ (V : Opens M), V ≤ F.domain →
    horizontalModule B A.value V ≃ₗ[ℂ] LocallyConstant V (FiberCoordinates r)
  coordinates : ∀ (V : Opens M) (hV : V ≤ F.domain) (s : horizontalModule B A.value V) (y : V),
    iso V hV s y = (F.matrix y.val)⁻¹ *ᵥ coordinateSection B F.index V s.val y.val
  restriction : ∀ (V W : Opens M) (hV : V ≤ F.domain) (hW : W ≤ F.domain) (h : W ≤ V)
    (s : horizontalModule B A.value V) (y : W),
    iso W hW (horizontalRestriction B A.value h s) y = iso V hV s ⟨y.val, h y.property⟩

abbrev CoefficientSheaf := Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)

def LocallyConstantFinite (G : CoefficientSheaf (M := M)) : Prop :=
  ∀ x : M, ∃ (U : Opens M), x ∈ U ∧ ∃ k : ℕ,
    ∃ e : ∀ (V : Opens M), V ≤ U → G.obj.obj (op V) ≃ₗ[ℂ] LocallyConstant V (FiberCoordinates k),
      ∀ (V W : Opens M) (hV : V ≤ U) (hW : W ≤ U) (h : W ≤ V)
        (s : G.obj.obj (op V)) (y : W),
        e W hW ((G.obj.map (homOfLE h).op).hom s) y = e V hV s ⟨y.val, h y.property⟩

variable [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]

def SemisimpleHorizontals : Prop :=
  ∀ (F : CoefficientSheaf (M := M)), LocallyConstantFinite F →
    ∀ i : F ⟶ horizontalSheaf B A.value, Mono i →
      ∃ p : horizontalSheaf B A.value ⟶ F, i ≫ p = 𝟙 F

end MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
