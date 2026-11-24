/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# The holomorphic kernel of the actual harmonic bar connection

The bar operator includes the projected derivative of the section, as well
as the extracted bar-connection matrix. Its kernel is taken on actual smooth
sections in every native bundle frame. The coefficient action is multiplication
by actual holomorphic functions. The ordinary local Leibniz source facts are
separate from integrability, metric existence and the Hodge correspondence.

Simpson, alg-geom/9604005v1, section 2, printed pages 9--11. In particular
the resulting holomorphic frames need not be the original smooth frames.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels

open CategoryTheory Opposite TopologicalSpace Set
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HolomorphicCoefficientSheaves
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

/-- Projection of the full covariant derivative, including the derivative of the section. -/
def barConnectionValue (h : HermitianMetric B) (A : SmoothConnection B)
    (i : Fin B.count) (U : Opens M) (s : RoughSection B U) (x : U)
    (u : Coordinates n) : FiberCoordinates r :=
  (1 / 2 : ℂ) •
    (connectionValue B (unitaryPart B h A) i U s x u +
      Complex.I • connectionValue B (unitaryPart B h A) i U s x (Complex.I • u))

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- The explicit section-derivative and extracted connection formula. -/
theorem barConnectionValue_formula (h : HermitianMetric B) (A : SmoothConnection B)
    (i : Fin B.count) (U : Opens M) (s : RoughSection B U) (x : U)
    (u : Coordinates n) :
    barConnectionValue B h A i U s x u =
      (1 / 2 : ℂ) •
        ((show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
          𝓘(ℝ, FiberCoordinates r) (coordinateSection B i U s)
          ((U : Set M) ∩ B.core.baseSet i) x.val u) +
          Complex.I • (show FiberCoordinates r from mfderivWithin 𝓘(ℝ, Coordinates n)
            𝓘(ℝ, FiberCoordinates r) (coordinateSection B i U s)
            ((U : Set M) ∩ B.core.baseSet i) x.val (Complex.I • u))) +
        extractedBarConnection B h A i x.val u *ᵥ coordinateSection B i U s x.val := by
  simp only [barConnectionValue, connectionValue, extractedBarConnection, typeZeroOne,
    Matrix.add_mulVec, Matrix.smul_mulVec]
  module

/-- Holomorphic sections are the kernel on every actual smooth frame and tangent vector. -/
def IsBarHolomorphic (h : HermitianMetric B) (A : SmoothConnection B)
    (U : Opens M) (s : RoughSection B U) : Prop :=
  IsSmoothSection B U s ∧
    ∀ i (x : U), x.val ∈ B.core.baseSet i → ∀ u,
      barConnectionValue B h A i U s x u = 0

variable (h : HermitianMetric B) (A : SmoothConnection B)
  [SectionCalculus B (unitaryPart B h A)]

/-- The actual complex-linear kernel, with no metric-existence or integrability input. -/
def barKernel (U : Opens M) : Submodule ℂ (RoughSection B U) where
  carrier := {s | IsBarHolomorphic B h A U s}
  zero_mem' := by
    refine ⟨SectionCalculus.smooth_zero (B := B) (A := unitaryPart B h A) U, ?_⟩
    intro i x hx u
    simp only [barConnectionValue,
      SectionCalculus.zero (B := B) (A := unitaryPart B h A) i U x hx,
      smul_zero, add_zero]
  add_mem' := by
    intro s t hs ht
    refine ⟨SectionCalculus.smooth_add (B := B) (A := unitaryPart B h A)
      U _ _ hs.1 ht.1, ?_⟩
    intro i x hx u
    have ha := SectionCalculus.add (B := B) (A := unitaryPart B h A)
      i U _ _ hs.1 ht.1 x hx
    calc
      barConnectionValue B h A i U (s + t) x u =
          barConnectionValue B h A i U s x u + barConnectionValue B h A i U t x u := by
        simp only [barConnectionValue, ha]
        module
      _ = 0 := by rw [hs.2 i x hx u, ht.2 i x hx u, add_zero]
  smul_mem' c s hs := by
    refine ⟨SectionCalculus.smooth_smul (B := B) (A := unitaryPart B h A)
      U c s hs.1, ?_⟩
    intro i x hx u
    have ha := SectionCalculus.smul (B := B) (A := unitaryPart B h A)
      i U c s hs.1 x hx
    simp only [barConnectionValue, ha]
    calc
      (1 / 2 : ℂ) • (c • connectionValue B (unitaryPart B h A) i U s x u +
          Complex.I • c • connectionValue B (unitaryPart B h A) i U s x (Complex.I • u)) =
        c • barConnectionValue B h A i U s x u := by
          dsimp [barConnectionValue]
          module
      _ = 0 := by rw [hs.2 i x hx u, smul_zero]

/-- Restriction is literal restriction of the same bundle section. -/
def barRestriction {U V : Opens M} (a : V ≤ U) :
    barKernel B h A U →ₗ[ℂ] barKernel B h A V where
  toFun s := ⟨restrictSection B a s.val, by
    refine ⟨SectionCalculus.smooth_restrict (B := B) (A := unitaryPart B h A)
      U V a s.val s.property.1, ?_⟩
    intro i x hx u
    simp only [barConnectionValue,
      SectionCalculus.restriction (B := B) (A := unitaryPart B h A)
        i U V a s.val s.property.1 x hx]
    exact s.property.2 i ⟨x.val, a x.property⟩ hx u⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- Actual kernel sections and their actual restriction form the coefficient presheaf. -/
def barPresheaf : (Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ModuleCat.of ℂ (barKernel B h A U.unop)
  map f := ModuleCat.ofHom (barRestriction B h A f.unop.le)
  map_id U := by apply ModuleCat.hom_ext; ext s; rfl
  map_comp f g := by apply ModuleCat.hom_ext; ext s; rfl

end MathlibExt.AlgebraicGeometry.HarmonicHolomorphicSectionKernels
