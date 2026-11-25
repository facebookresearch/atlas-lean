/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Actual H0 torus coactions and section-weight measures

The coaction is characterized through the actual action pullback and line
linearization. Its tensor-section comparison is normalized on every pure
tensor by literal pullback of the regular Laurent function and the section.
Weights are kernels of this fixed coaction minus the fixed character tensor
map. Supports, dimensions and the atomic measures therefore cannot be
supplied as an arbitrary weight sequence.

Finite-dimensional torus decomposition and tensor-section linearity are
source-covered representation/cohomology integration inputs. This file
does not re-request those generic laws as new Wanted results.

Source: Boucksom--Hisamoto--Jonsson, arXiv1504.06568v3,
Theorem A and §§2--3. Mathlib Laurent Hopf/group-scheme/tensor constructions
and the completed LinearizedLineBundles cocycle are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantSectionWeights

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
open MathlibExt.AlgebraicGeometry.LinearizedLineBundles
open MathlibExt.AlgebraicGeometry.GenericSectionMaps
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open scoped TensorProduct BigOperators ENNReal

variable {k : Type} [Field k] (X : Over (Base k)) [ModObj (Torus k) X]
  (M : X.left.Modules)

/-- The actual Laurent function pulled from the first projection. -/
def regularOnProduct (r : LaurentPolynomial k) : Γ((Torus k ⊗ X).left, ⊤) :=
  (fst (Torus k) X).left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv r)

/-- Actual pulled section of the projection module. -/
def projectionSection (s : Sections X M) :
    Sections (Torus k ⊗ X) ((Scheme.Modules.pullback (projection (Torus k) X)).obj M) :=
  pullSection (snd (Torus k) X)
    (𝟙 ((Scheme.Modules.pullback (projection (Torus k) X)).obj M)) s

/-- Literal multiplication of the displayed module section by a regular function. -/
def regularTimesSection (a : Γ((Torus k ⊗ X).left, ⊤))
    (s : Sections (Torus k ⊗ X)
      ((Scheme.Modules.pullback (projection (Torus k) X)).obj M)) :
    Sections (Torus k ⊗ X) ((Scheme.Modules.pullback (projection (Torus k) X)).obj M) := by
  let N := (Scheme.Modules.pullback (projection (Torus k) X)).obj M
  let t : Γ(N, ⊤) := s
  exact a • t

/-- Tensor/global-section comparison pinned to every actual pure tensor. -/
structure TensorSections where
  comparison : Sections X M ⊗[k] LaurentPolynomial k ≃ₗ[k]
    Sections (Torus k ⊗ X) ((Scheme.Modules.pullback (projection (Torus k) X)).obj M)
  normalized : ∀ s r, comparison (s ⊗ₜ[k] r) =
    regularTimesSection X M (regularOnProduct X r) (projectionSection X M s)

/-- The actual linearized action section, before applying the tensor comparison. -/
def actionSection (A : Linearization (Torus k) X M) (s : Sections X M) :
    Sections (Torus k ⊗ X) ((Scheme.Modules.pullback (projection (Torus k) X)).obj M) :=
  homSection (Torus k ⊗ X)
    (pullbackSection (action (Torus k) X) (sectionHom X M s) ≫ A.comparison.hom)

/-- Proof-only linearity adapter to the computed action/tensor coaction. -/
structure SectionCoaction (A : Linearization (Torus k) X M) (T : TensorSections X M) where
  map : Sections X M →ₗ[k] Sections X M ⊗[k] LaurentPolynomial k
  normalized : ∀ s, T.comparison (map s) = actionSection X M A s

variable {X M}

/-- The fixed pure-character tensor map. -/
def characterTensor (w : ℤ) :
    Sections X M →ₗ[k] Sections X M ⊗[k] LaurentPolynomial k :=
  (TensorProduct.mk k (Sections X M) (LaurentPolynomial k)).flip (LaurentPolynomial.T w)

/-- An actual H0 weight space of the normalized coaction. -/
def weightSpace {A : Linearization (Torus k) X M} {T : TensorSections X M}
    (R : SectionCoaction X M A T) (w : ℤ) : Submodule k (Sections X M) :=
  LinearMap.ker (R.map - characterTensor w)

/-- Finite weight decomposition of the global sections $H^0(X, M)$ under a coaction $R$ of
$\mathbb{G}_m = \operatorname{Spec} k[t, t^{-1}]$, for a field $k$, a $k$-scheme $X$ with a
$\mathbb{G}_m$-action and a module $M$ on $X$, where $R$ is normalized by a linearization $A$ of
$M$ through the comparison $T$: $H^0(X, M)$ is finite-dimensional over $k$, only finitely many
$w \in \mathbb{Z}$ have a nonzero weight space $\{s : R(s) = s \otimes t^w\}$, and the dimensions
of these weight spaces add up to $\dim_k H^0(X, M)$. -/
structure FiniteWeights {A : Linearization (Torus k) X M} {T : TensorSections X M}
    (R : SectionCoaction X M A T) where
  finiteSections : Module.Finite k (Sections X M)
  finiteSupport : Set.Finite {w : ℤ | weightSpace R w ≠ ⊥}
  dimension : ∑ w ∈ finiteSupport.toFinset, Module.finrank k (weightSpace R w) =
    Module.finrank k (Sections X M)

/-- The actual atomic degree-m section-weight measure, with its H0 denominator. -/
def weightMeasure {A : Linearization (Torus k) X M} {T : TensorSections X M}
    {R : SectionCoaction X M A T} (W : FiniteWeights R) (m : ℕ) :
    MeasureTheory.Measure ℝ :=
  ∑ w ∈ W.finiteSupport.toFinset,
    ((Module.finrank k (weightSpace R w) : ENNReal) /
      (Module.finrank k (Sections X M) : ENNReal)) •
        MeasureTheory.Measure.dirac ((w : ℝ) / m)

end MathlibExt.AlgebraicGeometry.EquivariantSectionWeights
