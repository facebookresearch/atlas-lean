/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The normalized wedge and chart integral definitions adapt
TauCetiProject/TauCeti, revision 62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/Geometry/Manifold/DifferentialForm/Wedge/Smooth/Basic.lean and
DifferentialForm/Integration/Chart/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: The Tau Ceti contributors.
Modification notice: use the fixed alternating-tangent chart model,
standard complex real/imaginary coordinates and a finite partition/Lebesgue
sum; retain ordinary smoothness/Stokes proofs as explicit integration inputs.
-/
module

public import MathlibExt.AlgebraicGeometry.KahlerClassGeometry
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinate-defined wedge and integration on complex manifolds

Real coordinates are fixed on every standard real/imaginary basis vector.
The integral is the finite chart-partition sum against ordinary Lebesgue
measure, with the actual chart pullback form. It is not a trace field.
The wedge is fixed on every tangent tuple by the signed-permutation sum
divided by the two factorials.

`WedgeTheory` (the smoothness of that pointwise wedge) and `IntegrationTheory`
(integrability, linearity and Stokes for that integral) are hypothesis
classes; everything using them is conditional on them. Their instances are
requested in `WantedExt/AlgebraicGeometry/ManifoldDifferentialFormsWanted.lean`.
TauCetiProject/TauCeti at 62bbc0596dc3539d488232e4e924a338548ea0a9 proves the
corresponding facts for its own form API in
`Geometry/Manifold/DifferentialForm/Wedge/Smooth/Basic.lean`,
`DifferentialForm/Integration/Chart/Basic.lean` and
`DifferentialForm/Integration/BoundarylessStokes.lean` (Apache 2.0).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals

open KahlerClassGeometry ManifoldDifferentialForms MeasureTheory
open scoped Manifold ContDiff BigOperators

abbrev RealCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin (n * 2))

def standardRealFrame (n : ℕ) (j : Fin (n * 2)) : Coordinates n :=
  let p := (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)).symm j
  EuclideanSpace.single p.1 (if p.2 = 0 then 1 else Complex.I)

structure RealCoordinateMap (n : ℕ) where
  map : RealCoordinates n ≃L[ℝ] Coordinates n
  basis : ∀ j, map (EuclideanSpace.single j 1) = standardRealFrame n j

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M]

abbrev Forms (p : ℕ) := GlobalForms ℝ (Coordinates n) M p

/-- A wedge product on smooth real differential forms on the complex manifold $M$ modelled on
$\mathbb{C}^n$: a smooth $0$-form `unit` with value $1$ at every point, and for all $p, q$ a map
`wedge` sending smooth forms $\alpha$ of degree $p$ and $\beta$ of degree $q$ to a smooth
$(p+q)$-form whose value at every point on every tuple $v$ of tangent vectors is $\frac{1}{p!\,q!}$
times the sum, over the permutations $\sigma$ of $p + q$ indices, of
$\operatorname{sign}(\sigma)\, \alpha(v_{\sigma(1)}, \dots, v_{\sigma(p)})$ times
$\beta(v_{\sigma(p+1)}, \dots, v_{\sigma(p+q)})$. The data are determined by these values, so an
instance amounts to the smoothness of the constant $0$-form $1$ and of the pointwise wedge of smooth
forms. -/
class WedgeTheory where
  unit : Forms n M 0
  unit_value : ∀ x : M, unit.val ⟨x, by trivial⟩ (fun i : Fin 0 ↦ Fin.elim0 i) = 1
  wedge : ∀ p q, Forms n M p → Forms n M q → Forms n M (p + q)
  value : ∀ p q (α : Forms n M p) (β : Forms n M q) (x : M)
      (v : Fin (p + q) → Coordinates n),
    (wedge p q α β).val ⟨x, by trivial⟩ v =
      ((p.factorial : ℝ) * q.factorial)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (p + q)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          α.val ⟨x, by trivial⟩ (fun i ↦ v (σ (Fin.castAdd q i))) *
          β.val ⟨x, by trivial⟩ (fun i ↦ v (σ (Fin.natAdd p i)))

def castForm {p q : ℕ} (h : p = q) : Forms n M p → Forms n M q := by
  cases h
  exact id

def castFormLinear {p q : ℕ} (h : p = q) : Forms n M p →ₗ[ℝ] Forms n M q := by
  cases h
  exact LinearMap.id

def wedgePower [WedgeTheory n M] (α : Forms n M 2) : (p : ℕ) → Forms n M (2 * p)
  | 0 => WedgeTheory.unit
  | p + 1 => castForm n M (Nat.mul_succ 2 p).symm
      (WedgeTheory.wedge (2 * p) 2 (wedgePower α p) α)

/-- Actual smooth partition data with supports inside the selected charts. -/
structure IntegrationAtlas where
  count : ℕ
  centre : Fin count → M
  weight : Fin count → M → ℝ
  smooth : ∀ i, ContMDiff 𝓘(ℝ, Coordinates n) 𝓘(ℝ, ℝ) ∞ (weight i)
  nonnegative : ∀ i x, 0 ≤ weight i x
  sum_one : ∀ x, ∑ i, weight i x = 1
  support : ∀ i, closure (Function.support (weight i)) ⊆
    (extChartAt 𝓘(ℝ, Coordinates n) (centre i)).source
  compact : ∀ i, IsCompact (closure (Function.support (weight i)))

variable (C : RealCoordinateMap n) (A : IntegrationAtlas n M)

def chartDensity (α : Forms n M (n * 2)) (i : Fin A.count) (z : RealCoordinates n) : ℝ :=
  A.weight i ((extChartAt 𝓘(ℝ, Coordinates n) (A.centre i)).symm (C.map z)) *
    chartForm ℝ (Coordinates n) M α.val (A.centre i) (C.map z)
      (standardRealFrame n)

/-- The literal finite coordinate/Lebesgue integral. -/
def integral (α : Forms n M (n * 2)) : ℝ :=
  ∑ i, ∫ z : RealCoordinates n, chartDensity n M C A α i z

/-- Integrability, linearity and Stokes' theorem for `integral`, the integral of top-degree forms on
$M$ defined by the real coordinates $C$ and the finite smooth partition of unity $A$ subordinate to
charts: an instance asserts that every chart density of every smooth $2n$-form is Lebesgue
integrable, that `integral` is additive and commutes with real scalars, and that `integral` vanishes
on $d\alpha$ for every smooth form $\alpha$ of degree $p$ with $p + 1 = 2n$. -/
class IntegrationTheory : Prop where
  integrable : ∀ α i, Integrable (chartDensity n M C A α i)
  add : ∀ α β, integral n M C A (α + β) = integral n M C A α + integral n M C A β
  smul : ∀ (c : ℝ) α, integral n M C A (c • α) = c * integral n M C A α
  stokes : ∀ p (h : p + 1 = n * 2) (α : Forms n M p),
    integral n M C A (castForm n M h (d ℝ (Coordinates n) M p α)) = 0

def integralLinear [IntegrationTheory n M C A] : Forms n M (n * 2) →ₗ[ℝ] ℝ where
  toFun := integral n M C A
  map_add' := IntegrationTheory.add
  map_smul' := IntegrationTheory.smul

end MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals
