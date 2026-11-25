/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticCyclePairings
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real currents on compact complex manifolds and Kähler-current domination

On a compact complex manifold every smooth form is a test form. A current is a
linear functional on smooth forms bounded by a finite family of chart
derivative seminorms on compact subsets of chart domains. Its differential has
the distributional sign `(-1)^(p+1)`. Form currents use the displayed wedge and
coordinate integral. Positivity is tested on real `(n-1,n-1)` forms and is
domination of that literal form current, rather than a free positivity label
or a numeric oracle.

`CurrentDifferentialTheory` (the differential of a current is again bounded) is
a hypothesis class; its instance is requested in
`WantedExt/AlgebraicGeometry/AnalyticCurrentsWanted.lean`.

Reference: J.-P. Demailly and M. Păun, *Numerical characterization of the
Kähler cone of a compact Kähler manifold*, Ann. of Math. 159 (2004),
arXiv:math/0105176v2, Theorem 0.4 (Theorem 0.5 of the published version).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCurrents

open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals AnalyticCyclePairings
open scoped Manifold ContDiff BigOperators

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M]

/-- The `C^m` seminorm of a form on a compact subset of the chart at `a`: the
supremum of the norms of its chart derivatives of order at most `m`. -/
def derivativeSeminorm (p : ℕ) (a : M) (K : Set (Coordinates n)) (m : ℕ)
    (alpha : Forms n M p) : ℝ :=
  sSup {r : ℝ | ∃ (j : ℕ), j ≤ m ∧ ∃ z ∈ K,
    r = ‖iteratedFDeriv ℝ j (chartForm ℝ (Coordinates n) M alpha.val a) z‖}

/-- The finite-seminorm bound is the concrete distribution continuity
condition; on a compact manifold every smooth form is a test form. -/
def IsDistribution [CompactSpace M] (p : ℕ) (T : Forms n M p →ₗ[ℝ] ℝ) : Prop :=
  ∃ (r : ℕ) (a : Fin r → M) (K : Fin r → Set (Coordinates n))
    (m : ℕ) (C : ℝ), 0 ≤ C ∧
    (∀ i, IsCompact (K i) ∧ K i ⊆ chartDomain ℝ (Coordinates n) M ⊤ (a i)) ∧
    ∀ alpha, |T alpha| ≤ C * ∑ i, derivativeSeminorm n M p (a i) (K i) m alpha

/-- A current of degree `p` on a compact complex manifold of complex dimension
`n`: a bounded linear functional on smooth forms of complementary degree. -/
structure Current [CompactSpace M] (p : ℕ) where
  functional : Forms n M (n * 2 - p) →ₗ[ℝ] ℝ
  bounded : IsDistribution n M (n * 2 - p) functional
  degree_le : p ≤ n * 2

variable [CompactSpace M]

/-- The distributional differential `dT(β) = (-1)^(p+1) T(dβ)`. -/
def differentialFunctional {p : ℕ} (T : Current n M p) (h : p + 1 ≤ n * 2) :
    Forms n M (n * 2 - (p + 1)) →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ (p + 1)) • T.functional.comp
    ((castFormLinear n M (by omega)).comp
      (d ℝ (Coordinates n) M (n * 2 - (p + 1))))

/-- The differential of a current is again a current: an instance asserts that for every current $T$
of degree $p$ on the compact complex manifold $M$ of dimension $n$ with $p + 1 \le 2n$, the
distributional differential $\beta \mapsto (-1)^{p+1} T(d\beta)$ (`differentialFunctional`)
satisfies the finite-seminorm bound `IsDistribution`, so that it is a current of degree $p + 1$. -/
class CurrentDifferentialTheory : Prop where
  bounded : ∀ p (T : Current n M p) (h : p + 1 ≤ n * 2),
    IsDistribution n M (n * 2 - (p + 1)) (differentialFunctional n M T h)

def differential [CurrentDifferentialTheory n M] {p : ℕ}
    (T : Current n M p) (h : p + 1 ≤ n * 2) : Current n M (p + 1) :=
  ⟨differentialFunctional n M T h, CurrentDifferentialTheory.bounded p T h, h⟩

variable [WedgeTheory n M] (R : RealCoordinateMap n) (A : IntegrationAtlas n M)
  [IntegrationTheory n M R A]

def formFunctional (p : ℕ) (h : p ≤ n * 2) (alpha : Forms n M p) :
    Forms n M (n * 2 - p) → ℝ :=
  fun beta ↦ integral n M R A (castForm n M (by omega)
    (WedgeTheory.wedge p (n * 2 - p) alpha beta))

def rotation (p : ℕ) (theta : ℝ) (alpha : Forms n M p) :
    RoughForm ℝ (Coordinates n) M ⊤ p :=
  fun x ↦ alpha.val x |>.compContinuousLinearMap
    ((Real.cos theta) • ContinuousLinearMap.id ℝ (Coordinates n) +
      (Real.sin theta) •
        (Complex.I • ContinuousLinearMap.id ℂ (Coordinates n)).restrictScalars ℝ)

def IsBalancedType (p : ℕ) (alpha : Forms n M p) : Prop :=
  ∀ theta : ℝ, rotation n M p theta alpha = alpha.val

def complexFrame (m : ℕ) (v : Fin m → Coordinates n) : Fin (m * 2) → Coordinates n :=
  fun j ↦ let a := (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).symm j
    if a.2 = 0 then v a.1 else Complex.I • v a.1

def IsPositiveTest (h : 0 < n) (beta : Forms n M (n * 2 - 2)) : Prop :=
  IsBalancedType n M (n * 2 - 2) beta ∧
    ∀ (x : M) (v : Fin (n - 1) → Coordinates n),
      0 ≤ beta.val ⟨x, by trivial⟩
        (fun j ↦ complexFrame n (n - 1) v (Fin.cast (by omega) j))

def IsTypeOneOneCurrent (T : Current n M 2) : Prop :=
  ∀ (beta gamma : Forms n M (n * 2 - 2)) (theta : ℝ),
    gamma.val = rotation n M (n * 2 - 2) theta beta →
      T.functional gamma = T.functional beta

def IsClosedCurrent (T : Current n M 2) : Prop :=
  ∀ h : 3 ≤ n * 2, differentialFunctional n M T h = 0

def Dominates (h : 0 < n) (T : Current n M 2) (eta : Forms n M 2) (epsilon : ℝ) : Prop :=
  ∀ beta : Forms n M (n * 2 - 2), IsPositiveTest n M h beta →
    epsilon * formFunctional n M R A 2 (by omega) eta beta ≤ T.functional beta

def Represents [CurrentDifferentialTheory n M] (h : 0 < n) (T : Current n M 2)
    (alpha : ClosedTwoForms n M) : Prop :=
  ∃ S : Current n M 1, ∀ beta : Forms n M (n * 2 - 2),
    T.functional beta - formFunctional n M R A 2 (by omega) alpha.val beta =
      (differential n M S (by omega)).functional beta

end MathlibExt.AlgebraicGeometry.AnalyticCurrents
