/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
public import MathlibExt.AlgebraicGeometry.DivisorDynamics

/-!
# Polarized stability of actual integrable Higgs bundles

Higher-dimensional stability tests coherent torsion-free saturated Higgs
subsheaves, including subsheaves which are not locally free. Generic rank
is fixed by actual dense-open bundle rank. The Hilbert coefficient used for
slope is fixed by the Euler characteristics of actual tensor powers of the
polarizing line; the common Todd contribution cancels in slope comparisons.
No harmonic metric or Chern-class conclusion is assumed in stability.

The Hilbert-polynomial existence dictionary is completed source mathematics:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0),
StacksFrontier/AlgebraicGeometry/Variety/EulerChar/HilbertPolynomial.lean,
HilbertPolynomialNumerical.lean and HilbertPolynomialHighTwist.lean. Its
producer is source integration, not a new Wanted theorem. References:
Simpson, Higgs bundles and local systems (1992), §1, Theorem1/Corollary1.3.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.PolarizedHiggsStability
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open scoped BigOperators

/-- The rank is witnessed on an actual dense Zariski open. -/
def HasGenericRank {X : Scheme.{0}} (F : X.Modules) (r : ℕ) : Prop :=
  ∃ U : X.Opens, Dense (U : Set X) ∧
    IsVectorBundle ((Scheme.Modules.pullback U.ι).obj F) r

/-- Hilbert polynomials on a scheme $X$ over $\mathbb{C}$ with respect to a line bundle $H$, in
dimension $d$: $X$ is Noetherian of Krull dimension $d$, $H$ is ample, and each quasi-coherent sheaf
of finite type $F$ on $X$ is assigned a polynomial $P_F \in \mathbb{Q}[t]$ with
$P_F(n) = \sum_{i \le d} (-1)^i \dim_{\mathbb{C}} H^i(X, F \otimes H^{\otimes n})$ for all
sufficiently large $n$; moreover, for every such $F$ and every $n \ge 0$, each
$H^i(X, F \otimes H^{\otimes n})$ is finite-dimensional, and it vanishes for $i > d$. -/
structure HilbertNumerics (X : ComplexScheme) (H : LineBundle X.left) (d : ℕ) where
  dimension : topologicalKrullDim X.left = d
  [noetherian : IsNoetherian X.left]
  ample : IsAmpleLine H
  polynomial : ∀ F : X.left.Modules, IsFiniteTypeQuasicoherent F → Polynomial ℚ
  normalization : ∀ (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F), ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → (polynomial F hF).eval (n : ℚ) =
      (DivisorDynamics.truncatedEuler X d
        (moduleTensor X.left F (power H.val n)) : ℚ)
  finiteCohomology : ∀ (F : X.left.Modules), IsFiniteTypeQuasicoherent F → ∀ n i : ℕ,
    FiniteDimensional ℂ (cohomology X.hom (moduleTensor X.left F (power H.val n)) i)
  cohomologyAboveDimension : ∀ (F : X.left.Modules), IsFiniteTypeQuasicoherent F → ∀ n i : ℕ,
    d < i → IsZero (cohomology X.hom (moduleTensor X.left F (power H.val n)) i)

/-- This coefficient divided by generic rank differs from usual slope only
by a positive common scaling and a common Todd term on the fixed variety. -/
def slope {X : ComplexScheme} {H : LineBundle X.left} {d : ℕ}
    (N : HilbertNumerics X H d) (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F)
      (r : ℕ) : ℚ :=
  (N.polynomial F hF).coeff (d-1) / r

/-- A saturated invariant coherent subsheaf, with its actual integrable field. -/
def Invariant {X : ComplexScheme} (E : HiggsBundle X)
    (F : X.left.Modules) (i : F ⟶ E.module) : Prop :=
  ∃ theta : F ⟶ moduleTensor X.left F (Omega X 1),
    square theta = 0 ∧ i ≫ E.theta = theta ≫ tensorMap i (𝟙 (Omega X 1))

/-- The actual coherent Higgs bundle, without imposing stability or metrics. -/
structure CoherentBundle (X : ComplexScheme) where
  bundle : HiggsBundle X
  coherent : IsFiniteTypeQuasicoherent bundle.module

/-- Positive-dimensional slope stability. Geometric smooth/projective/integral
hypotheses are explicit on every existence/comparison theorem using this predicate. -/
def IsStable {X : ComplexScheme} {H : LineBundle X.left} {d : ℕ}
    (N : HilbertNumerics X H d) (E : CoherentBundle X) : Prop :=
  0 < d ∧ 0 < E.bundle.rank ∧
  ∀ (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F) (s : ℕ), 0 < s → s < E.bundle.rank →
    HasGenericRank F s → IsTorsionFree F → ∀ i : F ⟶ E.bundle.module,
      Mono i → IsTorsionFree (cokernel i) → Invariant E.bundle F i →
        slope N F hF s < slope N E.bundle.module E.coherent E.bundle.rank

def IsSemistable {X : ComplexScheme} {H : LineBundle X.left} {d : ℕ}
    (N : HilbertNumerics X H d) (E : CoherentBundle X) : Prop :=
  0 < d ∧ 0 < E.bundle.rank ∧
  ∀ (F : X.left.Modules) (hF : IsFiniteTypeQuasicoherent F) (s : ℕ), 0 < s → s < E.bundle.rank →
    HasGenericRank F s → IsTorsionFree F → ∀ i : F ⟶ E.bundle.module,
      Mono i → IsTorsionFree (cokernel i) → Invariant E.bundle F i →
        slope N F hF s ≤ slope N E.bundle.module E.coherent E.bundle.rank

/-- A genuine finite direct sum of stable, same-slope integrable fields. -/
def IsPolystable {X : ComplexScheme} {H : LineBundle X.left} {d : ℕ}
    (N : HilbertNumerics X H d) (E : CoherentBundle X) : Prop :=
  let : HasFiniteBiproducts X.left.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  ∃ (n : ℕ) (F : Fin n → CoherentBundle X),
    (∑ i, (F i).bundle.rank) = E.bundle.rank ∧
    ∃ b : (biproduct fun i => (F i).bundle.module) ≅ E.bundle.module,
      (∀ i, IsStable N (F i)) ∧
      (∀ i, slope N (F i).bundle.module (F i).coherent (F i).bundle.rank =
        slope N E.bundle.module E.coherent E.bundle.rank) ∧
      ∀ i, biproduct.ι (fun j => (F j).bundle.module) i ≫ b.hom ≫ E.bundle.theta =
        (F i).bundle.theta ≫ tensorMap
          (biproduct.ι (fun j => (F j).bundle.module) i ≫ b.hom) (𝟙 (Omega X 1))

end MathlibExt.AlgebraicGeometry.PolarizedHiggsStability
