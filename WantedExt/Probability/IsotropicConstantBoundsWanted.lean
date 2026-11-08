/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Geometry.IsotropicCube
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import WantedExt.Geometry.HyperplaneSlicingUniversalWanted

/-!
# Established bounds for entropy-based isotropic constants

Source: optimization catalogue `constants/20b.md`, revision
2c1968cd520b60f1cf3cf50749f7285e800e4e15. These private wanted declarations
record unproved claims, not theorem assumptions exported to downstream proofs.
The unresolved personal-communication exponent has no invented exact value.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.IsotropicConstant

/-- Bourgain's classical bound, with one universal multiplier before dimension.
Source: catalogue [Bou1991], [Bou2002]; arXiv:2412.15044v1, Introduction. -/
private theorem_wanted bourgain1991_2002_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤
        ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4) * Real.log n)

/-- Removal of the logarithmic factor.
Source: catalogue [K2006]; arXiv:2412.15044v1, Introduction. -/
private theorem_wanted klartag2006_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4))

/-- The catalogue's weaker subpolynomial form of Chen's bound.
Source: catalogue [Che2021]; KL2022 equation (1.1) has sqrt(log log(3n)). -/
private theorem_wanted chen2021_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (Real.log n) * Real.log (Real.log n)))

/-- The first polylogarithmic slicing bound.
Source: arXiv:2203.15551v2, Introduction, equation labelled eq_1528. -/
private theorem_wanted klartagLehec2022_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤ ENNReal.ofReal (C * (Real.log n) ^ 4)

/-- The exact algebraic upper exponent, not an exact rational for `2.223...`.
Source: Jambulapati--Lee--Vempala, arXiv:2208.11644, Theorem 22, thm:main_result. -/
private theorem_wanted jlv2022_squaredRadius_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      squaredRadiusThinShellWidth n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          ((1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- The actual body/thin-shell transfer underlying the slicing consequence.
Source: KL2022 equation eq_435, citing Eldan--Klartag; its section convention
and the determinant body convention are comparable up to universal factors. -/
private theorem_wanted eldanKlartag_body_squaredRadius_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ K : FullDimensionalBody n,
        ENNReal.ofReal (bodyIsotropicConstant K) ≤
          ENNReal.ofReal C * squaredRadiusThinShellWidth n

/-- JLV's slicing consequence requires the preceding actual-body transfer.
Source: catalogue [JLV2022]; KL2024 Introduction reports this consequence. -/
private theorem_wanted jlv2022_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          ((1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- Klartag's square-root logarithmic bound.
Source: catalogue [K2023]; arXiv:2412.15044v1, Introduction. -/
private theorem_wanted klartag2023_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤ ENNReal.ofReal (C * Real.sqrt (Real.log n))

/-- Guan's double-logarithmic bound.
Source: catalogue [Gua2024]; arXiv:2412.15044v1, first paragraph. -/
private theorem_wanted guan2024_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionBodySupremum n ≤ ENNReal.ofReal (C * Real.log (Real.log n))

/-- Dimension-free body boundedness is established, not an open conjecture.
Source: arXiv:2412.15044v1, Theorem 1.2. -/
private theorem_wanted klartagLehec2024_body_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ K : FullDimensionalBody n, bodyIsotropicConstant K ≤ C

/-- The entropy-based law bound, including actual positive-dimensional affine spans.
Source: arXiv:2412.15044v1, equation eq_1910. -/
private theorem_wanted klartagLehec2024_intrinsicLaw_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ μ : IntrinsicLogConcaveLaw n, intrinsicLawIsotropicConstant μ ≤ C

/-- The source's final primary constant bound, recorded as a known unproved result.
Source: catalogue [KL2024]; arXiv:2412.15044v1, equation eq_1910. -/
private theorem_wanted entropyIsotropicConstant_lt_top : entropyIsotropicConstant < ⊤

/-- Actual simplex bodies asymptotically attain 1/e, with affine independence.
Source: catalogue lower-bound row and KL2024 Introduction after Theorem 1.2. -/
private theorem_wanted simplex_isotropicConstant_limit :
    ∃ K : (n : ℕ) → FullDimensionalBody (n + 1),
      (∀ n : ℕ, ∃ s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin (n + 1))) (n + 1),
        ((K n).body : Set (EuclideanSpace ℝ (Fin (n + 1)))) =
          convexHull ℝ (Set.range s.points)) ∧
      Filter.Tendsto (fun n : ℕ => bodyIsotropicConstant (K n))
        Filter.atTop (nhds (Real.exp (-1)))

/-- The global simplex lower bound; it is not a lower bound for every law.
Source: catalogue lower-bound row, asymptotically attained by simplices. -/
private theorem_wanted inv_e_le_entropyIsotropicConstant :
    ENNReal.ofReal (Real.exp (-1)) ≤ entropyIsotropicConstant

/-- The actual volume-one coordinate cube in every positive dimension.
Source: catalogue cube lower-bound row. The n=1 case is proved in IsotropicCube. -/
private theorem_wanted coordinateCube_benchmark :
    ∀ n : ℕ, 0 < n → ∃ K : FullDimensionalBody n,
      (K.body : Set (EuclideanSpace ℝ (Fin n))) =
        {x | ∀ i : Fin n, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ (1 / 2 : ℝ)} ∧
      volume (K.body : Set (EuclideanSpace ℝ (Fin n))) = 1 ∧
      bodyIsotropicConstant K = 1 / Real.sqrt 12

/-- A separate lower bound for every actual intrinsic log-concave law.
Source: arXiv:2412.15044v1, equation eq_1910, left inequality. -/
private theorem_wanted every_intrinsicLaw_gaussian_lower :
    ∀ n : ℕ, ∀ μ : IntrinsicLogConcaveLaw n,
      1 / Real.sqrt (2 * Real.pi * Real.exp 1) ≤ intrinsicLawIsotropicConstant μ

/-- The actual standard Gaussian law, density entropy, covariance, and sharp value.
Source: arXiv:2412.15044v1, equality discussion after eq_1910. -/
private theorem_wanted standardGaussian_benchmark :
    ∀ n : ℕ, 0 < n → ∃ μ : LogConcaveLaw n,
      μ.law = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) ∧
      covarianceMatrix μ.law = 1 ∧
      differentialEntropy μ.density = (n : ℝ) / 2 * Real.log (2 * Real.pi * Real.exp 1) ∧
      lawIsotropicConstant μ = 1 / Real.sqrt (2 * Real.pi * Real.exp 1)

/-- Body affine invariance uses the actual image body under an affine equivalence.
Source: catalogue body definition; arXiv:2412.15044v1, Introduction. -/
private theorem_wanted body_affine_invariance :
    ∀ n : ℕ, ∀ K : FullDimensionalBody n,
      ∀ T : AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)),
        ∃ K' : FullDimensionalBody n,
          (K'.body : Set (EuclideanSpace ℝ (Fin n))) =
            T '' (K.body : Set (EuclideanSpace ℝ (Fin n))) ∧
          bodyIsotropicConstant K' = bodyIsotropicConstant K

/-- The intrinsic value must be independent of the actual orthonormal chart.
Source: catalogue proper-affine-subspace convention; KL2024 after eq_1750. -/
private theorem_wanted intrinsic_chart_independence :
    ∀ n : ℕ, ∀ μ ν : IntrinsicLogConcaveLaw n, μ.law = ν.law →
      intrinsicLawIsotropicConstant μ = intrinsicLawIsotropicConstant ν

/-- The full-dimensional coordinate domain embeds without changing its actual law.
Source: catalogue definition of L_n^lc; KL2024 intrinsic convention. -/
private theorem_wanted fullDimensional_intrinsic_representation :
    ∀ n : ℕ, ∀ μ : LogConcaveLaw n, ∃ ν : IntrinsicLogConcaveLaw n,
      ν.dimension = n ∧ ν.law = μ.law ∧
      intrinsicLawIsotropicConstant ν = lawIsotropicConstant μ

/-- Push-forward invariance for an actual injective affine map.
Source: arXiv:2412.15044v1, displayed affine invariance after eq_1750. -/
private theorem_wanted intrinsic_affine_invariance :
    ∀ n N : ℕ, ∀ μ : IntrinsicLogConcaveLaw n,
      ∀ T : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin N),
        Function.Injective T → ∃ ν : IntrinsicLogConcaveLaw N,
          ν.law = μ.law.map T ∧
          intrinsicLawIsotropicConstant ν = intrinsicLawIsotropicConstant μ

/-- Reverse comparison asserts an actual body, not an unconstrained scalar.
The explicit radial Ball-body construction remains a source-acquisition gap.
Source: catalogue Ball1988/K2006 comparison; KL2024 discussion before eq_1910. -/
private theorem_wanted law_body_reverse_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ μ : LogConcaveLaw n,
      ∃ K : FullDimensionalBody n, lawIsotropicConstant μ ≤ C * bodyIsotropicConstant K

/-- Global body and entropy-law finiteness are equivalent up to universal factors.
Source: catalogue body/law comparison paragraph and KL2024 before eq_1910. -/
private theorem_wanted body_law_finiteness_equivalence :
    bodySupremum < ⊤ ↔ entropyIsotropicConstant < ⊤

/-- The consequence is the existing proposition about actual hyperplane sections.
Source: catalogue slicing paragraph; KL2024 Theorems 1.1 and 1.2. -/
private theorem_wanted entropy_finiteness_implies_slicing :
    entropyIsotropicConstant < ⊤ →
      MathlibExt.Geometry.HyperplaneSlicingUniversalWanted.conjecture

end MathlibExt.Probability.IsotropicConstant
