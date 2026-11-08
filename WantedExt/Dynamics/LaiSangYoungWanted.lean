/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lai-Sang Young entropy–dimension–Lyapunov theorem, Margulis–Ruelle inequality, Pesin entropy formula (symplectic surface case)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.LaiSangYoung` — entropy_dimension_lyapunov (manifest `manifests/problems/entropy_dimension_lyapunov.toml`, rev 1, submitter Kim Morrison, status archived); margulis_ruelle (manifest `manifests/problems/margulis_ruelle.toml`, rev 1, submitter Kim Morrison, status archived); pesin_formula (manifest `manifests/problems/pesin_formula.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.LaiSangYoungWanted` namespace. Mathematical
statements are unchanged. Source: L.-S. Young, *Dimension, entropy and Lyapunov exponents*, Ergodic Theory Dynam. Systems 2 (1982), 109–124. Knill, *Some fundamental theorems in mathematics*, §103. D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Brasil. Mat. 9 (1978); G. A. Margulis (1968, unpublished). Knill, *Some fundamental theorems in mathematics*, §103. Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math. Surveys 32 (1977). Knill, *Some fundamental theorems in mathematics*, §103.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.LaiSangYoungWanted
namespace Dynamics

/-!
# The Lai-Sang Young entropy–dimension–Lyapunov theorem and relatives

This module contributes three category-(b) eval problems from §103 of the Knill
survey (`sections/103-diffeomorphisms.md`):

* `entropy_dimension_lyapunov` — Lai-Sang Young (1982): for a `C²`-diffeomorphism
  `T` of a compact surface and an ergodic invariant measure `μ`,
  `h_μ(T) = dim(μ) · λ(T,μ) / 2`.
* `pesin_formula` — Pesin (1977): the symplectic specialisation `h_μ = λ₁`.
* `margulis_ruelle` — Margulis (1968) / Ruelle (1978): `h_μ ≤ λ₁⁺ + λ₂⁺`.

The shared trusted helper definitions (`EucPlane`, `dimMeasure`,
`IsMeasurablePartition`, `partitionEntropy`, `iteratedJoin`, `entropyW`,
`kolmogorovSinaiEntropy`, `lyapunovUpperAt`, `lyapunovLowerAt`,
`harmonicMeanLyapunov`) are non-holes. Mathlib has `dimH`, `Ergodic`,
`MeasurePreserving`, `Real.negMulLog`, and `fderiv`, but no Kolmogorov–Sinai
entropy, no Lyapunov exponents / Oseledec theorem, and none of these
theorems. The surface is modelled on `EuclideanSpace ℝ (Fin 2)` with a compact
invariant `K` (planar partial-scope statement: a compact surface is not generally covered by one Euclidean chart, so this global Euclidean formulation is a strict specialization of the manifold theorem, not an equivalent formulation).
-/

open scoped ENNReal
open MeasureTheory Filter Topology Real

/-- The Euclidean plane, used as the chart codomain for a compact surface. -/
abbrev EucPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The **Hausdorff dimension of a measure**: the infimum of Hausdorff
dimensions of Borel sets of full `μ`-measure. -/
noncomputable def dimMeasure {M : Type*} [EMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ |
    ∃ s : Set M, MeasurableSet s ∧ μ sᶜ = 0 ∧ dimH s = d}

/-- A finite **measurable partition** (mod `μ`-null sets). -/
structure IsMeasurablePartition {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (P : Finset (Set M)) : Prop where
  measurable : ∀ A ∈ P, MeasurableSet A
  cover : μ (⋃ A ∈ P, A)ᶜ = 0
  disjoint : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → μ (A ∩ B) = 0

/-- Shannon entropy `H_μ(P) = -∑ μ(A) log μ(A)` of a finite partition
(`0 log 0 = 0` via `Real.negMulLog`). -/
noncomputable def partitionEntropy {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (P : Finset (Set M)) : ℝ :=
  ∑ A ∈ P, Real.negMulLog (μ A).toReal

/-- The join `∨_{k=0}^{n-1} T^{-k} P` of pullback partitions. -/
noncomputable def iteratedJoin {M : Type*} (T : M → M)
    (P : Finset (Set M)) (n : ℕ) : Finset (Set M) :=
  (Fintype.piFinset (fun _ : Fin n => P)).image
    (fun f : Fin n → Set M => ⋂ k : Fin n, T^[(k : ℕ)] ⁻¹' f k)

/-- The **entropy of `T` w.r.t. a partition `P`**:
`limsup (1/n) H_μ(∨_{k<n} T^{-k} P)`. -/
noncomputable def entropyW {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M) (P : Finset (Set M)) : ℝ :=
  Filter.limsup
    (fun n : ℕ => partitionEntropy μ (iteratedJoin T P n) / n) atTop

/-- **Kolmogorov–Sinai entropy** of `(M, T, μ)`: the supremum of `entropyW`
over finite measurable partitions. -/
noncomputable def kolmogorovSinaiEntropy {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M) : ℝ :=
  sSup {h | ∃ P : Finset (Set M), IsMeasurablePartition μ P ∧ entropyW μ T P = h}

/-- **Upper Lyapunov exponent** at `x`: growth rate of `‖DT^n_x‖`. -/
noncomputable def lyapunovUpperAt
    (T : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  Filter.limsup
    (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n) atTop

/-- **Lower Lyapunov exponent** at `x`: `-limsup (1/n) log ‖(DT^n_x)⁻¹‖`. -/
noncomputable def lyapunovLowerAt
    (T : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  -Filter.limsup
    (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) atTop

/-- The **harmonic mean of `λ₁, −λ₂`**. -/
noncomputable def harmonicMeanLyapunov (lam1 lam2 : ℝ) : ℝ :=
  2 * lam1 * (-lam2) / (lam1 - lam2)

/- **Lai-Sang Young's entropy–dimension–Lyapunov theorem (1982).** For a
`C²`-diffeomorphism `T` of the plane with smooth inverse `T_inv` and an ergodic
invariant probability measure `μ` on a compact invariant `K`,
`h_μ(T) = dim(μ) · λ(T,μ) / 2`, with `λ(T,μ)` the harmonic mean of `λ₁, −λ₂`. -/
/-- Source: L.-S. Young, *Dimension, entropy and Lyapunov exponents*, Ergodic Theory Dynam. Systems 2 (1982), 109–124. Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `entropy_dimension_lyapunov`. -/
public theorem_wanted entropy_dimension_lyapunov
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0)
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ) :
    kolmogorovSinaiEntropy μ T =
      (dimMeasure μ).toReal *
        harmonicMeanLyapunov
          (∫ x, lyapunovUpperAt T x ∂μ)
          (∫ x, lyapunovLowerAt T x ∂μ) / 2

/- **Pesin formula (1977).** Symplectic surface case (`λ₁ = −λ₂`,
`dim(μ) = 2`): `h_μ(T) = λ₁`. -/
/-- Source: Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math. Surveys 32 (1977). Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `pesin_formula`. -/
public theorem_wanted pesin_formula
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0)
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ)
    (hμ_dim : dimMeasure μ = 2)
    (hlam_sym : ∫ x, lyapunovUpperAt T x ∂μ
        = -∫ x, lyapunovLowerAt T x ∂μ) :
    kolmogorovSinaiEntropy μ T = ∫ x, lyapunovUpperAt T x ∂μ

/- **Margulis–Ruelle inequality (1968/1978).** `h_μ(T) ≤ λ₁⁺ + λ₂⁺`. -/
/-- Source: D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Brasil. Mat. 9 (1978); G. A. Margulis (1968, unpublished). Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `margulis_ruelle`. -/
public theorem_wanted margulis_ruelle
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0)
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ) :
    kolmogorovSinaiEntropy μ T
      ≤ max 0 (∫ x, lyapunovUpperAt T x ∂μ)
          + max 0 (∫ x, lyapunovLowerAt T x ∂μ)

end Dynamics

end MathlibExt.Dynamics.LaiSangYoungWanted
