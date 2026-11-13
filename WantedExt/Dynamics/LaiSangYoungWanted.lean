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

/-- **Euclidean plane.** The Euclidean plane $\mathbb{R}^2$ with its Euclidean inner product and
norm. The theorems of this module model a compact surface by a compact invariant subset of
this plane. -/
abbrev EucPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- **Hausdorff dimension of a measure.** For a measure $\mu$ on an extended metric space $M$
equipped with a σ-algebra, the Hausdorff dimension of $\mu$ is the infimum, in $[0, \infty]$, of
the Hausdorff dimensions of the measurable sets $s \subseteq M$ with $\mu(M \setminus s) = 0$. -/
noncomputable def dimMeasure {M : Type*} [EMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ |
    ∃ s : Set M, MeasurableSet s ∧ μ sᶜ = 0 ∧ dimH s = d}

/-- **Measurable partition modulo null sets.** Let $\mu$ be a measure on a measurable space $M$.
A finite family $P$ of subsets of $M$ is a measurable partition of $M$ modulo $\mu$-null sets
when every member of $P$ is measurable, the complement of the union of the members of $P$ has
$\mu$-measure $0$, and any two distinct members $A \ne B$ of $P$ satisfy $\mu(A \cap B) = 0$. -/
structure IsMeasurablePartition {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (P : Finset (Set M)) : Prop where
  measurable : ∀ A ∈ P, MeasurableSet A
  cover : μ (⋃ A ∈ P, A)ᶜ = 0
  disjoint : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → μ (A ∩ B) = 0

/-- **Shannon entropy of a finite family of sets.** For a measure $\mu$ on a measurable space $M$
and a finite collection $P$ of subsets of $M$, the entropy of $P$ is
$H_\mu(P) = \sum_{A \in P} -\mu(A) \log \mu(A)$, where $\log$ is the natural logarithm, with the
convention $0 \log 0 = 0$. Here $\mu(A)$ is taken as a real number, so a set of infinite measure
contributes $0$.

It is applied to finite measurable partitions $P$. -/
noncomputable def partitionEntropy {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (P : Finset (Set M)) : ℝ :=
  ∑ A ∈ P, Real.negMulLog (μ A).toReal

/-- **Iterated join of a partition.** For a map $T : M \to M$, a finite family $P$ of subsets of
$M$ and $n \in \mathbb{N}$, the iterated join $\bigvee_{k=0}^{n-1} T^{-k} P$ is the finite family
of all sets $\bigcap_{k=0}^{n-1} T^{-k}(A_k)$ with $A_0, \dots, A_{n-1} \in P$, where $T^{-k}(A)$
is the preimage of $A$ under the $k$-th iterate $T^k$. For $n = 0$ it is $\{M\}$. -/
noncomputable def iteratedJoin {M : Type*} (T : M → M)
    (P : Finset (Set M)) (n : ℕ) : Finset (Set M) :=
  (Fintype.piFinset (fun _ : Fin n => P)).image
    (fun f : Fin n → Set M => ⋂ k : Fin n, T^[(k : ℕ)] ⁻¹' f k)

/-- **Entropy of a map relative to a partition.** Let $\mu$ be a measure on a measurable space
$M$, let $T : M \to M$ be a map and let $P$ be a finite family of subsets of $M$. The entropy of
$T$ relative to $P$ is
$$h_\mu(T, P) = \limsup_{n \to \infty} \frac{1}{n} H_\mu\Big(\bigvee_{k=0}^{n-1} T^{-k} P\Big),$$
where $\bigvee_{k=0}^{n-1} T^{-k} P$ is the iterated join of $P$ under $T$; the Shannon entropy
of a finite family $Q$ of sets is $H_\mu(Q) = \sum_{A \in Q} -\mu(A) \log \mu(A)$, with
$0 \log 0 = 0$ and with $\mu(A)$ replaced by $0$ when $\mu(A) = \infty$; and the limit superior
is taken to be $0$ when it is $+\infty$ or $-\infty$. -/
noncomputable def entropyW {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M) (P : Finset (Set M)) : ℝ :=
  Filter.limsup
    (fun n : ℕ => partitionEntropy μ (iteratedJoin T P n) / n) atTop

/-- **Kolmogorov–Sinai entropy.** Let $\mu$ be a measure on a measurable space $M$ and let
$T : M \to M$ be a map. The Kolmogorov–Sinai entropy $h_\mu(T)$ is the supremum of the
entropies $h_\mu(T, P)$ of $T$ relative to $P$ over all finite measurable partitions $P$ of $M$
modulo $\mu$-null sets, taken to be $0$ when these entropies are not bounded above. -/
noncomputable def kolmogorovSinaiEntropy {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (T : M → M) : ℝ :=
  sSup {h | ∃ P : Finset (Set M), IsMeasurablePartition μ P ∧ entropyW μ T P = h}

/-- **Upper Lyapunov exponent.** For a map $T : \mathbb{R}^2 \to \mathbb{R}^2$ of the Euclidean
plane and a point $x \in \mathbb{R}^2$, the upper Lyapunov exponent of $T$ at $x$ is
$$\overline{\lambda}(T, x) = \limsup_{n \to \infty} \frac{1}{n} \log \|D(T^n)_x\|,$$
where $D(T^n)_x$ is the derivative at $x$ of the $n$-th iterate $T^n$, taken to be $0$ when
$T^n$ is not differentiable at $x$; $\|\cdot\|$ is the operator norm; $\log 0 = 0$; and the
limit superior is taken to be $0$ when it is $+\infty$ or $-\infty$. -/
noncomputable def lyapunovUpperAt
    (T : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  Filter.limsup
    (fun n : ℕ => Real.log ‖fderiv ℝ (T^[n]) x‖ / n) atTop

/-- **Lower Lyapunov exponent.** For a map $T : \mathbb{R}^2 \to \mathbb{R}^2$ of the Euclidean
plane and a point $x \in \mathbb{R}^2$, the lower Lyapunov exponent of $T$ at $x$ is
$$\underline{\lambda}(T, x) = -\limsup_{n \to \infty} \frac{1}{n} \log \|(D(T^n)_x)^{-1}\|,$$
where $D(T^n)_x$ is the derivative at $x$ of the $n$-th iterate $T^n$, taken to be $0$ when
$T^n$ is not differentiable at $x$; the inverse $(D(T^n)_x)^{-1}$ is taken to be $0$ when
$D(T^n)_x$ is not invertible; $\|\cdot\|$ is the operator norm; $\log 0 = 0$; and the limit
superior is taken to be $0$ when it is $+\infty$ or $-\infty$. -/
noncomputable def lyapunovLowerAt
    (T : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  -Filter.limsup
    (fun n : ℕ => Real.log ‖(fderiv ℝ (T^[n]) x).inverse‖ / n) atTop

/-- **Harmonic mean of Lyapunov exponents.** For real numbers $\lambda_1$ and $\lambda_2$, this
is the harmonic mean $\frac{2 \lambda_1 (-\lambda_2)}{\lambda_1 - \lambda_2}$ of $\lambda_1$ and
$-\lambda_2$, taken to be $0$ when $\lambda_1 = \lambda_2$. -/
noncomputable def harmonicMeanLyapunov (lam1 lam2 : ℝ) : ℝ :=
  2 * lam1 * (-lam2) / (lam1 - lam2)

/- **Lai-Sang Young's entropy–dimension–Lyapunov theorem (1982).** For a
`C²`-diffeomorphism `T` of the plane with smooth inverse `T_inv` and an ergodic
invariant probability measure `μ` on a compact invariant `K`,
`h_μ(T) = dim(μ) · λ(T,μ) / 2`, with `λ(T,μ)` the harmonic mean of `λ₁, −λ₂`. -/
/-- **Young's entropy–dimension–Lyapunov formula (planar case).** Let $T$ be a $C^2$
diffeomorphism of the Euclidean plane $\mathbb{R}^2$: $T$ has a two-sided inverse $T^{-1}$ and
both $T$ and $T^{-1}$ are $C^2$. Let $K \subseteq \mathbb{R}^2$ be a compact set with
$T(K) = K$, and let $\mu$ be a Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$ that is $T$-invariant and ergodic for $T$. Let $\lambda_1$
and $\lambda_2$ be the $\mu$-integrals of the upper and the lower Lyapunov exponent of $T$. Then
the Kolmogorov–Sinai entropy of $T$ with respect to $\mu$ is
$$h_\mu(T) = \frac{\dim(\mu) \cdot H}{2},$$
where $\dim(\mu)$ is the Hausdorff dimension of $\mu$ and
$H = \frac{2 \lambda_1 (-\lambda_2)}{\lambda_1 - \lambda_2}$ is the harmonic mean of $\lambda_1$
and $-\lambda_2$, taken to be $0$ when $\lambda_1 = \lambda_2$.

Source: L.-S. Young, *Dimension, entropy and Lyapunov exponents*, Ergodic Theory Dynam. Systems 2 (1982), 109–124. Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `entropy_dimension_lyapunov`. -/
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
/-- **Pesin entropy formula (planar case).** Let $T$ be a $C^2$ diffeomorphism of the Euclidean
plane $\mathbb{R}^2$, that is, a $C^2$ map with a $C^2$ two-sided inverse. Let
$K \subseteq \mathbb{R}^2$ be a compact set with $T(K) = K$, and let $\mu$ be an ergodic
$T$-invariant Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$. Write $h_\mu(T)$ for the Kolmogorov–Sinai entropy of $T$
with respect to $\mu$, and $\lambda_1(x)$ and $\lambda_2(x)$ for the upper and lower Lyapunov
exponents of $T$ at $x$. Suppose that the Hausdorff dimension of $\mu$ equals $2$ and that
$\int \lambda_1 \, d\mu = -\int \lambda_2 \, d\mu$. Then $h_\mu(T) = \int \lambda_1 \, d\mu$.

Source: Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math. Surveys 32 (1977). Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `pesin_formula`. -/
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
/-- **Margulis–Ruelle inequality (planar case).** Let $T$ be a $C^2$ diffeomorphism of the
Euclidean plane $\mathbb{R}^2$, that is, a $C^2$ map with a $C^2$ two-sided inverse. Let
$K \subseteq \mathbb{R}^2$ be a compact set with $T(K) = K$, and let $\mu$ be an ergodic
$T$-invariant Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$. Write $h_\mu(T)$ for the Kolmogorov–Sinai entropy of $T$
with respect to $\mu$, and $\lambda_1(x)$ and $\lambda_2(x)$ for the upper and lower Lyapunov
exponents of $T$ at $x$. Then

$$h_\mu(T) \le \max(0, \int \lambda_1 \, d\mu) + \max(0, \int \lambda_2 \, d\mu).$$

Source: D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Brasil. Mat. 9 (1978); G. A. Margulis (1968, unpublished). Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `margulis_ruelle`. -/
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
