/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Dirichlet process: marginals, conjugacy, the Pólya urn and the Chinese restaurant

`MathlibExt.Probability.DirichletProcess` defines the Dirichlet process `DP(α, H)`
(`dirichletProcess α hα H`, a law on `Measure X`) through Sethuraman's (1994) stick-breaking
construction and proves its mean, its variance, the almost-sure normalization of the weights,
and the Blackwell–MacQueen predictive rule for two observations. This file records the
classical results it does not prove.

* **Finite-dimensional marginals** (Ferguson 1973, §3; Sethuraman 1994, Theorem 3.4): for a
  measurable partition `A₀, …, A_m` of `X` with `H(Aᵢ) > 0`, the vector `(G(A₀), …, G(A_m))`
  has the Dirichlet law with parameters `(α H(A₀), …, α H(A_m))`
  (`map_dirichletProcess_partition`). Ferguson defines the Dirichlet process by this property.
* **Moments are the Pólya urn** (Blackwell–MacQueen 1973): `E[∏ᵢ G(Aᵢ)]` is the probability
  that the first `n` draws `X₀, …, X_{n-1}` of the Blackwell–MacQueen urn land in
  `A₀, …, A_{n-1}` (`lintegral_dirichletProcess_prod`). The urn (`blackwellMacQueen`) draws
  `X_n` from `(α H + ∑_{i<n} δ_{Xᵢ}) / (α + n)` (`polyaUrnPredictive`). Equivalently, given
  `G ∼ DP(α, H)` and `X₀, X₁, … | G` i.i.d. `G`, the predictive law is
  `P(X_n ∈ A | X₀, …, X_{n-1}) = (α H(A) + #{i < n | Xᵢ ∈ A}) / (α + n)`.
* **Conjugacy** (Ferguson 1973, Theorem 1): given observations `x₀, …, x_{n-1}`, the posterior
  of `G` is `DP(α + n, (α H + ∑ᵢ δ_{xᵢ}) / (α + n))`. We state it as the disintegration of the
  joint law of `(G, X₀, …, X_{n-1})` over the marginal law of the observations
  (`setLIntegral_dirichletProcess_prod`).
* **Exchangeability** of the urn (`map_perm_blackwellMacQueen`) and the **Chinese restaurant
  law of the ties**: for an atomless base measure, the partition of `{0, …, n-1}` into groups of
  equal observations follows the Chinese restaurant process with parameter `α`
  (`blackwellMacQueen_tiePartition`, Pitman 2006, §3.1; the law `crpProb` is proved in
  `MathlibExt.Biology.PopulationGenetics.ChineseRestaurant`). The proved file covers `n = 2`:
  two draws pick the same stick piece with probability `1 / (1 + α)`.

Sources: T. S. Ferguson, "A Bayesian analysis of some nonparametric problems", Ann. Statist. 1
(1973) 209–230; D. Blackwell and J. B. MacQueen, "Ferguson distributions via Pólya urn
schemes", Ann. Statist. 1 (1973) 353–355; J. Sethuraman, "A constructive definition of
Dirichlet priors", Statist. Sinica 4 (1994) 639–650; J. Pitman, *Combinatorial Stochastic
Processes*, Lecture Notes in Math. 1875 (2006), ch. 3.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.ChineseRestaurant
public import MathlibExt.Probability.DirichletProcess
public import MathlibExt.Probability.Distributions.Dirichlet

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X]

/-- The **Blackwell–MacQueen urn** with parameter `α` and base measure `H`: the joint law of the
first `n` draws, where draw `n` has law `polyaUrnPredictive α H xs` given the previous draws
`xs` (Blackwell–MacQueen 1973). -/
noncomputable def blackwellMacQueen (α : ℝ) (H : Measure X) : (n : ℕ) → Measure (Fin n → X)
  | 0 => Measure.dirac fun i ↦ i.elim0
  | n + 1 => (blackwellMacQueen α H n).bind fun xs ↦
      (polyaUrnPredictive α H xs).map fun x ↦ Fin.snoc (α := fun _ ↦ X) xs x

/-- The partition of the indices `{0, …, n-1}` into groups of equal entries of `xs`. -/
noncomputable def tiePartition {n : ℕ} (xs : Fin n → X) : Finpartition (univ : Finset (Fin n)) :=
  haveI := Classical.decRel (Setoid.ker xs).r
  Finpartition.ofSetoid (Setoid.ker xs)

/-- **Finite-dimensional marginals of the Dirichlet process** (Ferguson 1973, §3; Sethuraman
1994, Theorem 3.4): on a measurable partition `A₀, …, A_m` of `X` with `H(Aᵢ) > 0`, the vector
`(G(A₀), …, G(A_m))` has the Dirichlet law `Dir(α H(A₀), …, α H(A_m))`. -/
theorem_wanted map_dirichletProcess_partition (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {m : ℕ} (A : Fin (m + 1) → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = Set.univ)
    (hpos : ∀ i, 0 < H (A i)) :
    (dirichletProcess α hα H).map (fun ν i ↦ (ν (A i)).toReal) =
      dirichletMeasure fun i ↦ α * H.real (A i)

/-- **The moments of the Dirichlet process are the Blackwell–MacQueen urn** (Blackwell–MacQueen
1973): `E[∏ᵢ G(Aᵢ)] = P(X₀ ∈ A₀, …, X_{n-1} ∈ A_{n-1})` for the urn's first `n` draws. -/
theorem_wanted lintegral_dirichletProcess_prod (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {n : ℕ} (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    ∫⁻ ν, ∏ i, ν (A i) ∂dirichletProcess α hα H = blackwellMacQueen α H n (Set.univ.pi A)

/-- **Ferguson's conjugacy** (Ferguson 1973, Theorem 1): given `n` observations `xs` from
`G ∼ DP(α, H)`, the posterior of `G` is `DP(α + n, (α H + ∑ᵢ δ_{xsᵢ}) / (α + n))`. Stated as
the disintegration `P(G ∈ S, X₀ ∈ A₀, …) = ∫_{∏ Aᵢ} DP(α + n, posterior base)(S) dP(xs)` over
the urn law of the observations. -/
theorem_wanted setLIntegral_dirichletProcess_prod (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {n : ℕ} (A : Fin n → Set X) (hA : ∀ i, MeasurableSet (A i))
    {S : Set (Measure X)} (hS : MeasurableSet S) :
    ∫⁻ ν in S, ∏ i, ν (A i) ∂dirichletProcess α hα H =
      ∫⁻ xs in Set.univ.pi A,
        (haveI := isProbabilityMeasure_polyaUrnPredictive hα (H := H) xs;
          dirichletProcess (α + n) (add_pos_of_pos_of_nonneg hα n.cast_nonneg)
            (polyaUrnPredictive α H xs)) S ∂blackwellMacQueen α H n

/-- **Exchangeability of the Blackwell–MacQueen urn** (Blackwell–MacQueen 1973): relabeling the
draws by a permutation does not change their joint law. -/
theorem_wanted map_perm_blackwellMacQueen (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (blackwellMacQueen α H n).map (fun xs ↦ xs ∘ σ) = blackwellMacQueen α H n

/-- **The ties of the Blackwell–MacQueen urn follow the Chinese restaurant process** (Pitman
2006, §3.1): for an atomless base measure, the partition of the first `n` draws into groups of
equal values has the law `θ^{|π|} ∏_{B ∈ π} (|B| - 1)! / θ^{(n)}` with `θ = α`. -/
theorem_wanted blackwellMacQueen_tiePartition [MeasurableSingletonClass X]
    [MeasurableSpace.CountablySeparated X] (α : ℝ) (hα : 0 < α) (H : Measure X)
    [IsProbabilityMeasure H] (hH : ∀ x, H {x} = 0) {n : ℕ}
    (π : Finpartition (univ : Finset (Fin n))) :
    blackwellMacQueen α H n {xs | tiePartition xs = π} =
      ENNReal.ofReal (MathlibExt.Biology.PopulationGenetics.ChineseRestaurant.crpProb α π)

end ProbabilityTheory
