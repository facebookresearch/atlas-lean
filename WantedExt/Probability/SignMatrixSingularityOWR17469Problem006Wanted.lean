/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Singularity probability of random sign matrices (Oberwolfach Report 6/2020)

A. Litvak (with K. Tikhomirov), Singularity of sparse Bernoulli matrices, Oberwolfach Report 6/2020,
p. 390: the old folklore conjecture `P{B_n is singular} = (1/2 + o_n(1))^n` for an `n × n` random
matrix `B_n` with i.i.d. `±1` entries.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace MathlibExt.Probability.SignMatrixSingularityOWR17469Problem006Wanted

/-!
Source: A. Litvak (with K. Tikhomirov), Singularity of sparse Bernoulli matrices, in New
Perspectives and Computational Challenges in High Dimensions, Oberwolfach Reports 17 (2020), no. 6,
p. 390, (1), DOI 10.4171/OWR/2020/6. UnsolvedMath record UM-30004384 (`OWR-17469-006`), dataset
ulamai/UnsolvedMath v1.8.0.

The probability is the proportion of the `2^{n²}` sign patterns whose `±1` matrix is singular
(determinant `0` over `ℤ`, equivalently over `ℝ`). `P = (1/2 + o(1))^n` is stated as `P^{1/n} →
1/2`, which is equivalent (put `o(1) = P^{1/n} - 1/2`). The report records on p. 391 that
Tikhomirov's theorem gives the affirmative answer.
-/

open Filter Topology

/-- The `n × n` integer matrix with entries `±1` given by a sign pattern `s` (`true ↦ 1`,
`false ↦ -1`). -/
def signMatrix {n : ℕ} (s : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => if s i j then 1 else -1

/-- The probability that the random sign matrix `B_n`, with independent entries uniform on
`{-1, 1}`, is singular: the proportion of the `2^(n²)` sign patterns whose matrix has determinant
`0`. -/
noncomputable def singularityProbability (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun s : Fin n → Fin n → Bool => (signMatrix s).det = 0).card : ℝ) /
    2 ^ (n ^ 2)

/-- The folklore conjecture recalled by Litvak (Oberwolfach Report 6/2020, p. 390, (1)):
`P(B_n is singular) = (1/2 + o(1))^n`, i.e. the `n`-th root of the singularity probability tends
to `1/2`. -/
def signMatrixSingularitySharp : Prop :=
  Tendsto (fun n : ℕ => singularityProbability n ^ (1 / (n : ℝ))) atTop (𝓝 (1 / 2))

/--
Resolved true: Tikhomirov proved that for an `n × n` random matrix with independent `±1` entries
`P{M_n is singular} = (1/2 + o_n(1))^n`, as the report itself states on p. 391 ("A recent
breakthrough result of K. Tikhomirov provides the affirmative answer to this conjecture"). Source:
A. Litvak (with K. Tikhomirov), Singularity of sparse Bernoulli matrices, in New Perspectives and
Computational Challenges in High Dimensions, Oberwolfach Reports 17 (2020), no. 6, p. 390, (1), DOI
10.4171/OWR/2020/6; resolution: K. Tikhomirov, Singularity of random Bernoulli matrices, Ann. of
Math. (2) 191 (2020), 593-634, arXiv:1812.09016, abstract: for an n × n random matrix M_n with
independent ±1 entries, P{M_n is singular} = (1/2 + o_n(1))^n; Oberwolfach Report 6/2020, p. 391,
https://arxiv.org/abs/1812.09016.
-/
public theorem_wanted signMatrixSingularitySharp_holds : signMatrixSingularitySharp

end MathlibExt.Probability.SignMatrixSingularityOWR17469Problem006Wanted
