/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F-matrix encoding and metrics on ranked tree shapes

Kim, Rosenberg and Palacios (2020) encode a ranked tree shape with `n` leaves and `m` sampling
events by its F matrix, of size `(n + m - 2) × (n + m - 2)`, and compare ranked tree shapes by
the entrywise `L¹` and `L²` distances `d₁, d₂` of their F matrices; for ranked genealogies, with
branch lengths, the weighted distances `d₁ʷ, d₂ʷ` replace each entry `F_{i,j}` by `F_{i,j} W_{i,j}`,
where `W_{i,j}` is the length of the time span from interval `j` down to interval `i`. Theorem 1
of the source states that the F matrix determines the ranked tree shape, and Proposition 2 that
the four distances are metrics; Eq. 5 defines the `L²`-medoid set of a sample.

The models and every part of the statement below except one are proved in
`Domains.Biology.PopulationGenetics.Coalescent.FMatrix`: the unique encoding
(`RankedTreeShape.fMatrix_injective`, and `RankedHistory.fMatrix_eq_fMatrix_iff` for ranked
labeled histories), the diagonal of isochronous F matrices
(`RankedTreeShape.fMatrix_diag_of_isochronous`), the metric space structures of `d₁` and `d₂`
(`RankedTreeShape.metricSpaceD₁`, `RankedTreeShape.metricSpaceD₂`), the pseudometric space
structures of `d₁ʷ` and `d₂ʷ` (`RankedGenealogy.pseudoMetricSpaceDw₁`,
`RankedGenealogy.pseudoMetricSpaceDw₂`), their metric space structures on isochronous genealogies
(`RankedGenealogy.metricSpaceDw₁OfIsochronous`, `RankedGenealogy.metricSpaceDw₂OfIsochronous`)
and the existence of medoids (`l2MedoidSet_nonempty`). What remains is that `d₁ʷ` and `d₂ʷ`
separate heterochronous ranked genealogies: two ranked genealogies with the same weighted F matrix
are equal. When the diagonals
of the F matrices agree this is `RankedGenealogy.eq_of_weighted_eq`; the source's argument (SI
Appendix, section 2) recovers the times from the first column of the weighted matrix, which
determines them only when a child of the root persists to the most recent interval.

Source: J. Kim, N. A. Rosenberg and J. A. Palacios, "Distance metrics for ranked evolutionary
trees", Proceedings of the National Academy of Sciences USA 117(46) (2020) 28876–28886,
Theorem 1, Eqs. 1–5 and Proposition 2, https://doi.org/10.1073/pnas.1922851117.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.PopulationGenetics.Coalescent.FMatrix

@[expose] public section

namespace WantedExt.Biology.PopulationGenetics.Coalescent.FMatrixWanted

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- **F-matrix encoding and metrics on ranked tree shapes** (Kim, Rosenberg and Palacios 2020,
Theorem 1, Eqs. 1–5 and Proposition 2).

* The F matrix determines the ranked tree shape with `n` leaves and `m` sampling events
  (heterochronous for `m ≥ 2`, isochronous for `m = 1`).
* For ranked labeled histories of `n` genes, the F matrices agree exactly when a relabelling of
  the genes carries the ancestral partitions of one history to those of the other, that is,
  exactly when the histories have the same ranked tree shape.
* For isochronous ranked tree shapes with `n` leaves, the interval `i` (counted from the root,
  from `0`) has `i + 2` lineages: `F_{i,i} = i + 1` in the source's indexing from `1`.
* The `L¹` and `L²` distances `d₁, d₂` between the F matrices are metrics on ranked tree shapes
  with `n` leaves and `m` sampling events, and so are the weighted distances `d₁ʷ, d₂ʷ` on ranked
  genealogies with `n` leaves and `m` sampling events: each is the distance of a metric space
  structure.
* For any distance, a nonempty finite sample has a nonempty `L²`-medoid set, the set of sampled
  points minimising the sum of squared distances to the sample. -/
theorem_wanted fMatrix_encoding_and_metrics :
    (∀ n m : ℕ, Function.Injective (RankedTreeShape.fMatrix (n := n) (m := m))) ∧
    (∀ (n : ℕ) (h₁ h₂ : RankedHistory n), h₁.fMatrix = h₂.fMatrix ↔
      ∃ σ : Equiv.Perm (Fin n), (partitionsOf h₁).map (relabelLineages σ) = partitionsOf h₂) ∧
    (∀ (n : ℕ) (T : RankedTreeShape n 1) (i : Fin (n + 1 - 2)), T.fMatrix i i = (i : ℕ) + 2) ∧
    (∀ n m : ℕ, ∃ M : MetricSpace (RankedTreeShape n m),
      ∀ T₁ T₂, M.dist T₁ T₂ = RankedTreeShape.d₁ T₁ T₂) ∧
    (∀ n m : ℕ, ∃ M : MetricSpace (RankedTreeShape n m),
      ∀ T₁ T₂, M.dist T₁ T₂ = RankedTreeShape.d₂ T₁ T₂) ∧
    (∀ n m : ℕ, ∃ M : MetricSpace (RankedGenealogy n m),
      ∀ g₁ g₂, M.dist g₁ g₂ = RankedGenealogy.dw₁ g₁ g₂) ∧
    (∀ n m : ℕ, ∃ M : MetricSpace (RankedGenealogy n m),
      ∀ g₁ g₂, M.dist g₁ g₂ = RankedGenealogy.dw₂ g₁ g₂) ∧
    (∀ {X : Type} (d : X → X → ℝ) {s : ℕ} (T : Fin s → X), 0 < s →
      (l2MedoidSet d T).Nonempty)

end WantedExt.Biology.PopulationGenetics.Coalescent.FMatrixWanted
