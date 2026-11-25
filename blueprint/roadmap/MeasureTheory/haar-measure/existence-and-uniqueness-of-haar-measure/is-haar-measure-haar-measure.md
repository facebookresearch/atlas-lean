# Existence of Haar measure

Let $G$ be a topological group with its Borel σ-algebra, and let $K_0 \subseteq G$ be a compact set with nonempty
interior, so that $G$ is locally compact. The measure built from $K_0$ by Haar's covering construction and normalised
so that $K_0$ has measure $1$ is a [Haar measure](../is-haar-measure.md) on $G$: it is invariant under left
translations, finite on compact sets and positive on nonempty open sets. The group need not be
Hausdorff; the classical statement is the special case of a locally compact Hausdorff group.

## Sources

- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the theorem: `MeasureTheory.Measure.isHaarMeasure_haarMeasure`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L572.
- The same file, for its hypotheses, none of which is `T2Space G`: `[Group G]`, `[TopologicalSpace G]` and `[IsTopologicalGroup G]`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L80, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L100 and https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L139; `[MeasurableSpace G]` and `[BorelSpace G]`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L514; and `K₀ : PositiveCompacts G` in the statement. Its introduction, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L15, describes the classical Hausdorff setting.
