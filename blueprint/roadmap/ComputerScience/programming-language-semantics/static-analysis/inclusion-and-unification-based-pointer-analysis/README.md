# Inclusion- and unification-based pointer analysis

Flow-insensitive points-to analysis with the allocation-site abstraction. Andersen's analysis generates inclusion constraints, solved in cubic time by the [cubic algorithm](../closure-analysis-0-cfa-and-the-cubic-algorithm.md); Steensgaard's analysis treats assignments as bidirectional and solves equality constraints by unification in almost linear time, at a loss of precision. Neither is the most precise flow-insensitive analysis. Soundness of Andersen's analysis with respect to an operational semantics is [stated separately](../soundness-of-andersen-s-pointer-analysis.md).

- [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md)
- [Andersen's analysis in cubic time](andersen-s-analysis-in-cubic-time.md)
- [Andersen's analysis is not the most precise flow-insensitive analysis](andersen-s-analysis-is-not-the-most-precise-flow.md)
- [Steensgaard's unification constraints](steensgaard-s-unification-constraints.md)
- [Steensgaard's analysis in almost linear time](steensgaard-s-analysis-in-almost-linear-time.md)
- [Andersen's analysis is at least as precise as Steensgaard's](andersen-s-analysis-is-at-least-as-precise-as-ste.md)
