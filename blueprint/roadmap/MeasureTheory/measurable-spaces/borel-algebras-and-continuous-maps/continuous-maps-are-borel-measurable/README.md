# Continuous maps are Borel measurable

Let $X$ and $Y$ be topological spaces with their Borel σ-algebras. Then every continuous map $f \colon X \to Y$ is
measurable: preimages of Borel sets are Borel sets.

## Idea

The sets $E \subseteq Y$ whose preimage is a Borel set form a σ-algebra, since preimages commute with complements and
countable unions, and by continuity it contains the open sets, so it contains every Borel set. Composed with a
measurable function, a continuous map gives a measurable function: $|f|$, $\operatorname{Re} f$,
$\operatorname{Im} f$ and $\max(f, 0)$ are measurable when $f$ is, and translations of $\mathbb{R}$ map Borel sets to
Borel sets.

## Statements

- [Continuous maps are Borel measurable](borel-measurable.md)

## Background

- [σ-algebras](../../measurable-spaces-and-measurable-functions/sigma-algebras/README.md): Borel σ-algebras
- [Measurable functions](../../measurable-spaces-and-measurable-functions/measurable-functions/README.md): measurability

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 2.41, for continuous real functions on Borel subsets of $\mathbb{R}$ (version read: the open-access PDF dated 12 June 2026).
