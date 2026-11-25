# Lebesgue measure on the real line

The Lebesgue outer measure of $A \subseteq \mathbb{R}$ is $m^*(A) = \inf \sum_k \ell(I_k)$ over the sequences of open
intervals $I_k$ that cover $A$. A set $A$ is Lebesgue measurable if it contains a Borel set $B$ with
$m^*(A \setminus B) = 0$, and Lebesgue measure assigns to each such set the number $m(A) = m^*(A)$.

## Idea

Outer measure is defined for every subset of $\mathbb{R}$ and gives each interval its length, but it is not additive on
all sets, as the Vitali set shows. The Lebesgue measurable sets form a σ-algebra containing the Borel sets, on which
$m$ is countably additive, so $m$ is a measure; it is the completion of its restriction to the Borel sets. A Lebesgue
measurable set differs from a Borel set by a set of outer measure $0$; other approaches define the same sets through
Carathéodory's criterion or approximation from outside by open sets.

## Statements

- [Lebesgue measure on the real line](lebesgue-measure.md)

## Background

- [σ-algebras](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/README.md): Borel sets
- [Measures](../../../measures/measures-and-countable-additivity/measures/README.md): measures

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definitions 2.1, 2.2, 2.70 and 2.73 (version read: the open-access PDF dated 12 June 2026).
