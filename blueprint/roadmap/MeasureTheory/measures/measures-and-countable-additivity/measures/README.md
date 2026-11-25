# Measures

Let $X$ be a set and $\mathcal{M}$ a σ-algebra on $X$. A measure on $(X, \mathcal{M})$ is a function
$\mu \colon \mathcal{M} \to [0, \infty]$ with $\mu(\emptyset) = 0$ that is countably additive:
$\mu\big(\bigcup_k E_k\big) = \sum_k \mu(E_k)$ for every sequence $E_1, E_2, \ldots$ of pairwise disjoint sets in
$\mathcal{M}$. The triple $(X, \mathcal{M}, \mu)$ is then a measure space.

## Idea

Countable additivity is what makes limits work: it gives continuity from below along increasing sequences of sets and,
when some set of the sequence has finite measure, continuity from above along decreasing ones, and from there the
convergence theorems for integrals. It implies finite additivity, monotonicity and countable subadditivity. Counting
measure, Dirac measures and Lebesgue measure on the Lebesgue measurable subsets of $\mathbb{R}$ are measures. A measure
extends to every subset $A$ of $X$ by $\mu(A) = \inf\{\mu(E) : E \in \mathcal{M},\ E \supseteq A\}$; the card's other
statements are stated for this extension, so monotonicity and subadditivity hold for all sets, and a property holds
almost everywhere when the set where it fails has measure zero in this sense. A measure is σ-finite when $X$ is a
countable union of sets of finite measure, as for Lebesgue measure; it is the standard sufficient hypothesis for
Fubini's theorem and the Radon–Nikodym theorem.

## Statements

- [Measure](measure.md)
- [Finite additivity of a measure](measure-bi-union-finset.md): finitely many disjoint measurable sets.
- [Monotonicity of a measure](measure-mono.md): for all sets, measurable or not.
- [Countable subadditivity of a measure](measure-i-union-le.md): for all sets, measurable or not.
- [Almost everywhere](ae.md): properties that fail only on a set of measure zero.
- [σ-finite measure](sigma-finite.md): $X$ is a countable union of sets of finite measure.

## Background

- [σ-algebras](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/README.md): the domain of a measure

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 2.54 (version read: the open-access PDF dated 12 June 2026).
