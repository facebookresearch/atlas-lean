# Radon measures

Let $X$ be a topological space with a σ-algebra. A measure $\mu$ on $X$ is regular if it is finite on compact sets,
outer regular, meaning $\mu(A) = \inf\{\mu(U) : U \supseteq A \text{ open}\}$ for every measurable set $A$, and inner
regular on open sets, meaning $\mu(U) = \sup\{\mu(K) : K \subseteq U \text{ compact}\}$ for every open set $U$. This is
the general form of a Radon measure: on a locally compact Hausdorff space with its Borel σ-algebra, the regular measures
are exactly the Radon measures, the Borel measures that are finite on compact sets, outer regular on Borel sets and
inner regular on open sets.

## Idea

Radon measures are the measures that integration of continuous functions sees: by the Riesz–Markov–Kakutani theorem, the
positive linear functionals on the continuous compactly supported functions on a locally compact Hausdorff space are
exactly the integrals against Radon measures. Lebesgue measure on $\mathbb{R}^n$ and Haar measures on locally compact
groups are Radon measures, and on a locally compact Hausdorff space in which every open set is σ-compact, such as
$\mathbb{R}^n$, every Borel measure that is finite on compact sets is regular.

## Statements

- [Regular measure](regular.md)

## Background

- [Outer regularity of Lebesgue measure](../outer-regularity-of-lebesgue-measure/README.md): outer regularity
- [σ-algebras](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/README.md): the Borel σ-algebra
