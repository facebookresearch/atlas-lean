# Inner regularity of finite measures on Polish spaces

Let $P$ be a finite measure on the Borel sets of a second countable, completely pseudometrizable space, such as
$\mathbb{R}^n$ or any Polish space. Then every Borel set $A$ is approximated from inside by compact sets:
$P(A) = \sup\{P(K) : K \subseteq A,\ K \text{ compact and closed}\}$.

## Idea

A finite Borel measure on a metric space is approximated from inside by closed sets, so the point is to find compact
sets of almost full measure. For each $n$, countably many balls of radius $1/n$ cover the space, and finitely many of
them carry all but $\varepsilon 2^{-n}$ of the mass; the intersection over $n$ of the closures of these finite unions is
closed and totally bounded, hence compact by completeness, and its complement has measure at most $\varepsilon$. In
probability this says that a single probability measure on a Polish space is tight, the condition of Prokhorov's
theorem.

## Statements

- [Finite measures on Polish spaces are inner regular](inner-regular-compact-closed-of-finite.md)

## Background

- [Radon measures](../radon-measures/README.md): inner approximation by compact sets
