# L^p spaces

Let $\mu$ be a measure on a set $X$ with a σ-algebra, let $E$ be a normed additive commutative group, such as
$\mathbb{R}$, $\mathbb{C}$ or a normed space, and let $p \in [0, \infty]$. The space $L^p(\mu; E)$ consists of the
classes, under equality $\mu$-almost everywhere, of almost everywhere strongly measurable functions $f \colon X \to E$
with $\|f\|_p < \infty$, where $\|f\|_p = \big(\int_X \|f\|^p \, d\mu\big)^{1/p}$ for $0 < p < \infty$, $\|f\|_\infty$
is the essential supremum of $\|f\|$, and $\|f\|_0 = 0$. This is the general form of the space $L^p(\mu)$ of a measure
space: for $E = \mathbb{C}$ and $1 \le p < \infty$, its elements are the classes of measurable functions
$f \colon X \to \mathbb{C}$ with $\int_X |f|^p \, d\mu < \infty$.

## Idea

Identifying functions that agree almost everywhere makes $\|\cdot\|_p$ definite for $p > 0$: $\|f\|_p = 0$ exactly when
$f = 0$ almost everywhere. For $1 \le p \le \infty$, Minkowski's inequality makes $L^p(\mu; E)$ a normed group, a normed
space when $E$ is one, and it is complete when $E$ is, by the Riesz–Fischer theorem; for $0 < p < 1$ and $E \ne \{0\}$
the triangle inequality fails as soon as $X$ has two disjoint sets of finite positive measure. $L^2(\mu; \mathbb{C})$ is
a Hilbert space, with $\langle f, g \rangle = \int f \bar g \, d\mu$. Counting measure on $\mathbb{N}$ gives the
sequence spaces $\ell^p$. On a finite measure space $L^q \subseteq L^p$ for $p \le q$, while on $\mathbb{R}$ neither of
$L^1$ and $L^2$ contains the other.

## Statements

- [The space $L^p$ of a measure](lp.md)

## Background

- [Measurable functions](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/README.md): measurability

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 7.16 (version read: the open-access PDF dated 12 June 2026).
