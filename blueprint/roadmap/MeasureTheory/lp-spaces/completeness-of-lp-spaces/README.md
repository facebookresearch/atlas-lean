# Riesz–Fischer theorem: completeness of L^p

Let $(X, \mathcal{M}, \mu)$ be a measure space, let $1 \le p \le \infty$, and let $E$ be a complete normed additive
commutative group, such as $\mathbb{R}$, $\mathbb{C}$ or a Banach space. Then $L^p(\mu; E)$, the space of almost
everywhere strongly measurable functions $f \colon X \to E$ with $\|f\|_p < \infty$, functions equal almost everywhere
being identified, is complete for the distance $\|f - g\|_p$: if $\|f_n - f_m\|_p \to 0$ as $m, n \to \infty$, there is
$f \in L^p(\mu; E)$ with $\|f_n - f\|_p \to 0$. This is the general form of the Riesz–Fischer theorem: for
$E = \mathbb{C}$ and $1 \le p < \infty$, where each class contains a measurable function, it says that $L^p(\mu)$ is
complete.

## Idea

Given a Cauchy sequence, pass to a subsequence with $\|f_{n_{k+1}} - f_{n_k}\|_p < 2^{-k}$. For $p < \infty$,
Minkowski's inequality and the monotone convergence theorem show that $g = \sum_k \|f_{n_{k+1}} - f_{n_k}\|$ has
$\|g\|_p \le 1$, so the series converges almost everywhere and $f_{n_k}$ converges almost everywhere to a function $f$.
Fatou's lemma then gives $f \in L^p$ and $\|f_{n_k} - f\|_p \to 0$, and a Cauchy sequence with a convergent subsequence
converges. For $p = \infty$ the convergence is uniform off a null set. The proof also shows that a sequence converging
in $L^p$ has a subsequence converging almost everywhere. So for $p \ge 1$ and $E$ a Banach space, $L^p(\mu; E)$ is a
Banach space, and $L^2(\mu)$, with real or complex values, is a Hilbert space.

## Statements

- [$L^p$ is complete for $1 \le p \le \infty$](inst-complete-space.md)

## Background

- [L^p spaces](../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the space and its norm

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 7.20 and 7.24 (version read: the open-access PDF dated 12 June 2026).
