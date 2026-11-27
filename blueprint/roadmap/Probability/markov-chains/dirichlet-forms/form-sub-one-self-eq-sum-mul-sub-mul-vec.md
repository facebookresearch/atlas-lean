# Sinclair's identity in Dirichlet-form terms

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$, and $P$ a real $S \times S$ matrix with unit
row sums in detailed balance with $\pi$: $\pi(x) P(x, y) = \pi(y) P(y, x)$ for all $x, y$. Then the
[form](form.md) of $(\pi, P - I)$ satisfies, for every $g : S \to \mathbb{R}$,

$$\mathcal E_{\pi, P - I}(g, g) = \sum_x \pi(x)\, g(x) \bigl(g(x) - (Pg)(x)\bigr) .$$

This restates [Sinclair's identity](../mixing-times-of-markov-chains/sum-mul-sub-mul-vec-eq.md),
behind his variational characterisation (5), through [the Dirichlet form of a Markov
kernel](form-sub-one.md).

## Background

- [The Dirichlet form of a reversible matrix](../mixing-times-of-markov-chains/sum-mul-sub-mul-vec-eq.md): the same identity.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370, equation (5).
