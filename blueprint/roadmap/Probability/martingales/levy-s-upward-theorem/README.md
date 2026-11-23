# Lévy's upward theorem

If σ-fields $\mathcal F_n$ increase to $\mathcal F_\infty = \sigma\big(\bigcup_n \mathcal F_n\big)$ and $E|X| < \infty$, then
$E(X \mid \mathcal F_n) \to E(X \mid \mathcal F_\infty)$ almost surely and in $L^1$.

## Idea

As information accumulates, the best estimates of $X$ converge to the best estimate given all of it. In
particular, if $X$ is $\mathcal F_\infty$-measurable, then $E(X \mid \mathcal F_n) \to X$; for $X = 1_A$ with
$A \in \mathcal F_\infty$, the conditional probabilities of $A$ tend to $0$ or $1$, and a short argument from this
reproves Kolmogorov's zero–one law. The martingale $E(X \mid \mathcal F_n)$ is uniformly integrable, so it converges
almost surely and in $L^1$, and a π–λ argument identifies the limit. Lévy's downward theorem treats decreasing
sequences of σ-fields.

## Statements

- [Lévy's upward theorem](levy-upward-theorem.md)

## Background

- [Martingale convergence theorem](../martingale-convergence-theorems/README.md): convergence of uniformly integrable martingales
- [Tower property](../../foundations/conditional-expectation/tower-property/README.md): the tower property
- [Uniform integrability](../uniform-integrability/README.md): uniform integrability
