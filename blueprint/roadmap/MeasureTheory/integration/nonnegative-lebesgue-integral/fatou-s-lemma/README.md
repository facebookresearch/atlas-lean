# Fatou's lemma

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $f_1, f_2, \ldots \colon X \to [0, \infty]$ be
measurable. Then the pointwise lower limit $\liminf_k f_k$ is measurable and
$\int \liminf_{k \to \infty} f_k \, d\mu \le \liminf_{k \to \infty} \int f_k \, d\mu$.

## Idea

The infima $g_k = \inf_{j \ge k} f_j$ increase to $\liminf_k f_k$ and satisfy $\int g_k \le \int f_j$ for
$j \ge k$, so the monotone convergence theorem gives the inequality. It can be strict even for bounded functions on a
finite measure space: on $[0, 1]$ with Lebesgue measure, the indicators of $[0, 1/2]$ and $(1/2, 1]$, alternating,
have lower limit $0$ while each has integral $1/2$. Fatou's lemma is the usual way to pass from almost everywhere
convergence to bounds on integrals, as in the proofs of the completeness of $L^p$ and of the dominated convergence
theorem.

## Statements

- [Fatou's lemma](fatou-lemma.md)

## Background

- [Lebesgue integral](../lebesgue-integral/README.md): the integral
- [Monotone convergence theorem](../../monotone-convergence-theorem/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Exercise 17 in Section 3A (version read: the open-access PDF dated 12 June 2026).
