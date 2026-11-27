# Padé approximants recover the exact two-locus sampling distribution

Let $q(\mathbf a,\mathbf b,\mathbf c)$ be the two-locus sampling distribution of a configuration under a neutral finite-alleles model with recombination rate $\rho$, with asymptotic expansion $q = \sum_{k\ge 0} q_k\,\rho^{-k}$ as $\rho \to \infty$ (see [the recursive expansion](recursive-asymptotic-expansion-of-the-two-locus-sampling-distribution.md)).

For a function $f$ of $x = 1/\rho$ and integers $U, V \ge 0$, the **$[U/V]$ Padé approximant** is the rational function

$$
f_{[U/V]}(x) = \frac{A_0 + A_1x + \cdots + A_Ux^U}{1 + B_1x + \cdots + B_Vx^V}, \qquad f(x) - f_{[U/V]}(x) = O(x^{U+V+1}),
$$

determined by the first $U + V + 1$ Taylor coefficients of $f$, here $q_0,\dots,q_{U+V}$.

**Theorem.**

1. Under a neutral finite-alleles model, $q(\mathbf a,\mathbf b,\mathbf c)$ is a rational function of $1/\rho$ whose numerator and denominator have equal degree.
2. Consequently, for every configuration $(\mathbf a,\mathbf b,\mathbf c)$ there is a finite $U_0$ such that for all $U, V \ge U_0$ the Padé approximant $q_{[U/V]}(\mathbf a,\mathbf b,\mathbf c)$ equals $q(\mathbf a,\mathbf b,\mathbf c)$ exactly, for every $\rho \in [0,\infty)$.

So finitely many terms of a divergent-looking large-$\rho$ expansion determine the exact two-locus sampling distribution as an analytic function of $\rho$, including the regime $\rho \to 0$. By contrast, truncating the series at its smallest term (optimal truncation) only gives an approximation accurate for large $\rho$.

## Depends on

- [Recursive asymptotic expansion of the two-locus sampling distribution](recursive-asymptotic-expansion-of-the-two-locus-sampling-distribution.md)

## Expansion

The sampling probabilities solve a finite linear system obtained from the coalescent-with-recombination recursion over all configurations reachable from $(\mathbf a,\mathbf b,\mathbf c)$; its coefficients are affine in $\rho$, so by Cramer's rule each probability is a ratio of polynomials in $\rho$, and dividing numerator and denominator by the top power of $\rho$ makes it a rational function of $1/\rho$ of equal degrees. A rational function of type $[U_0/U_0]$ is reproduced exactly by its own $[U/V]$ Padé approximant whenever $U, V \ge U_0$, by uniqueness of Padé approximants.

## Sources

- Paul A. Jenkins, Yun S. Song, "Padé approximants and exact two-locus sampling distributions", *The Annals of Applied Probability* 22 (2012), 576–607, <https://doi.org/10.1214/11-AAP780>; preprint arXiv:1107.3897, <https://doi.org/10.48550/arXiv.1107.3897>. Numbering of the arXiv version: Section 4 (Definitions 4.1–4.2, Lemma 4.1, Theorem 4.1).
