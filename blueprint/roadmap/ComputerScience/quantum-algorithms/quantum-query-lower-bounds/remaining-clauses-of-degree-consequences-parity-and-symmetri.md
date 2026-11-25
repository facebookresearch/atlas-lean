# Query lower bounds from polynomial degree: parity and symmetric functions

Symmetrization of polynomials on the Boolean cube (a symmetrized polynomial equals a univariate polynomial of no larger
degree in the Hamming weight) and the degree lower bound $N$ for approximating parity within $1/3$ are separate
results and are not part of this node. This node collects their query consequences.

## Expansion

A sound expansion has separate pages for:

1. **Parity lower bound.** Every quantum query algorithm that computes the parity of $N$ bits with error at most $1/3$
   uses at least $N/2$ queries: its acceptance probability is a real multilinear polynomial of degree at most $2T$ that
   approximates parity within $1/3$, and every such polynomial has degree at least $N$.
2. **Symmetric functions.** For a $T$-query algorithm, symmetrizing its acceptance polynomial gives a univariate real
   polynomial $r$ of degree at most $2T$ such that $r(|x|)$ is the average of the acceptance probabilities on the
   permutations of $x$; if the algorithm computes a symmetric $f(x) = F(|x|)$ with error at most $\varepsilon$, then
   $|r(k) - F(k)| \le \varepsilon$ for $k = 0, \dots, N$.

## Proof depends on

- [Polynomial method for quantum query complexity](polynomial-method-for-quantum-query-complexity.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §11.2 (the acceptance probability has degree at most $2T$; symmetrization $q(x) = \frac{1}{N!}\sum_\pi p(\pi(x)) = r(|x|)$) and Exercise 11.4(b) (Parity needs $N/2$ queries even with error at most $1/3$). <https://arxiv.org/pdf/1907.09415v6>
