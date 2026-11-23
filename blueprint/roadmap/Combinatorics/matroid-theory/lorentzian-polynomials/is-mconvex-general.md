# M-convex set

A set $J$ of finitely supported vectors $\alpha \in \mathbb{N}^\iota$ (vectors with finitely many
nonzero coordinates) is *M-convex* if for all $\alpha, \beta \in J$ and every index $i$ with
$\alpha_i > \beta_i$ there is an index $j$ with $\alpha_j < \beta_j$ and
$\alpha - e_i + e_j \in J$, where $e_i$ is the $i$-th unit vector.

This is the exchange axiom of Murota's discrete convex analysis. Two distinct vectors of an
M-convex set are never comparable coordinatewise, and an M-convex set lies in a single hyperplane
$\{\alpha : \sum_i \alpha_i = d\}$. For $\iota = \{1, \dots, n\}$, Brändén and Huh use M-convexity
to describe the supports of Lorentzian polynomials in $n$ variables: by their Theorem 2.25 the
support of every Lorentzian polynomial is M-convex, and by Theorem 3.10 every nonempty M-convex
subset of a discrete simplex $\{\alpha \in \mathbb{N}^n : \alpha_1 + \cdots + \alpha_n = d\}$ is
the support of one. On a finite index set, the nonempty M-convex sets of zero-one vectors are exactly the sets of indicator vectors of the bases of matroids.

The [M-convex sets](is-mconvex.md) of $\mathbb{N}^n$ used in Theorem 2.25 are the case
$\iota = \{1, \dots, n\}$.

## Background

- [Matroids are the zero-one M-convex sets](is-mconvex-iff-exists-matroid.md): the nonempty M-convex sets of zero-one vectors are the base sets of matroids.

## Sources

- K. Murota, *Discrete Convex Analysis*, SIAM, 2003, Section 4.1.
- P. Brändén and J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), 821–891,
  Section 1 (definition of M-convexity), https://arxiv.org/abs/1902.03719.
