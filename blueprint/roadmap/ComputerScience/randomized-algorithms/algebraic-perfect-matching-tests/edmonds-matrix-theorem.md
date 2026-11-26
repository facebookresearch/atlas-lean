# Edmonds' theorem and the randomized bipartite matching test

$\det E_G \ne 0$ as a polynomial if and only if $G$ has a perfect matching. Consequently, if the variables are replaced by values drawn independently and uniformly from a finite subset $T$ of a field (or of $\mathbb{Z}$), then: if $G$ has no perfect matching the determinant is always $0$; if $G$ has one, the determinant is $0$ with probability at most $n/|T|$.

## Proof sketch

In the Leibniz expansion, each permutation $\sigma$ contributes the monomial $\prod_i x_{i\sigma(i)}$ exactly when $\sigma$ is a perfect matching, and distinct permutations give distinct monomials, so no cancellation occurs. The probability bound is the Schwartz-Zippel lemma for a nonzero polynomial of degree at most $n$.

## Depends on

- [The Edmonds matrix of a bipartite graph](edmonds-matrix.md)

## Sources

- J. Edmonds, "Systems of Distinct Representatives and Linear Algebra", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- J. T. Schwartz, "Fast Probabilistic Algorithms for Verification of Polynomial Identities", Journal of the ACM 27(4), 1980.
- R. Zippel, "Probabilistic Algorithms for Sparse Polynomials", Symbolic and Algebraic Computation (EUROSAM 1979), LNCS 72, Springer, 1979.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
