# Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators

Let $E$ be $[0, 1]$ or a simplex, and let $A$ be a linear operator that maps the polynomials of degree at most $n$ into themselves for every $n$, such as the neutral Wright–Fisher generator, the Wright–Fisher generator with mutation, or the $K$-allele generator. Write $e^{tA}$ for the matrix exponential of $A$ on the finite-dimensional space of polynomials of degree at most $n$. If $X$ solves the [martingale problem](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $A$ on polynomials with respect to $(\mathcal F_t)$, with any initial law, then for every polynomial $p$ and all $s \le t$,

$$\mathbb E[p(X_t) \mid \mathcal F_s] = \bigl(e^{(t-s)A} p\bigr)(X_s) \quad \text{almost surely}.$$

Integrability is automatic since $E$ is compact. Proof sketch: for $F \in \mathcal F_s$, the vector $m(t) = \bigl(\mathbb E[\mathbf 1_F\, q(X_t)]\bigr)_q$, with $q$ running over a monomial basis of degree at most $n$, satisfies the closed linear equation $m' = A^{\top} m$ for $t \ge s$, from the martingale identity at fixed times, with $m(s) = \bigl(\mathbb E[\mathbf 1_F\, q(X_s)]\bigr)_q$; its unique solution gives $\mathbb E[\mathbf 1_F\, p(X_t)] = \mathbb E[\mathbf 1_F\, (e^{(t-s)A} p)(X_s)]$.

## Depends on

- [Martingale problems (generic definition)](../../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Conditional expectation given a σ-field](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

- [Global existence and uniqueness for globally Lipschitz ODEs](../../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)
- [Duhamel's formula (variation of constants)](../../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md)
- [Uniqueness of the conditional expectation](../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/ae-eq-cond-exp-of-forall-set-integral-eq.md)

## Expansion

A full proof page must still establish the linear equation for $m$ from the martingale property, its unique solvability, and the case of a random initial state.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4, Section 4 (duality) and the moment method, <https://doi.org/10.1002/9780470316658>
- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", *Theoretical Population Biology* 26(2):119–164, 1984, <http://www.columbia.edu/cu/simontavare/STpapers-pdf/T84a.pdf> (background)
