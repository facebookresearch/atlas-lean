# The invariant method for polynomial calculus degree lower bounds

Let $M$ be an $\mathcal{R}$-submodule of polynomials that contains every input of degree at most $d$ and contains $x_i p$ whenever $p \in M$ and $\deg(x_i p) \le d$. Then every line of a PC proof of degree at most $d$ lies in $M$. In particular, if $1 \notin M$ then the inputs have no PC refutation of degree at most $d$. Proofs and refutations are also monotone in the input list.

## Proof sketch

Induction along the proof: inputs lie in $M$, $M$ is closed under linear combinations, and multiplication by a variable stays within $M$ under the degree bound.

## Depends on

- [Polynomial calculus proofs, degree and size](polynomial-calculus-proofs.md)

## Sources

- M. Clegg, J. Edmonds and R. Impagliazzo, "Using the Groebner Basis Algorithm to Find Proofs of Unsatisfiability", Proceedings of the 28th ACM Symposium on Theory of Computing (STOC), 1996: Theorem 1 (the space $V_d$ of degree-$d$ consequences).
- R. Impagliazzo, P. Pudlák and J. Sgall, "Lower Bounds for the Polynomial Calculus and the Gröbner Basis Algorithm", Computational Complexity 8(2), 127–144, 1999.
- S. Buss, D. Grigoriev, R. Impagliazzo and T. Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", Journal of Computer and System Sciences 62(2), 267–289, 2001.
