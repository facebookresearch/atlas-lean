# Bounded convergence theorem

Let $\mu$ be a finite measure, $G$ a real Banach space and $C$ a real number. Let
$F_n : \alpha \to G$ be almost everywhere strongly measurable functions with $\|F_n\| \le C$
almost everywhere for every $n$, and suppose $F_n \to f$ in $\mu$-measure. Then
$\int_\alpha F_n \, d\mu \to \int_\alpha f \, d\mu$. The statement is recorded for every real
normed space $G$, with the convention that the Bochner integral is $0$ when $G$ is not complete, so
for an incomplete $G$ it asserts nothing more; its content is the Banach-space case. On a finite
measure space almost-everywhere convergence implies convergence in measure, so the classical
pointwise form is a special case.

## Idea

The bounded convergence theorem is dominated convergence with a constant dominating function,
which is integrable because the measure is finite. Finiteness cannot be dropped: on the real line
the functions $\frac1n \mathbf{1}_{[0, n]}$, $n \ge 1$, are bounded by $1$ and tend to $0$ uniformly,
hence in measure, but all their integrals equal $1$. The stronger form gives convergence in $L^1$,
$\int \|F_n - f\| \, d\mu \to 0$, a statement about real integrals that needs no completeness of
$G$; for a Banach space it implies the convergence of the integrals.

## Statements

- [Bounded convergence theorem](tendsto-integral-of-bounded-convergence.md)
- [Bounded convergence theorem, $L^1$ form](tendsto-integral-norm-sub-of-bounded-con.md): a stronger form, convergence in $L^1$.
