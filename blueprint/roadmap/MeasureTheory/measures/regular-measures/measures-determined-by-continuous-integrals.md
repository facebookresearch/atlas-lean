# Finite Borel measures on a metric space are determined by integrals of bounded continuous functions

Let $(S,d)$ be a metric space with its Borel $\sigma$-algebra, and let $\mu$ and $\nu$ be finite Borel measures on $S$. If

$$\int_Sf\,d\mu=\int_Sf\,d\nu\qquad\text{for every bounded continuous }f:S\to\mathbb R,$$

then $\mu=\nu$. When $S$ is compact, the bounded continuous functions are all of $C(S)$.

## Proof depends on

- [The distance to a set is 1-Lipschitz and vanishes exactly on its closure](../../../Topology/metric-spaces/distance-to-a-set.md)
- [Dynkin's π–λ theorem](../../measurable-spaces/pi-systems-and-the-theorem/dynkin-s-pi-lambda-theorem/induction-on-inter.md)

## Expansion

A proof page must approximate the indicator of a closed set $F$ from above by the bounded continuous functions $f_k(x)=\max\bigl(0,1-k\,d(x,F)\bigr)$, which decrease to $\mathbf 1_F$ because the [distance to a closed set](../../../Topology/metric-spaces/distance-to-a-set.md) is continuous and vanishes exactly on it; conclude $\mu(F)=\nu(F)$ by dominated convergence; note that $\mu(S)=\nu(S)$ from $f\equiv1$; and extend from the closed sets, a $\pi$-system generating the Borel $\sigma$-algebra, by the $\pi$–$\lambda$ theorem.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 1, Section 1.
