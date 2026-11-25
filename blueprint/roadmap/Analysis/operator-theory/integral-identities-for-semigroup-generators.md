# Integral identities for a strongly continuous semigroup and its generator

Let $(T(t))_{t\ge0}$ be a [strongly continuous contraction semigroup](strongly-continuous-contraction-semigroups.md) on a real Banach space $L$ with generator $A$. Integrals below are Riemann integrals of continuous $L$-valued functions. Then:

1. for every $f\in L$ and $t\ge0$, $\int_0^tT(s)f\,ds\in\mathcal D(A)$ and $A\int_0^tT(s)f\,ds=T(t)f-f$;
2. for every $f\in\mathcal D(A)$ and $t\ge0$, $T(t)f\in\mathcal D(A)$, $\frac{d}{dt}T(t)f=AT(t)f=T(t)Af$, and

$$T(t)f-f=\int_0^tT(s)Af\,ds .$$

## Depends on

- [Strongly continuous contraction semigroups, generators and cores](strongly-continuous-contraction-semigroups.md)

## Expansion

A proof page must establish item 1 by computing $h^{-1}(T(h)-I)\int_0^tT(s)f\,ds=h^{-1}\int_t^{t+h}T(s)f\,ds-h^{-1}\int_0^hT(s)f\,ds$ and letting $h\to0^+$ by continuity; the right derivative in item 2 from the semigroup property, the left derivative from the uniform bound $\lVert T(t-h)\rVert\le1$ and strong continuity; and the integral formula from the fundamental theorem of calculus for continuously differentiable $L$-valued functions.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 1.
- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*, Springer, 1983, Chapter 1.
