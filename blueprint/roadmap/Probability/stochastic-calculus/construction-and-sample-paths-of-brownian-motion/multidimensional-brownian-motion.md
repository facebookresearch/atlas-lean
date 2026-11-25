# Multidimensional Brownian motion

Let $d\ge1$ and let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space. A $d$-dimensional standard Brownian motion is an $\mathbb R^d$-valued process $B=(B^1,\ldots,B^d)$ such that the coordinates $B^1,\ldots,B^d$ are independent real [Brownian motions](exists-is-brownian-real.md) started at $0$. With respect to the filtration it is an $(\mathcal F_t)$-Brownian motion if moreover it is adapted and each increment $B_t-B_s$, $0\le s\le t$, is independent of $\mathcal F_s$.

For a positive semidefinite $d\times d$ matrix $C$, with positive semidefinite square root $C^{1/2}$, the process $B^C_t=C^{1/2}B_t$ is a Brownian motion with covariance matrix $C$. The following hold:

1. $B$ has continuous paths, $B_0=0$, and independent stationary increments with $B_t-B_s\sim\mathcal N(0,(t-s)I_d)$.
2. The finite-dimensional laws of $B^C$ are centred Gaussian with

    $$\operatorname{Cov}\bigl(B^C_s,B^C_t\bigr)=\min(s,t)\,C,\qquad s,t\ge0,$$

    and conversely a continuous centred Gaussian process $X$ with $X_0=0$ and $\operatorname{Cov}(X_s,X_t)=\min(s,t)C$ has the law of $B^C$.
3. For $C=I_d$ the process $B^C$ is the standard $d$-dimensional Brownian motion; any $A\in\mathbb R^{d\times d}$ with $AA^{\mathsf T}=C$ gives a process $AB$ with the same law as $C^{1/2}B$.

## Depends on

- [Existence of Brownian motion](exists-is-brownian-real.md)
- [Positive elements are the squares of positive elements](../../../Analysis/operator-algebras/powers-and-square-roots-of-positive-operators/nonneg-iff-exists-nonneg-and-eq-mul-self.md)
- [Positive square roots are unique](../../../Analysis/operator-algebras/powers-and-square-roots-of-positive-operators/mul-self-eq-mul-self-iff.md)

## Expansion

A full proof page must establish the following.

- Existence: take $d$ independent copies of a real Brownian motion on a product space, so that the coordinates are independent.
- Item 1 from coordinatewise independence and the one-dimensional increments.
- Item 2: linear images of Gaussian vectors are Gaussian, $\operatorname{Cov}(AB_s,AB_t)=\min(s,t)AA^{\mathsf T}$, and a centred Gaussian law is determined by its covariance; continuity of paths transfers through the linear map.
- Item 3, including the case of singular $C$, where $B^C$ lives in the range of $C$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, multidimensional Brownian motion (definition).
