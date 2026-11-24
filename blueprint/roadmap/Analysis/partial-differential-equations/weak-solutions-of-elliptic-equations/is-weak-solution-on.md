# Weak solution of a divergence-form elliptic equation

Given coefficients $a^{ij}, b^i, c$ and a right-hand side $f$ on $U \subseteq \mathbb{R}^n$, a function
$u \in H^1(U)$ with weak gradient $Du$ is a weak solution of

$$Lu = -\sum_{i,j} (a^{ij} u_{x_i})_{x_j} + \sum_i b^i u_{x_i} + c u = f \quad \text{in } U$$

when $B[u, \varphi] = (f, \varphi)$ for every $\varphi \in C^\infty_c(U)$, where
$B[u, v] = \int_U \big(\sum a^{ij} u_{x_i} v_{x_j} + \sum b^i u_{x_i} v + c u v\big)$ and $(f, \varphi) = \int_U f \varphi$. The coefficients and $f$ are arbitrary functions here; an integral whose integrand is not integrable is read as $0$. For bounded measurable coefficients and $f \in L^2(U)$ both integrands are integrable and this is the usual weak formulation.

Howard's slides test against all $v \in H^1_0(U)$. For $u \in H^1(U)$, bounded measurable coefficients and
$f \in L^2(U)$ both sides are continuous in $v$ for the $H^1$ norm, and $H^1_0(U)$ is the closure of
$C^\infty_c(U)$, so the two formulations agree. Boundary conditions
are not part of this notion.

## Background

- [Sobolev space $H^1(U)$](mem-h1-on.md): the space of the unknown.
- [Test function on an open set](is-test-function-on.md): the functions tested against.

## Sources

- P. Howard, MATH 612 lecture slides, Texas A&M University, Spring 2020: [Weak solutions](https://people.tamu.edu/~phoward/m612/s20/elliptic1.pdf), Definitions (i) and (ii).
