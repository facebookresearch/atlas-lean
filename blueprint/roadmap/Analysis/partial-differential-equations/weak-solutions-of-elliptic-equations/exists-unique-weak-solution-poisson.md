# Existence and uniqueness of weak solutions of the Dirichlet problem for Poisson's equation

Let $n \ge 1$ and let $U \subseteq \mathbb{R}^n$ be bounded and open. For every $f \in L^2(U)$ there
is a weak solution $u \in H^1_0(U)$ of

$$-\Delta u = f \text{ in } U, \qquad u = 0 \text{ on } \partial U,$$

and it is unique up to equality almost everywhere on $U$.

Howard's slides state it for $f \in H^{-1}(U)$; this is the case
$f \in L^2(U)$. The proof is the abstract theorem with $H = H^1_0(U)$ and $D$ the gradient,
using that $H^1_0(U)$ is a Hilbert space and Poincaré's inequality. In dimension $0$ the statement is false ($U$ is a point, the weak formulation forces
$f = 0$), hence the hypothesis $n \ge 1$.

## Informally uses

- [Existence and uniqueness of weak solutions of the abstract Poisson problem](exists-unique-weak-solution.md):
  the Lax–Milgram argument in abstract form.

## Background

- [Sobolev space $H^1_0(U)$](mem-h10-on.md) and
  [weak solution of a divergence-form elliptic equation](is-weak-solution-on.md).

## Sources

- P. Howard, MATH 612 lecture slides, Texas A&M University, Spring 2020: [The Lax–Milgram theorem](https://people.tamu.edu/~phoward/m612/s20/elliptic2.pdf), Theorem 6.2.1 and "Application to Poisson's equation" (Poincaré's inequality is cited
  there as Theorem 5.6.3).
