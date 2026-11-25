# Existence and uniqueness of weak solutions of the abstract Poisson problem

Let $H$ be a real Hilbert space, $G$ a real inner product space and $D : H \to G$ a bounded linear
map with $\beta \|u\|^2 \le \|D u\|^2$ for some $\beta > 0$. Then for every bounded linear
functional $L$ on $H$ there is exactly one $u \in H$ with

$$\langle D u, D v \rangle = L(v) \quad \text{for all } v \in H.$$

This is the abstract form of the application of the Lax–Milgram theorem to Poisson's equation: for
$H = H^1_0(U)$, $D$ the gradient and $L(v) = \int_U f v$, the solution is the weak solution of
$-\Delta u = f$, $u = 0$ on $\partial U$; the concrete statement on domains is
[the Dirichlet problem for Poisson's equation](exists-unique-weak-solution-poisson.md).

## Informally uses

- [Poincaré-type bound gives coercivity](is-coercive-gradient-form.md): the Lax–Milgram hypothesis.
- [Solution of a coercive variational problem](../../numerical-analysis/c-a-s-lemma/variational-solution.md): the Lax–Milgram
  theorem, together with Céa's lemma.

## Sources

- P. Howard, MATH 612 lecture slides, Texas A&M University, Spring 2020: [The Lax–Milgram theorem](https://people.tamu.edu/~phoward/m612/s20/elliptic2.pdf), Theorem 6.2.1 and "Application to Poisson's equation".
