# $H^1$ on the whole space

A function $u$ belongs to $H^1(\mathbb{R}^n)$ in the sense of this topic if and only if it belongs to
$W^{1,2}(\mathbb{R}^n)$ in the sense of the
[Sobolev space $W^{k,p}(\mathbb{R}^n)$](../../function-spaces/sobolev-embedding-theorem/mem-sobolev-wk.md) of the Sobolev embedding theorem.
One direction uses that $L^2$ functions are locally integrable. For the other, the order-zero
clause of $W^{1,2}$ gives some $g \in L^2$ with $\int u \varphi = \int g \varphi$ for all test
functions $\varphi$, so $u = g$ almost everywhere by the fundamental lemma of the calculus of
variations, and $u \in L^2$.

## Informally uses

- [Weak partial derivatives on the whole space](is-weak-partial-deriv-on-univ-iff.md): matches the
  first-order clauses.

## Background

- [Sobolev space $H^1(U)$](mem-h1-on.md) and
  [Sobolev space $W^{k,p}(\mathbb{R}^n)$](../../function-spaces/sobolev-embedding-theorem/mem-sobolev-wk.md): the two definitions compared.

## Sources

- J. K. Hunter, *Notes on Partial Differential Equations*, UC Davis, [Chapter 3 (Sobolev spaces)](https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf), Definition 3.23 with $k = 1$, $p = 2$, $\Omega = \mathbb{R}^n$.
