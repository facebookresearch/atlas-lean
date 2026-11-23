# Weak partial derivative on an open set

For $i \in \{0, \dots, n - 1\}$, a function $g$ is the weak partial derivative $\partial_i u$ of $u$
on $U \subseteq \mathbb{R}^n$ when

$$\int_U u \, \partial_i \varphi \, dx = - \int_U g \, \varphi \, dx$$

for every test function $\varphi \in C^\infty_c(U)$. Hunter's Definition 3.1 also requires
$u, g \in L^1_{\mathrm{loc}}(U)$; here that requirement is carried by the Sobolev notions built on
this one, which ask for $u, g \in L^2(U)$. The integrals are Lebesgue integrals, taken to be $0$
when the integrand is not integrable; with $u, g \in L^2(U)$ both integrands are integrable,
because $\varphi$ and $\partial_i \varphi$ are bounded with compact support.

## Background

- [Test function on an open set](is-test-function-on.md): the functions tested against.
- [Weak derivative](../../function-spaces/sobolev-embedding-theorem/is-weak-deriv.md): the whole-space weak derivative of any order;
  [the two agree](is-weak-partial-deriv-on-univ-iff.md) on $\mathbb{R}^n$ for first derivatives.

## Sources

- J. K. Hunter, *Notes on Partial Differential Equations*, UC Davis, [Chapter 3 (Sobolev spaces)](https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf), Definition 3.1.
