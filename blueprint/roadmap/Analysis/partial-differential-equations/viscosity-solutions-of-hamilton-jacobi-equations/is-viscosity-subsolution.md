# Viscosity subsolution of a first-order equation

Let $\Omega$ be a subset of a real normed space $E$ and $F : E \times \mathbb{R} \times E^* \to \mathbb{R}$.
A function $u$ is a viscosity subsolution of $F(x, u, Du) = 0$ on $\Omega$ if $u$ is upper
semicontinuous on $\Omega$ and, whenever $\varphi$ is a $C^1$ function and $u - \varphi$ has a local
maximum relative to $\Omega$ at $x \in \Omega$,

$$F(x, u(x), D\varphi(x)) \le 0 .$$

The test function "touches $u$ from above" at $x$, and the inequality is what a classical
subsolution would satisfy there, since at an interior maximum of $u - \varphi$ the two gradients agree
(Crandall–Ishii–Lions, (2.1)–(2.2)). The gradient is a continuous linear functional, so no inner
product is needed.

The user's guide defines the notion through second-order superjets and notes in Remarks 2.3 that
it is equivalent to the test-function form; Calder uses $C^\infty$ test functions and remarks
(Remark 2.7) that $C^1$ test functions give the same notion. Here the test functions are $C^1$.

The test functions are $C^1$ on the whole space $E$. In finite dimensions, the setting of every
theorem here that needs more than the definition, this is the same as testing with functions
that are $C^1$ near $x$, since multiplying by a smooth bump function equal to $1$ near $x$ changes
neither the local maximum nor $D\varphi(x)$.

## Sources

- M. G. Crandall and P.-L. Lions, "Viscosity solutions of Hamilton–Jacobi equations", Trans. Amer. Math. Soc. 277 (1983), 1–42.
- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Definition 2.2 and Remarks 2.3.
- J. Calder, *Lecture notes on viscosity solutions*, University of Minnesota, version of 30 July 2024, Definition 2.1 and Remark 2.7.
