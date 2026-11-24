# Viscosity solution of a first-order equation

A viscosity solution of $F(x, u, Du) = 0$ on $\Omega$ is a function that is both a
[viscosity subsolution](is-viscosity-subsolution.md) and a
[viscosity supersolution](is-viscosity-supersolution.md) on $\Omega$. Being upper and lower
semicontinuous, it is continuous on $\Omega$. The name comes from the method of vanishing viscosity,
which produces such solutions as limits of solutions of $F(x, u, Du) = \varepsilon \Delta u$; the
theory itself makes no use of it (Crandall–Ishii–Lions, Remarks 2.3).

## Background

- [Hyperbolic motions in the N-body problem](../../ordinary-differential-equations/hyperbolic-motions-in-the-n-body-problem/README.md):
  Maderna and Venturelli construct these motions from viscosity solutions of the Hamilton–Jacobi
  equation of the N-body problem; the statement there does not use this definition.

## Sources

- M. G. Crandall and P.-L. Lions, "Viscosity solutions of Hamilton–Jacobi equations", Trans. Amer. Math. Soc. 277 (1983), 1–42.
- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Definition 2.2.
- J. Calder, *Lecture notes on viscosity solutions*, University of Minnesota, version of 30 July 2024, Definition 2.1.
