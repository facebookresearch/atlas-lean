# Viscosity supersolution of a first-order equation

A function $u$ is a viscosity supersolution of $F(x, u, Du) = 0$ on $\Omega$ if $u$ is lower
semicontinuous on $\Omega$ and, whenever $\varphi$ is a $C^1$ function and $u - \varphi$ has a local
minimum relative to $\Omega$ at $x \in \Omega$,

$$F(x, u(x), D\varphi(x)) \ge 0 .$$

This is the mirror image of a [viscosity subsolution](is-viscosity-subsolution.md), with test
functions touching from below. The two notions are not exchanged by replacing $F$ with $-F$: see
the [eikonal example](is-viscosity-solution-neg-abs.md).

## Sources

- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Definition 2.2.
- J. Calder, *Lecture notes on viscosity solutions*, University of Minnesota, version of 30 July 2024, Definition 2.1.
