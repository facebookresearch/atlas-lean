# Tate's local functional equation

This node is still to be broken down. It covers the local zeta integrals of Tate's thesis and their functional
equation, which define Tate's local factors. Let $F$ be a local field, $\psi$ a nontrivial unitary additive character, $dx$ a
[Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md) on $F$ and $d^\times x$ a Haar measure on $F^\times$, $\hat f$ the Fourier transform of a
Schwartz–Bruhat function $f$ with respect to $\psi$ and $dx$, and $\chi$ a quasi-character of $F^\times$, not necessarily unitary.

- **Local zeta integrals.** $Z(f, \chi, s) = \int_{F^\times} f(x) \chi(x) \lvert x \rvert^s \, d^\times x$ converges for
  $\operatorname{Re} s$ large and continues meromorphically.
- **Local functional equation.** There is a meromorphic function $\gamma(\chi, \psi, s)$, independent of $f$ and of $d^\times x$ but
  depending on $dx$ (so written $\gamma(\chi, \psi, dx, s)$ when the measure varies), with
  $Z(\hat f, \chi^{-1}, 1 - s) = \gamma(\chi, \psi, s)\, Z(f, \chi, s)$ for all $f$; it is written
  $\gamma = \varepsilon(\chi, \psi, s) L(\chi^{-1}, 1 - s) / L(\chi, s)$ with Tate's local $L$- and $\varepsilon$-factors.

## Expansion

A good expansion has statement pages for the convergence and continuation of the local zeta integrals and for the local
functional equation, with the computation of the factors at unramified, ramified and archimedean places, each citing the
source below with locators. The normalisation of $\gamma$ depends on $dx$ through $\hat f$.

## Depends on

- [Haar measure](../../MeasureTheory/haar-measure/is-haar-measure.md), for the measures on $F$ and $F^\times$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: §4 (local fields, characters and Fourier analysis), Theorem 4.18, pp. 19–20, in particular (e), the local
  functional equation for every nontrivial $\psi$ and Haar measure $dx$.
