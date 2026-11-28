# Gaussian product theorem

The product of two spherical Gaussians centred at two points is a single Gaussian centred at their exponent-weighted mean, times a constant that decays with the squared distance between the centres.

For $\alpha,\beta>0$ and $A,B\in\mathbb R^3$, with $P=\dfrac{\alpha A+\beta B}{\alpha+\beta}$ and $\mu=\dfrac{\alpha\beta}{\alpha+\beta}$, for all $r\in\mathbb R^3$

$$
e^{-\alpha|r-A|^2}\,e^{-\beta|r-B|^2}=e^{-\mu|A-B|^2}\,e^{-(\alpha+\beta)|r-P|^2},
$$

and consequently the overlap of the two (unnormalized) $s$-type Gaussians is

$$
\int_{\mathbb R^3}e^{-\alpha|r-A|^2}e^{-\beta|r-B|^2}\,dr=\Bigl(\frac{\pi}{\alpha+\beta}\Bigr)^{3/2}e^{-\mu|A-B|^2}.
$$

## Context

Undergraduate. Each product of two Gaussian primitives is a Gaussian (times polynomials) centred at its own product centre $P$, and a product of two contractions is a finite sum of such primitive-pair terms, generally with several different centres; this reduces overlap and kinetic integrals to one-centre quantities, while nuclear-attraction integrals (kernel centred at a nucleus) and electron-repulsion integrals (two product centres) remain multi-centre and are evaluated by recurrences built on the same identity.

## Depends on

- [Contracted Gaussian basis function](contracted-gaussian-basis-function.md)

## Proof depends on

None.

## Expansion

Complete the square: $\alpha|r-A|^2+\beta|r-B|^2=(\alpha+\beta)|r-P|^2+\mu|A-B|^2$, verified by expanding both sides. For the overlap, translate by $P$ and factor the three-dimensional integral into three one-dimensional ones (Fubini; Mathlib `integral_prod_mul`), each given by the one-dimensional Gaussian integral $\int_{\mathbb R}e^{-\gamma t^2}dt=\sqrt{\pi/\gamma}$ (Mathlib `integral_gaussian`).

## Sources

- Wim Klopper, *SCF methods, basis sets, and integrals — Lecture IV: Integrals*, European Summer School in Quantum Chemistry (ESQC 2024), slides 'The Gaussian-product theorem' and 'The overlap integral'. [esqc.org/lectures/WK4.pdf](http://www.esqc.org/lectures/WK4.pdf)
