# Gottesman–Kitaev–Preskill code

Let $q$ and $p$ be the position and momentum operators of a harmonic oscillator, $[q, p] = i$, let $n \ge 2$ be an integer
and $\alpha > 0$. The Gottesman–Kitaev–Preskill (GKP) code encoding a qudit of dimension $n$ in the oscillator is the
simultaneous $+1$ eigenspace of the commuting displacement operators

$$S_q = e^{2\pi i q / \alpha}, \qquad S_p = e^{-i n p \alpha},$$

with logical operators $\bar Z = e^{2\pi i q / (n\alpha)}$ and $\bar X = e^{-i p \alpha}$. Its ideal codewords are the
non-normalizable states $|\bar j\rangle = \sum_{s \in \mathbb{Z}} |q = \alpha(n s + j)\rangle$, $j = 0, \dots, n - 1$, combs
of position eigenstates; for $n = 2$ and $\alpha = \sqrt{\pi}$ the code is symmetric in $q$ and $p$. By measuring
$S_q$ and $S_p$ (the values of $q$ modulo $\alpha$ and of $p$ modulo $2\pi/(n\alpha)$) and shifting back, the code corrects
every displacement $e^{-i u p} e^{i v q}$ with $|u| < \alpha/2$ and $|v| < \pi/(n\alpha)$. Normalizable approximate
codewords replace the combs by Gaussian-damped sums of squeezed states.

## Expansion

A sound expansion adds pages for the canonical commutation relation and Weyl displacement operators on
$L^2(\mathbb{R})$, the commutation of $S_q$ and $S_p$ from $e^A e^B = e^{[A, B]} e^B e^A$, and the correction of small
shifts (Gottesman, Kitaev and Preskill, Section IV, from the large-$d$ limit of the shift-resistant qudit codes of
Section II); the statement with non-normalizable codewords needs a precise formulation, for instance on tempered
distributions, before it can be stated in Lean.

## Sources

- D. Gottesman, A. Kitaev and J. Preskill, *Encoding a qubit in an oscillator*, Phys. Rev. A 64 (2001), 012310, arXiv:quant-ph/0008040, Section II (shift-resistant qudit codes, "amplitude shifts by less than $r_1/2$ and phase shifts by less than $r_2/2$ can be corrected") and Section IV, equations (21)–(28).
