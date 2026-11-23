# Additive duality of adeles and the volume of A/K

This node is still to be broken down. It covers the harmonic analysis of the additive group of the adele
ring $\mathbb{A}$ of a number field $K$ on which the
[Poisson summation formula for adeles](adelic-poisson-summation.md) rests.

- **Local duality.** For each place $v$, the standard additive character $\psi_v$ of $K_v$, the
  isomorphism $a \mapsto (x \mapsto \psi_v(ax))$ of $K_v$ onto its Pontryagin dual, the conductor of $\psi_v$, the
  self-dual Haar measure $dx_v$ (Lebesgue measure on $\mathbb{R}$, twice the Lebesgue measure on $\mathbb{C}$, and at a
  finite place the measure giving $\mathcal{O}_v$ volume $\mathrm{N}(\mathfrak{d}_v)^{-1/2}$ for the local different
  $\mathfrak{d}_v$), the local Schwartz–Bruhat functions and the Fourier inversion formula on them.
- **Global duality.** The standard character $\psi = \prod_v \psi_v$ of $\mathbb{A}$, the isomorphism
  $a \mapsto \psi(a \cdot)$ of $\mathbb{A}$ onto its Pontryagin dual, the triviality of $\psi$ on $K$, and the
  identification of the annihilator of $K$ with $K$ itself, so that $K$ is the dual of the compact group
  $\mathbb{A}/K$.
- **Volume and Fourier inversion on $\mathbb{A}/K$.** The quotient $\mathbb{A}/K$ has volume $1$ for the product measure
  $dx = \prod_v dx_v$ and the counting measure on $K$, and Fourier inversion holds on $\mathbb{A}/K$ for the
  periodization of a Schwartz–Bruhat function.

A good expansion has pages for the local standard characters and self-dual measures, for local Fourier
inversion on Schwartz–Bruhat functions, for the self-duality of $\mathbb{A}$ and $K^\perp = K$, for the volume of
$\mathbb{A}/K$, and for Fourier inversion on the compact group $\mathbb{A}/K$, each with a precise statement and the
locators below.

## Depends on

- [Adelic norm](adeles-and-ideles/adelic-norm.md), for the normalized absolute values of the completions

## Sources

- B. Poonen, *Tate's thesis*, lecture notes for MIT 18.786 (Spring 2015), PDF of 2025-10-11,
  <https://math.mit.edu/~poonen/786/notes.pdf>: the paragraph after Definition 4.5 (standard characters),
  §4.4 (local Schwartz–Bruhat functions), Definitions 4.6 and 4.7 and Proposition 4.8 (self-dual
  measures and Fourier inversion), §5.2 with Corollary 5.2 (self-duality of $\mathbb{A}$), Proposition 5.3
  ($\psi|_K = 1$), Corollary 5.4 ($K^\perp = K$), §5.3 and Proposition 5.5 (the volume of $\mathbb{A}/K$ is $1$), and
  the proof of Theorem 5.7 (Fourier inversion on $\mathbb{A}/K$) with Remark 5.8.
