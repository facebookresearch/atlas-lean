# Quantum worst-case hardness of continuous LWE

For $\beta\in(0,1)$, $\gamma\ge2\sqrt n$ and $\gamma/\beta$ polynomially bounded, there is a polynomial-time quantum reduction from discrete Gaussian sampling with width $2\sqrt n\,\eta_\varepsilon(L)/\beta$ to decision CLWE; consequences cover GapSVP and SIVP and homogeneous CLWE.

Let $\beta=\beta(n)\in(0,1)$ and $\gamma=\gamma(n)\ge2\sqrt n$ with $\gamma/\beta$ polynomially bounded, and let $\varepsilon=\varepsilon(n)$ be negligible in $n$ (Bruna et al., Section 2.1, assume this throughout unless stated otherwise, for example $\varepsilon=\exp(-n)$). $\eta_\varepsilon(L)$ is the smoothing parameter, and an instance of $\mathrm{DGS}_\varphi$ is a lattice $L$ and $r\ge\varphi(L)$, to be answered by an independent sample whose distribution is within negligible statistical distance of the discrete Gaussian $D_{L,r}$.

**Theorem.** There is a polynomial-time quantum reduction from $\mathrm{DGS}_{2\sqrt n\,\eta_\varepsilon(L)/\beta}$ to $\mathrm{CLWE}_{\beta,\gamma}$.

**Consequences** (same parameter conditions):

1. there is a polynomial-time quantum reduction from $\mathrm{SIVP}_\alpha$ and $\mathrm{GapSVP}_\alpha$ to $\mathrm{CLWE}_{\beta,\gamma}$ for some $\alpha=\tilde O(n/\beta)$;
2. there is a polynomial-time quantum reduction from $\mathrm{DGS}_{2\sqrt{2n}\,\eta_\varepsilon(L)/\beta}$ to $\mathrm{hCLWE}_{\beta,\gamma}$.

## Proof sketch

The proof iterates two steps as Regev's reduction for LWE does. The classical step (Bruna–Regev–Song–Tang, Lemma 3.3), given a CLWE oracle, a lattice $L$, $r\ge2q\,\eta_\varepsilon(L)$ with $q=\gamma/\beta$, and polynomially many samples from $D_{L,r_i}$ for polynomially many widths $r_i\ge r$, solves $\mathrm{BDD}_{L^*,\gamma/(\sqrt2r)}$; Regev's quantum step turns a BDD solver into samples of a narrower discrete Gaussian. Consequence 1 follows from the standard reductions from SIVP and GapSVP to DGS (Regev, Section 3.3), stated as Corollary 3.2; consequence 2 combines the theorem at $\beta/\sqrt2$ with the reduction from CLWE to hCLWE (Lemma 4.1), stated as Corollary 4.2.

## Expansion

A good expansion adds pages for:

- the classical step: for $\beta\in(0,1)$ and $\gamma\ge2\sqrt n$ with $q=\gamma/\beta$ polynomially bounded, a probabilistic polynomial-time algorithm with a $\mathrm{CLWE}_{\beta,\gamma}$ oracle, given a lattice $L$, a parameter $r\ge2q\,\eta_\varepsilon(L)$ and polynomially many samples from $D_{L,r_i}$ for polynomially many widths $r_i\ge r$, solves $\mathrm{BDD}_{L^*,d}$ for $d=\gamma/(\sqrt2r)$ (Bruna–Regev–Song–Tang, Lemma 3.3);
- the reduction from CLWE to hCLWE (Bruna–Regev–Song–Tang, Lemma 4.1).

## Depends on

- [Continuous learning with errors (CLWE)](continuous-lwe.md)
- [Homogeneous continuous learning with errors (hCLWE)](homogeneous-continuous-lwe.md)
- [Approximate lattice problems GapSVP and SIVP](../../cryptography/public-key/isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/gapsvp-and-sivp.md)
- [Discrete Gaussian sampling problem](../../cryptography/public-key/isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/discrete-gaussian-sampling-problem.md)
- [Smoothing parameter of a lattice](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-gaussians-and-smoothing-parameter/smoothing-parameter.md)

## Proof depends on

- [Quantum step of Regev's reduction: narrower Gaussian samples from a BDD solver](../../cryptography/public-key/isogeny-and-lattice-foundations/worst-case-to-average-case-lattice-reductions/regev-quantum-step.md)

## Sources

- Joan Bruna, Oded Regev, Min Jae Song, Yi Tang, "Continuous LWE", ACM STOC 2021; numbers from arXiv:2005.09595v2: Section 2.1 (default $\varepsilon$), Definition 2.14, Theorem 3.1, Corollary 3.2, Lemma 3.3, Lemma 4.1 and Corollary 4.2.
