# Discrete Gaussian sampling problem

For $s>0$ and a lattice $\Lambda$, the discrete Gaussian $D_{\Lambda,s}$ assigns to $x\in\Lambda$ probability proportional to $\rho_s(x)=\exp(-\pi\|x\|^{2}/s^{2})$. The *discrete Gaussian sampling problem* $\mathrm{DGS}_\varphi$, for a function $\varphi$ of the lattice, asks: given a basis of $\Lambda$ and $s\ge\varphi(\Lambda)$, output a sample from a distribution statistically close to $D_{\Lambda,s}$. Samples from $D_{\Lambda,s}$ have length at most $\sqrt{n}\,s$ except with probability $2^{-\Omega(n)}$, not length of order $s$. For $\varepsilon\le1/10$ and $\varphi(\Lambda)\ge\sqrt2\,\eta_\varepsilon(\Lambda)$, where $\eta_\varepsilon$ is the smoothing parameter, there is a polynomial-time reduction from $\mathrm{GIVP}_{2\sqrt{n}\varphi}$ to $\mathrm{DGS}_\varphi$: $n^{2}$ samples at a width $r\in(\varphi(\Lambda),2\varphi(\Lambda)]$, found by trying the widths $\tilde\lambda_n2^{-i}$ from an LLL basis, contain $n$ linearly independent vectors, all of length at most $2\sqrt{n}\,\varphi(\Lambda)$, with probability exponentially close to $1$. Since $\eta_\varepsilon(\Lambda)\le\sqrt{\ln(2n(1+1/\varepsilon))/\pi}\cdot\lambda_n(\Lambda)$, this solves $\mathrm{SIVP}$ with approximation factor $O(\sqrt{n}\,\varphi(\Lambda)/\lambda_n(\Lambda))$; the factor $\sqrt{n}$ and the smoothing-dependent lower bound on the width are both needed.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005), Corollary 3.16, Lemma 3.17.
- Craig Gentry, Chris Peikert, Vinod Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", STOC (2008).
