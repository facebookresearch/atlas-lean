# Discrete Gaussian sampling problem

For $s>0$ and a lattice $\Lambda$, the discrete Gaussian $D_{\Lambda,s}$ assigns to $x\in\Lambda$ probability proportional to $\rho_s(x)=\exp(-\pi\|x\|^{2}/s^{2})$. The *discrete Gaussian sampling problem* $\mathrm{DGS}_\varphi$, for a function $\varphi$ of the lattice, asks: given a basis of $\Lambda$ and $s\ge\varphi(\Lambda)$, output a sample from a distribution statistically close to $D_{\Lambda,s}$. Sampling at width $s$ slightly above the smoothing parameter yields short independent vectors and hence solves $\mathrm{SIVP}$ with approximation factor proportional to $s/\lambda_n$.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005).
- Craig Gentry, Chris Peikert, Vinod Vaikuntanathan, "Trapdoors for Hard Lattices and New Cryptographic Constructions", STOC (2008).
