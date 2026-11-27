# Quantum step of Regev's reduction: narrower Gaussian samples from a BDD solver

Given a polynomial-time algorithm solving $\mathrm{BDD}$ on $\Lambda^{*}$ within distance $d$, with $d$ below half of $\lambda_1(\Lambda^{*})$, there is a quantum polynomial-time algorithm that outputs samples from a distribution statistically close to $D_{\Lambda,\sqrt{n}/(\sqrt{2}d)}$ (more precisely of width roughly $\sqrt{n}/d$ up to constants), provided this width exceeds the smoothing parameter of $\Lambda$.

## Proof sketch

Prepare a superposition $\sum_{x\in\Lambda^{*}}\sum_{z}\rho_{d'}(z)|x+z\rangle|z\rangle$ over points near the dual lattice with Gaussian offsets $z$ of width $d'\approx d/\sqrt{n}$ per coordinate, so that $\|z\|\le d$ with overwhelming probability. Use the BDD solver to compute $x$ from $x+z$ and uncompute it, leaving $\sum_{y}\rho_{d'}(y-\Lambda^{*})|y\rangle$ (a periodic Gaussian). Its quantum Fourier transform is a Gaussian-weighted superposition over $\Lambda$ of width $1/d'$, and measuring yields a discrete Gaussian sample on $\Lambda$.

## Depends on

- [Bounded distance decoding](bounded-distance-decoding.md)
- [Discrete Gaussian sampling problem](discrete-gaussian-sampling-problem.md)

## Proof depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005).
