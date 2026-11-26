# Regev's quantum worst-case to average-case reduction for LWE

Let $n$ be the dimension, $q=q(n)\le 2^{\mathrm{poly}(n)}$ and $\alpha=\alpha(n)\in(0,1)$ with $\alpha q>2\sqrt{n}$. If there is a probabilistic polynomial-time algorithm solving search $\mathrm{LWE}_{n,q,\Psi_\alpha}$ (Gaussian error of standard width $\alpha q$), then there is a quantum polynomial-time algorithm solving $\mathrm{GapSVP}_\gamma$ and $\mathrm{SIVP}_\gamma$ on arbitrary $n$-dimensional lattices with $\gamma=\widetilde{O}(n/\alpha)$. The same holds for decision LWE when $q$ is prime and polynomially bounded, via search-to-decision.

## Proof sketch

Start with samples from $D_{\Lambda,r}$ for very large $r$, which are easy to generate with LLL. Alternately apply the classical step (LWE oracle plus samples of width $r$ give BDD on $\Lambda^{*}$ at distance $\alpha q/(\sqrt{2}r)$) and the quantum step (BDD gives samples of width about $r\sqrt{n}/(\alpha q)\le r/2$). After polynomially many iterations the width is near the smoothing parameter, giving short independent vectors for $\mathrm{SIVP}$; $\mathrm{GapSVP}$ follows via a related reduction.

## Depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)
- [Quantum step of Regev's reduction: narrower Gaussian samples from a BDD solver](regev-quantum-step.md)
- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)
- [Quantum step of Regev's reduction: narrower Gaussian samples from a BDD solver](regev-quantum-step.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005).
