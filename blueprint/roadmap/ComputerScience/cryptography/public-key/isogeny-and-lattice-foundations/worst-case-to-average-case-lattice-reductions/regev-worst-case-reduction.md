# Regev's quantum worst-case to average-case reduction for LWE

Let $n$ be the dimension, $q=q(n)\le 2^{\mathrm{poly}(n)}$ and $\alpha=\alpha(n)\in(0,1)$ with $\alpha q>2\sqrt{n}$. If there is a probabilistic polynomial-time algorithm solving search $\mathrm{LWE}_{n,q,\Psi_\alpha}$ (Gaussian error of standard width $\alpha q$), then there is a quantum polynomial-time algorithm solving $\mathrm{GapSVP}_\gamma$ and $\mathrm{SIVP}_\gamma$ on arbitrary $n$-dimensional lattices with $\gamma=\widetilde{O}(n/\alpha)$. The same holds for decision LWE when $q$ is prime and polynomially bounded, via search-to-decision.

## Proof sketch

Start with samples from $D_{\Lambda,r}$ for very large $r$, which are easy to generate with LLL. Alternately apply the classical step (LWE oracle plus samples of width $r$ give BDD on $\Lambda^{*}$ at distance $\alpha q/(\sqrt{2}r)$) and the quantum step (BDD gives samples of width about $r\sqrt{n}/(\alpha q)\le r/2$). Each iteration divides the width by $\alpha q/\sqrt{n}>2$, and the iterations stop at a width $r>\sqrt{2n}\,\eta_\varepsilon(\Lambda)/\alpha$, which is the smoothing-dependent width the iterative step needs, not the smoothing parameter itself; this solves $\mathrm{DGS}_{\sqrt{2n}\eta_\varepsilon(\Lambda)/\alpha}$. Since samples of width $r$ have length up to $\sqrt{n}\,r$, the reduction from $\mathrm{GIVP}$ to $\mathrm{DGS}$ gives $n$ independent vectors of length at most $2\sqrt{2}\,n\,\eta_\varepsilon(\Lambda)/\alpha$, and with $\eta_\varepsilon(\Lambda)\le\omega(\sqrt{\log n})\,\lambda_n(\Lambda)$ for negligible $\varepsilon$ this is $\mathrm{SIVP}_{\widetilde{O}(n/\alpha)}$; $\mathrm{GapSVP}$ follows via a related reduction.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)
- [Quantum step of Regev's reduction: narrower Gaussian samples from a BDD solver](regev-quantum-step.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005), Theorem 3.1, Corollary 3.16, Lemma 3.17.
