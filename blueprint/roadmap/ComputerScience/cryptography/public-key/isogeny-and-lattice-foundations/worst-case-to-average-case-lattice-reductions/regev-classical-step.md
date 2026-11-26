# Classical step of Regev's reduction: BDD on the dual from an LWE oracle

Let $q\ge 2$, $\alpha\in(0,1)$ and let $\Lambda$ be a lattice with $r\ge\sqrt{2}\,q\,\eta_\varepsilon(\Lambda)$ for negligible $\varepsilon$, where $\eta_\varepsilon$ is the smoothing parameter. Given an oracle solving search $\mathrm{LWE}_{n,q,\Psi_\alpha}$ (with Gaussian error of width $\alpha q$, over polynomially many samples) and polynomially many samples from $D_{\Lambda,r}$, there is a classical probabilistic polynomial-time algorithm solving $\mathrm{BDD}$ on the dual lattice $\Lambda^{*}$ for targets within distance $\alpha q/(\sqrt{2}\,r)$.

## Proof sketch

Given a BDD target $x=y+e$ with $y\in\Lambda^{*}$, map each Gaussian sample $v\in\Lambda$ to an LWE-style sample $(a,b)=(B^{-1}v\bmod q,\ \langle v,x\rangle/q+\text{small Gaussian}\bmod 1)$: since $\langle v,y\rangle$ is an integer determined by $y$'s coordinates mod $q$, the second component is $\langle a,s\rangle/q$ plus an error $\langle v,e\rangle/q$ that is close to Gaussian of width about $r\|e\|/q\le\alpha/\sqrt{2}$ after adding compensating noise. The LWE oracle recovers $s=(B^{*})^{-1}y\bmod q$, and iterating on $(x-\text{lift})/q$ recovers $y$.

## Depends on

- [Bounded distance decoding](bounded-distance-decoding.md)
- [Discrete Gaussian sampling problem](discrete-gaussian-sampling-problem.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", JACM (2009); STOC (2005).
