# Peikert's classical reduction from GapSVP to LWE with exponential modulus

For functions $\zeta(n)\ge\gamma(n)\ge 1$, the problem $\zeta$-to-$\gamma$-$\mathrm{GapSVP}$ ($\mathrm{GapSVP}_{\zeta,\gamma}$) is $\mathrm{GapSVP}_\gamma$ restricted to inputs $(B,d)$ with the promise $\lambda_1(\mathcal{L}(B))\le\zeta(n)$, scaled so that the Gram–Schmidt vectors of $B$ have length at least $1$, and $1\le d\le\zeta(n)/\gamma(n)$. Let $\alpha=\alpha(n)\in(0,1)$, $\gamma=\gamma(n)\ge n/(\alpha\sqrt{\log n})$, $\zeta=\zeta(n)\ge\gamma(n)$ and $q=q(n)\ge\zeta(n)\cdot\omega\bigl(\sqrt{\log n/n}\bigr)$. Then there is a classical probabilistic polynomial-time reduction from solving $\mathrm{GapSVP}_{\zeta,\gamma}$ in the worst case (with overwhelming probability) to solving search $\mathrm{LWE}_{n,q,\Psi_\alpha}$ using $\mathrm{poly}(n)$ samples (Peikert, Theorem 3.1). No condition on the factorization of $q$ is needed; one is used only for the separate search-to-decision reduction. For $\zeta\ge 2^{n/2}$, LLL reduction makes $\mathrm{GapSVP}_{\zeta,\gamma}$ equivalent to standard $\mathrm{GapSVP}_\gamma$, so for $q\ge 2^{n/2}$ a polynomial-time algorithm for search LWE yields a classical probabilistic polynomial-time algorithm for $\mathrm{GapSVP}_{\gamma}$ with $\gamma=\widetilde{O}(n/\alpha)$. For smaller $q$, down to $q=\omega(\sqrt{n}/\alpha)$ and in particular for $q=\mathrm{poly}(n)$, the same theorem with $\zeta$ as large as $q\ge\zeta\cdot\omega(\sqrt{\log n/n})$ allows gives the same approximation factor $\gamma=\widetilde{O}(n/\alpha)$, for the promise problem $\mathrm{GapSVP}_{\zeta,\gamma}$ (Remark 3.2).

## Proof sketch

Replace the quantum step by a classical one that works only for the decisional problem: use the LWE oracle as a BDD solver on the dual and observe that a BDD solver for distance about $\lambda_1(\Lambda^{*})/\gamma$ yields a GapSVP decider via the classical Goldreich–Goldwasser-type interactive test on lattices, which does not need narrow Gaussian samples. The modulus grows with $\zeta$ because the reduction must start from Gaussian samples wide enough to be generated classically for any lattice satisfying the promise $\lambda_1\le\zeta$.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)

## Sources

- Chris Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest Vector Problem", STOC (2009), Definition 2.7, Remark 2.8, Theorem 3.1 and Remark 3.2.
