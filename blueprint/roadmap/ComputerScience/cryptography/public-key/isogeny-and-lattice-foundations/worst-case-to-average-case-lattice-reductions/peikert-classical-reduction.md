# Peikert's classical reduction from GapSVP to LWE with exponential modulus

For $\alpha\in(0,1)$ and modulus $q\ge 2^{n/2}$ (more precisely $q$ exponential in $n$ with $\alpha q\ge\omega(\sqrt{\log n})$ and suitable factorization), solving search $\mathrm{LWE}_{n,q,\Psi_\alpha}$ in polynomial time implies a classical probabilistic polynomial-time algorithm for $\mathrm{GapSVP}_{\gamma}$ with $\gamma=\widetilde{O}(n/\alpha)$. For polynomial moduli, the same classical reduction holds from a variant ($\zeta$-to-$\gamma$-GapSVP) with weaker approximation guarantees.

## Proof sketch

Replace the quantum step by a classical one that works only for the decisional problem: use the LWE oracle as a BDD solver on the dual and observe that a BDD solver for distance about $\lambda_1(\Lambda^{*})/\gamma$ yields a GapSVP decider via the classical Goldreich–Goldwasser-type interactive test on lattices, which does not need narrow Gaussian samples. Exponential $q$ is needed to make the classical step work starting from wide samples.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)
- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

- [Classical step of Regev's reduction: BDD on the dual from an LWE oracle](regev-classical-step.md)

## Sources

- Chris Peikert, "Public-Key Cryptosystems from the Worst-Case Shortest Vector Problem", STOC (2009).
