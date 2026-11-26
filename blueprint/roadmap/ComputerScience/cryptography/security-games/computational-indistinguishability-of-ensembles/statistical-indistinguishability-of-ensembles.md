# Statistical indistinguishability of distribution ensembles

Two distribution ensembles $X = (X_n)$ and $Y = (Y_n)$ on bit strings are *statistically indistinguishable* if there is a negligible function $\varepsilon$ such that for every $n$ and every set $E$ of bit strings,

$$\Pr[X_n \in E] \le \Pr[Y_n \in E] + \varepsilon(n).$$

Equivalently, the total variation (statistical) distance $\Delta(X_n, Y_n) = \sup_E |\Pr[X_n \in E] - \Pr[Y_n \in E]|$ is negligible. No bound is placed on the support size or on the lengths of the strings in the supports.

## Depends on

- [Total variation distance between finite measures](../../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
