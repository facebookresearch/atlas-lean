# Local stability of the disease-free periodic solution

In the setting of the [next-generation operator in a periodic environment](periodic-next-generation-operator.md), with $\mathcal{R}_0 = \rho(L)$:

**Theorem (Wang–Zhao).** The disease-free periodic solution $x^*(t)$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

## Depends on

- [Next-generation operator in a periodic environment](periodic-next-generation-operator.md)

## Proof depends on

- [Periodic reproduction number and the monodromy matrix](periodic-reproduction-number-and-the-monodromy-matrix.md)

## Expansion

The linearization of the full system at $x^*(t)$ is block triangular, with the infected block $F(t) - V(t)$ and the uninfected block, whose monodromy matrix has spectral radius below $1$ by the linear stability of $x_U^*$. By Floquet theory $x^*$ is locally asymptotically stable when every Floquet multiplier lies inside the unit disc and unstable when one lies outside, so the conclusion follows from the sign equivalence between $\mathcal{R}_0 - 1$ and $\rho(\Phi_{F-V}(\omega)) - 1$. Applications to seasonal brucellosis strengthen the conclusion to global attractivity for $\mathcal{R}_0 < 1$ by a comparison argument: when $F(t) - V(t)$ is cooperative and irreducible, there is a positive $\omega$-periodic $q(t)$ such that $e^{\mu t} q(t)$, with $\mu = \omega^{-1}\ln\rho(\Phi_{F-V}(\omega))$, solves the linear system, and the infected subsystem is eventually dominated by a small perturbation of it; uniform persistence theory gives a positive periodic solution when $\mathcal{R}_0 > 1$.

## Sources

- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic environments", Journal of Dynamics and Differential Equations 20 (2008) 699–717, <https://doi.org/10.1007/s10884-008-9111-8>, Theorem 2.2.
- P. Lou, L. Wang, X. Zhang, J. Xu, K. Wang, "Modelling Seasonal Brucellosis Epidemics in Bayingolin Mongol Autonomous Prefecture of Xinjiang, China, 2010–2014", BioMed Research International (2016) 5103718, Section 3 (Lemma 3, Theorem 4 with proof (16)–(23)), <https://doi.org/10.1155/2016/5103718>.
- N. Nyerere, L. S. Luboobi, S. C. Mpeshe, G. M. Shirima, "Modeling the Impact of Seasonal Weather Variations on the Infectiology of Brucellosis", Computational and Mathematical Methods in Medicine 2020 (2020) 8972063, Lemma 1, Theorems 1–2, <https://doi.org/10.1155/2020/8972063> (PMC7586161).
