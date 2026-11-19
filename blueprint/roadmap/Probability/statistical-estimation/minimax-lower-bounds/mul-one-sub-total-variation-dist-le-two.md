# Le Cam's two-point lower bound for one deterministic estimator

Let $P_0$ and $P_1$ be probability measures on $\Omega$, let $\ell : \Theta \times \Theta \to [0, \infty]$
be a loss and $\alpha \in [0, \infty]$ with $\ell(\theta_0, \theta_1) \le \alpha (\ell(\theta_0, t) + \ell(\theta_1, t))$
for every $t \in \Theta$. Every deterministic estimator $T : \Omega \to \Theta$ for which $\omega \mapsto \ell(\theta_i, T(\omega))$
is measurable ($i = 0, 1$) satisfies

$$
\ell(\theta_0, \theta_1)\, \bigl(1 - \mathrm{TV}(P_0, P_1)\bigr) \le 2\alpha \max\Bigl(\mathbb{E}_{P_0}\, \ell(\theta_0, T),\ \mathbb{E}_{P_1}\, \ell(\theta_1, T)\Bigr).
$$

The expectations are lower Lebesgue integrals, so no integrability is assumed. The proof bounds
both risks below on the [common part](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/exists-le-le-measure-univ-eq.md)
of $P_0$ and $P_1$, which has mass $1 - \mathrm{TV}(P_0, P_1)$.

## Informally uses

- [Common part of two probability measures](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/exists-le-le-measure-univ-eq.md):
  the measure on which both risks are compared.

## Background

- [Two-point testing bound](../../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/one-sub-total-variation-dist-le-add-comp.md):
  the testing version of the same reduction.

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025, Theorem 31.1, eq. (31.2); the $\alpha$-triangle inequality (31.1) is only needed at the pair $\theta_0, \theta_1$.
