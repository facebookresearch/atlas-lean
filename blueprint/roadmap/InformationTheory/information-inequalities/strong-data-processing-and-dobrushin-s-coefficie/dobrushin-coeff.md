# Dobrushin's contraction coefficient

For a Markov kernel $\kappa$ from $X$ to $Y$, Dobrushin's coefficient is

$$
\eta_{\mathrm{TV}}(\kappa) = \sup_{x, x' \in X} \mathrm{TV}(\kappa(x), \kappa(x')),
$$

with $\mathrm{TV}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$. It lies in $[0, 1]$ and is $0$ when $X$
is empty. The diagonal terms vanish, so it agrees with the supremum over $x \ne x'$ in Polyanskiy
and Wu.

## Background

- [Total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md):
  the distance between rows.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 33.4 (the right-hand side `sup_{x ≠ x'} TV(P_{Y|X=x}, P_{Y|X=x'})`; the diagonal terms vanish).
