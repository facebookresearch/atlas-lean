# Dobrushin's contraction

Let $\kappa$ be a Markov kernel from $X$ to $Y$ and $\mu$, $\nu$ probability measures on $X$, and
write $\kappa \circ \mu$ for the law of the output when the input has law $\mu$. Then

$$
\mathrm{TV}(\kappa \circ \mu, \kappa \circ \nu) \le \eta_{\mathrm{TV}}(\kappa)\, \mathrm{TV}(\mu, \nu).
$$

No countability or standard-Borel hypothesis is used. The proof writes $\mu = m + \mu_1$ and
$\nu = m + \nu_1$ with $m$ the [common part](../total-variation-and-pinsker-s-inequality/exists-le-le-measure-univ-eq.md)
of $\mu$ and $\nu$, so that $\mu_1$ and $\nu_1$ both have mass $t = \mathrm{TV}(\mu, \nu)$, and
compares $\kappa \circ \mu_1$ with $\kappa \circ \nu_1$ on each event $B$ by averaging
$\kappa(x)(B) - \kappa(x')(B) \le \eta_{\mathrm{TV}}(\kappa)$ over $x \sim \mu_1$, $x' \sim \nu_1$.

## Informally uses

- [Common part of two probability measures](../total-variation-and-pinsker-s-inequality/exists-le-le-measure-univ-eq.md):
  the decomposition of $\mu$ and $\nu$.

## Background

- [Doeblin's argument](../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/tv-dist-pow-le-of-minorization.md):
  geometric convergence of a Markov chain under a minorization condition; a minorization by $\delta \pi$ gives $\eta_{\mathrm{TV}} \le 1 - \delta$, and iterating Dobrushin's contraction gives the same rate.

## Sources

- Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge University Press, 2025), Theorem 33.4 (the inequality `η_TV ≤ sup_{x ≠ x'} TV(P_{Y|X=x}, P_{Y|X=x'})`); R. L. Dobrushin (1956).
