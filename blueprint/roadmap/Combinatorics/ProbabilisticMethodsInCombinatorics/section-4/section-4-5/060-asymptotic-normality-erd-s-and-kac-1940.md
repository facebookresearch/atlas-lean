---
article_id: af_ab8261de0f295e9585b53407
declaration: theorem
origin: cited
lean: ErdosKac.erdos_kac
---

# Theorem 4.5.3 (Asymptotic normality: Erdős and Kac 1940)

With $x \in [n]$ uniformly chosen at random, $\nu(x)$ is asymptotically normal, i.e., for every $\lambda \in \mathbb{R}$, $\lim_{n \to \infty} \mathbb{P}_{x \in [n]}\!\left( \frac{\nu(x) - \log \log n}{\sqrt{\log \log n}} \geq \lambda\right) = \frac{1}{\sqrt{2\pi}} \int_\lambda^\infty e^{-t^2/2}\, dt$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 4.5.2 (Central limit theorem for sums of independent Bernoullis)](059-central-limit-theorem-for-sums-of-indepe.md)
- [Theorem 4.5.4 (Method of moments)](061-method-of-moments.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Section 4.5](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
