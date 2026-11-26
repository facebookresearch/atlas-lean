# Stationary cumulants of trait and log-fitness under pure pleiotropy

Consider an infinite population of haplotypes. Each haplotype carries a negative log-fitness $X \ge 0$ and a trait value $Z \in \mathbb{R}$, both additive over sites (fitness $e^{-X}$ is multiplicative). Each generation, selection reweights the distribution $f(x, z)$ of $(X, Z)$ by $e^{-x}$, and then mutation adds a Poisson number, with mean $n\mu$, of independent mutational effects drawn from a distribution $m(x, z)$ on $(0, \infty) \times \mathbb{R}$; the trait itself is neutral. Write $M_f(u, v) = \mathbb{E}_f[e^{uX + vZ}]$ and $M_m(u, v) = \mathbb{E}_m[e^{uX + vZ}]$, and let $S = 1 - e^{-X}$ denote the selection coefficient of a mutation. Starting from an isogenic population, the moment generating function converges to

$$M_f(u, v) = \exp\left(n\mu \sum_{i=0}^{\infty} \left[M_m(u - i, v) - M_m(-i, 0)\right]\right),$$

and, whenever the moments below are finite and differentiation, summation and integration can be interchanged, the cumulants $\kappa_{a,b} = \partial_u^a \partial_v^b \log M_f(u,v)\big|_{u=v=0}$ of the stationary distribution satisfy, for integers $a, b \ge 0$ with $(a, b) \ne (0, 0)$,

$$\kappa_{a,b} = n\mu\, \mathbb{E}_m\!\left[\frac{X^a Z^b}{S}\right].$$

Thus every cumulant of the distribution over individuals is a moment of the distribution over new mutations, weighted by the expected persistence $1/S$ of a mutation.

## Proof sketch

Selection maps $M_f(u, v)$ to $M_f(u-1, v)/M_f(-1, 0)$ and Poisson mutation multiplies it by $\exp(n\mu (M_m(u,v) - 1))$. Iterating from $M_f \equiv 1$ for $\tau$ generations gives $\exp\left(n\mu \sum_{i=0}^{\tau-1} [M_m(u-i, v) - M_m(-i, 0)]\right)$, and letting $\tau \to \infty$ gives the stationary form. Differentiating $e^{-ix}(e^{ux+vz} - 1)$ at $u = v = 0$ gives $e^{-ix} x^a z^b$ for $(a, b) \ne (0,0)$, and $\sum_{i \ge 0} e^{-ix} = 1/(1 - e^{-x}) = 1/S$ for $x > 0$. Because effects on fitness are multiplicative and the trait is neutral, linkage equilibrium is maintained and following asexual haplotypes suffices. For diploids the result applies with additive effects, or in the rare-alleles approximation with heterozygous effects.

## Sources

- T. Johnson and N. Barton, Theoretical models of selection and mutation on quantitative traits, *Phil. Trans. R. Soc. B* 360 (2005), 1411–1425, <https://doi.org/10.1098/rstb.2005.1667>, PMCID PMC1569515 (Appendix A(a), Equations A1–A11).
