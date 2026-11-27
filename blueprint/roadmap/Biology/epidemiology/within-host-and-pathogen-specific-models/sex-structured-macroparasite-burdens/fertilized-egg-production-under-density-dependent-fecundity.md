# Fertilized egg production under density-dependent fecundity

**Setting.** Use the sex-structured burden model of the companion article: burden pgf $G$ with mean $m$, each parasite female with probability $\alpha$ ($\beta = 1-\alpha$), and polygamous mating. Female fecundity is negatively density dependent: in a host with $n$ parasites each female lays eggs at rate

$$\lambda(n) = \lambda_0 e^{-\gamma(n-1)} = \lambda_0 z^{n-1}, \qquad z = e^{-\gamma} \in (0, 1],$$

where $\lambda_0$ is the intrinsic fecundity and $\gamma \ge 0$ the strength of density dependence.

**Proposition.** Per host, the mean egg production and the mean fertilised egg production are

$$\lambda_0\,\alpha\, G'(z) \qquad\text{and}\qquad \lambda_0\,\alpha\, G'(z)\Big[1 - \frac{G'(\alpha z)}{G'(z)}\Big].$$

Consequently:

- the mean effective transmission contribution per female (eggs per female relative to $\lambda_0$) is $\psi = G'(z)/m$;
- the fraction of eggs that are fertilised, i.e. the mating probability under density dependence, is

$$\phi = 1 - \frac{G'(\alpha z)}{G'(z)},$$

which reduces to $1 - G'(\alpha)/m$ when $z = 1$;
- in a mean-burden transmission model the fertilised egg output is $\lambda_0\alpha m\,\psi(m)\,\phi(m) = \lambda_0\alpha G'(z)\big[1 - G'(\alpha z)/G'(z)\big]$.

## Depends on

- [Mating probability of polygamous macroparasites](mating-probability-of-polygamous-macroparasites.md)

## Proof sketch

Conditional on $n$ parasites and $j$ females, a host produces $j\lambda_0 z^{n-1}$ eggs. Summing over $j \sim \mathrm{Binomial}(n,\alpha)$ gives $n\alpha\lambda_0 z^{n-1}$, and averaging over $n$ gives $\lambda_0\alpha\sum_n n p_n z^{n-1} = \lambda_0\alpha G'(z)$. For fertilised eggs, remove the all-female hosts, which contribute $n\alpha^n\lambda_0 z^{n-1}$. Their average is $\lambda_0\alpha\sum_n n p_n(\alpha z)^{n-1} = \lambda_0\alpha G'(\alpha z)$. The ratios give $\psi$ and $\phi$. Density dependence enters only by evaluating the pgf derivative at $z$ and $\alpha z$ instead of $1$ and $\alpha$.

## Sources

- Gonzalo Maximiliano Lopez and Juan Pablo Aparicio, "Mathematical Modeling of Mating Probability and Fertile Egg Production in Helminth Parasites", *Bulletin of Mathematical Biology* 86 (2024), 131, <https://doi.org/10.1007/s11538-024-01356-3>. Preprint version: arXiv:2202.11552 (2022), Section 4 and Propositions A.2 and A.3, <https://doi.org/10.48550/arXiv.2202.11552>.
