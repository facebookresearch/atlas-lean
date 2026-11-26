# Dirichlet limit of within-host sequence-type frequencies

Work in the [host-structured virus model](marginal-type-frequencies-of-a-host-structured-virus-population.md) under its assumptions (A1) to (A3), with $\lambda_N/\gamma_N \to \theta > 0$. Pick a host $\tilde m$ uniformly at random and let

$$W^N(T) = \frac1N \sum_{n=1}^N \delta_{X^N_{\tilde m, n}(T)} \in \mathcal M_1([K]^L)$$

be the sequence-type frequencies of all virions in that host. For $\psi = (\psi_\ell)_{\ell \in [L]} \in (\mathcal M_1([K]))^L$ write $\psi^\otimes = \psi_1 \otimes \cdots \otimes \psi_L$ for the product measure on $[K]^L$.

**Theorem.**

1. In case (i), $\lambda_N/(M\mu_N) \to 0$: $W^N(T) \Rightarrow \mathrm{Dir}(\theta\,\nu^\otimes)$, where $\nu^\otimes$ is the product of the marginals of the mutation law $\nu$.
2. In case (ii), $\lambda_N/(M\mu_N) \to C > 0$: $W^N(T)$ converges in distribution to a Dirichlet law with random parameter $\theta\,\psi^\otimes$, where $\psi$ has the law of the limit $\bar X$ of the locus-wise population frequencies (independent $\mathrm{Dir}(\frac{1+\theta}{C}\nu_\ell)$ components).
3. If a population-wide sample $\mathfrak s$ has locus-wise frequencies $\bar X^{N,\mathfrak s}(T)$ with $|\bar X^{N,\mathfrak s}(T) - \bar X^N(T)| \to 0$ almost surely, then jointly $\big(W^N(T), \bar X^{N,\mathfrak s}(T)\big) \Rightarrow \big(\mathrm{Dir}(\theta\bar X^\otimes), \bar X\big)$.

The same limits hold for the frequencies in a within-host sample of $j_N \to \infty$ virions, $j_N \le N$.

**Key lemma (colored Hoppe urn).** Let $W^N$ be the type frequencies obtained by coloring the families after $j_N \to \infty$ draws from a Hoppe urn with parameter $\theta_N \to \theta > 0$, each family receiving an i.i.d. color with law $p_N \to p$ in distribution, where $p$ is either deterministic or has a Lebesgue density. Then $W^N$ converges in distribution to $\mathrm{Dir}(\theta p)$ (with random parameter when $p$ is random).

## Depends on

- [Marginal type frequencies of a host-structured virus population](marginal-type-frequencies-of-a-host-structured-virus-population.md)
- [Hoppe's urn generates the Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/hoppe-law-eq-ewens-prob.md)

## Expansion

Backward in time the ancestral lines of a within-host sample first coalesce through replication and are lost to the host through reinfection, at rates whose ratio is $\theta$; this is exactly a reversed Hoppe urn, so the sample splits into families according to the Ewens partition with parameter $\theta$, and about $\theta\log j_N$ families survive. In a second phase recombination, which is faster than mutation, scatters the loci of each family onto lines in different hosts, so each locus of each family independently samples an allele from the population-wide frequency at that locus. That makes the family types i.i.d. with law $\psi^\otimes$ (the product of the locus-wise frequencies), and the colored-urn lemma turns Ewens families with i.i.d. colors into a Dirichlet law with parameter $\theta\psi^\otimes$. Linkage within a host is therefore completely broken in the limit.

## Sources

- R. Eichhorn and C. Pokalyuk, "On a Neutral Host-Virus Model with Recombination", arXiv preprint (2025), Theorems 2.11 and 2.13 and Lemma 4.1. <https://doi.org/10.48550/arXiv.2509.19253>