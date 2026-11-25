# Robertson's limit of artificial selection

For an additive allele at frequency $0 < p < 1$ in a diploid population of size $N$ with genic selection coefficient $s$, the
[diffusion fixation probability](kimura-fixation.md) with $\sigma = 2Ns$ is $u_\sigma(p) = (1 - e^{-2\sigma p})/(1 - e^{-2\sigma})$, and

$$u_\sigma(p) = p + \sigma\, p(1 - p) + O(\sigma^2) \qquad (\sigma \to 0).$$

The expected eventual change of allele frequency is $u_\sigma(p) - p$, while the first-generation change is $s\, p(1 - p)$, so

$$\frac{u_\sigma(p) - p}{s\, p(1 - p)} \longrightarrow 2N \qquad (s \to 0,\ s \ne 0).$$

Under weak selection the total advance by the selection limit is $2N$ times the response in the first generation, for the
allele frequency and therefore for the mean of an additive trait, whose change is proportional to it. For $p \in \{0, 1\}$,
$u_\sigma(p) = p$ for every $\sigma$. With drift the [additive variance](../../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/add-var-biallelic.md) $2p(1 - p)a^2$ is eventually lost, so the limit is reached.

## Depends on

- [Kimura's fixation probability](kimura-fixation.md)
- [Additive variance at a biallelic locus](../../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/add-var-biallelic.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section IX.9, p. 449, "Genetic drift" (Robertson (1960) applied Kimura's fixation probabilities to predict the limiting phenotype under selection). The expansion is derived above.
