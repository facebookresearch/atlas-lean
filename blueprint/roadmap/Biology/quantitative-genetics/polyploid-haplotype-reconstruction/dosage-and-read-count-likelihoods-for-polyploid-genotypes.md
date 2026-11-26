# Dosage and read-count likelihoods for polyploid genotypes

Fix a ploidy $K$ ($K = 4$ for tetraploids), a marker, and an offspring whose true allele-2 dosage is $d \in \{0, \dots, K\}$, a deterministic function of its hidden parental-origin state and the phased parental genotypes. Let $\varepsilon$ be the genotyping (dosage) error probability and $\epsilon$ the per-read sequencing error probability.

1. **Dosage data.** If the observation is a called dosage $y$,

$$\ell(\varepsilon) = (1 - \varepsilon)\, \mathbf 1\{y = d\} + \frac{\varepsilon}{K}\, \mathbf 1\{y \ne d\}:$$

with probability $\varepsilon$ the call is replaced by one of the other $K$ dosages, uniformly.

2. **Read counts.** If the observation is a pair $(r_1, r_2)$ of allele-1 and allele-2 read counts, generated from an effective dosage $d'$ that differs from $d$ with probability $\varepsilon$,

$$\mathbb P\bigl((r_1, r_2) \mid d'\bigr) = \binom{r_1 + r_2}{r_1} q^{r_1} (1 - q)^{r_2}, \qquad q = \Bigl(1 - \frac{d'}{K}\Bigr)(1 - \epsilon) + \frac{d'}{K}\,\epsilon,$$

and $\ell(\varepsilon) = \sum_{d'} \mathbb P((r_1, r_2) \mid d')\, \mathbb P(d' \mid d, \varepsilon)$ with $\mathbb P(d' \mid d, \varepsilon)$ given by part 1.

3. **Probability vectors.** For a general observation $y$ with likelihoods $\mathbb P(y \mid d')$, $d' = 0, \dots, K$, part 2 becomes

$$\ell(\varepsilon) = (1 - \varepsilon)\, \mathbb P(y \mid d) + \frac{\varepsilon}{K}\Bigl(\eta - \mathbb P(y \mid d)\Bigr), \qquad \eta = \sum_{d'=0}^K \mathbb P(y \mid d'),$$

which reduces to part 1 when $\mathbb P(y \mid d') = \mathbf 1\{y = d'\}$ (so $\eta = 1$), and a missing observation has $\ell \equiv 1$.

These are the emission probabilities of the hidden Markov model whose hidden states follow the [parental-origin chain](parental-origin-markov-chain-for-autotetraploid-gametes.md); offspring are conditionally independent given the phased parental genotypes.

## Depends on

- [Parental-origin Markov chain for autotetraploid gametes](parental-origin-markov-chain-for-autotetraploid-gametes.md)

## Expansion

Part 3 is part 2 with the binomial replaced by an arbitrary likelihood: summing $\mathbb P(y \mid d')$ against $\mathbb P(d' \mid d, \varepsilon)$ gives $(1-\varepsilon)\mathbb P(y \mid d)$ from $d' = d$ plus $\varepsilon/K$ times the sum over the other $K$ dosages, which is $\eta - \mathbb P(y \mid d)$. In the binomial, $d'/K$ is the fraction of allele-2 copies, and a read shows allele 1 if it samples an allele-1 copy correctly or an allele-2 copy with a sequencing error.

## Sources

- C. Zheng, R. R. Amadeu, P. R. Muñoz and J. B. Endelman, *Haplotype reconstruction in connected tetraploid F1 populations*, Genetics 219 (2021), iyab106, <https://doi.org/10.1093/genetics/iyab106>, PMCID PMC8633103 (PolyOrigin model: genotype model, equations (1)–(5)).
