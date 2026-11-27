# Ewens distribution of latent mutations of a rare variant

Consider one locus with $K$ alleles under the neutral Wright–Fisher diffusion with parent-independent mutation: each lineage mutates at rate $\theta/2$ and a mutation produces allele $i$ with probability $\pi_i$, $\sum_i \pi_i = 1$. At stationarity, an ordered sample of size $n$ has allele counts $(n_1, \dots, n_K)$, $\sum_i n_i = n$, with probability

$$p_o(n_1, \dots, n_K) = \frac{1}{\theta^{(n)}}\prod_{i=1}^K (\theta\pi_i)^{(n_i)},$$

where $x^{(m)} = x(x+1)\cdots(x+m-1)$ is the rising factorial (the unordered probability multiplies by the multinomial coefficient). For each allele $i$ let $k_i \in \{1, \dots, n_i\}$ be the number of *latent mutations*: the most recent mutations to type $i$ that gave rise to the $n_i$ sampled copies. Then, conditional on the counts,

$$P(k_1, \dots, k_K \mid n_1, \dots, n_K) = \prod_{i=1}^K \frac{|S_{n_i}(k_i)|\,(\theta\pi_i)^{k_i}}{(\theta\pi_i)^{(n_i)}},$$

where $|S_m(k)|$ is the unsigned Stirling number of the first kind. The latent mutation counts are independent across alleles, and $k_i$ has the law of the number of distinct alleles in an Ewens sample of size $n_i$ with parameter $\theta\pi_i$; equivalently $k_i$ is a sum of independent Bernoulli variables with success probabilities $\theta\pi_i/(\theta\pi_i + j - 1)$, $j = 1, \dots, n_i$.

**Rare variants.** If allele $K$ is common and alleles $1, \dots, K-1$ appear in fixed small counts while $n_K \to \infty$, the same law holds for the *nonempty* latent mutations (mutations from the common background), because "empty" mutations to one's own type and mutations with rare-variant ancestors become negligible.

## Depends on

- [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)
- [The Dirichlet law is stationary for parent-independent mutation](../../../population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)
- [Law of the number of alleles](../../../detecting-selection/ewens-watterson-test/num-alleles-prob-eq.md)
- [Bernoulli representation and central limit theorem for Ewens block counts](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/asymptotics-of-k-n-mean-theta-log-n-and-clt.md)

## Proof depends on

- [Coalescent with killing](../../../population-genetics/allele-counts-and-the-coalescent-with-killing/killing-coalescent.md)
- [Probability that the next event at a level is a mutation](../../../population-genetics/allele-counts-and-the-coalescent-with-killing/measure-real-mutation-first.md)

## Expansion

Expanding the rising factorial, $(\theta\pi_i)^{(n_i)} = \sum_{k=1}^{n_i}|S_{n_i}(k)|(\theta\pi_i)^k$, suggests the joint law. To prove it, run the ancestral process conditioned on the sample's types (Griffiths–Tavaré). The total event rate is $n(\theta + n - 1)/2$; a type-$i$ lineage is involved with probability $n_i/n$, and the event is then a mutation with probability $\theta\pi_i/(\theta\pi_i + n_i - 1)$ or a coalescence of two type-$i$ lineages with probability $(n_i - 1)/(\theta\pi_i + n_i - 1)$, both obtained from ratios of $p_o$. Either way $n_i$ drops by one, and lineages are followed back only to their first mutation. The sequence of mutation-or-coalescence choices within type $i$ depends only on $n_i$ and $\theta\pi_i$, so the counts are independent sums of Bernoulli variables, which is the Ewens allele-number law (Eqs. (10)–(14) and (16)–(17) of the source). For rare variants, events on common-allele lineages occur at rate about $n_K^2/2$, empty mutations at rate $O(n_K)$ and the rare-allele events of interest at $O(n_K)$ with probabilities $\frac{n_i}{n_K}\cdot\frac{\theta\pi_i}{\theta\pi_i + n_i - 1}$ and $\frac{n_i}{n_K}\cdot\frac{n_i - 1}{\theta\pi_i + n_i - 1}$; the rare-allele ancestry is resolved in a time that tends to $0$ as $n_K \to \infty$.

## Sources

- J. Wakeley, W. Fan, E. Koch, S. Sunyaev, "Recurrent mutation in the ancestry of a rare variant", Genetics (2023), <https://doi.org/10.1093/genetics/iyad049> (PMC10324944).
