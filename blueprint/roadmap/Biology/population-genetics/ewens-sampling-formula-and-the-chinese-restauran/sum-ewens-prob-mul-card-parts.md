# Expected number of alleles

For every real $\theta > 0$ and every natural number $n$, the expected number of parts of an integer partition of $n$ drawn from the [Ewens sampling formula](ewens-prob.md) is

$$\sum_{\pi} E_\theta(\pi)\, |\pi| = \sum_{i=0}^{n-1} \frac{\theta}{\theta + i}:$$

the expected number of alleles in a sample of $n$ genes. In terms of the
[allele-count configuration](../allele-counts-and-the-coalescent-with-killing/allele-count.md)
$a(\pi)$, with $a_j(\pi)$ the number of parts of $\pi$ equal to $j$, the number of parts is the
[sum of the allele counts](../allele-counts-and-the-coalescent-with-killing/sum-allele-count.md),
$|\pi| = \sum_{j=1}^n a_j(\pi)$, so the same mean reads
$\sum_\pi E_\theta(\pi) \sum_{j=1}^n a_j(\pi) = \sum_{i=0}^{n-1} \theta / (\theta + i)$.

## Sources

- W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theoret. Population Biol. 3 (1972), 87–112.
