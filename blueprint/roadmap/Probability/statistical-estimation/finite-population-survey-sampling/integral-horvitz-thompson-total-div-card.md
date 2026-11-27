# Unbiasedness of the Horvitz–Thompson mean

Let $U$ be a finite population and let $p$ be a sampling design on $U$: a probability mass function on the finite subsets $s \subseteq U$ (the samples). Let $N = |U|$. Write $\pi_i = \sum_{s \ni i} p(s)$ for the inclusion probability of unit $i$ and, for real values $y : U \to \mathbb{R}$, $\hat Y(s) = \sum_{i \in s} y_i / \pi_i$ for the Horvitz–Thompson total at the sample $s$. Expectations $\mathbb{E}_p$ are taken under the probability measure of $p$ on the samples, for any $\sigma$-algebra on the samples in which every single sample is measurable. If $\pi_i > 0$ for all $i \in U$, then $\hat Y / N$ is unbiased for the population mean:

$$\mathbb{E}_p\Big[\frac{\hat Y}{N}\Big] = \frac{1}{N} \sum_{i \in U} y_i.$$

With the convention $x / 0 = 0$ the identity also holds for the empty population, where both sides are $0$.

## Sources

- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47(260) (1952), 663–685.
