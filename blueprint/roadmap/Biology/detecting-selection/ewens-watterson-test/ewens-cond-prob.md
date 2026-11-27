# Ewens conditional probability given the number of alleles

For a real $\theta$ and a partition $\pi$ of $n$ with $K(\pi)$ parts, the conditional weight of $\pi$ given the number of alleles is

$$P_\theta(\pi \mid K = K(\pi)) = \frac{P_\theta(\pi)}{P_\theta(K = K(\pi))},$$

where $P_\theta(\pi)$ is the Ewens sampling formula and $P_\theta(K = k)$ the [probability of $k$ alleles](num-alleles-prob.md), with the convention $x/0 = 0$. For $\theta > 0$ it is the conditional probability of the allelic partition $\pi$ given that the sample has $K(\pi)$ alleles.
