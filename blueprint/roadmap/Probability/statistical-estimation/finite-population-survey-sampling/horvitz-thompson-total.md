# Horvitz–Thompson estimator of a population total

Let $U$ be a finite population and let $p$ be a sampling design on $U$: a probability mass function on the finite subsets $s \subseteq U$ (the samples). Let $\pi_i$ be the inclusion probability of unit $i$ and let $y : U \to \mathbb{R}$. The Horvitz–Thompson total at the sample $s$ weights each sampled value by the reciprocal of its inclusion probability:

$$\hat Y(s) = \sum_{i \in s} \frac{y_i}{\pi_i},$$

with the convention $y_i / 0 = 0$ for a unit of inclusion probability zero.

## Sources

- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47(260) (1952), 663–685.
