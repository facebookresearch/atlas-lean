# Unbiasedness of the Sen–Yates–Grundy variance estimator

Let $U$ be a finite population and let $p$ be a sampling design on $U$: a probability mass function on the finite subsets $s \subseteq U$ (the samples). Write $\pi_i = \sum_{s \ni i} p(s)$ and $\pi_{ij} = \sum_{s \ni i,\, j} p(s)$ for the first- and second-order inclusion probabilities, let $y : U \to \mathbb{R}$, let $\hat Y(s) = \sum_{i \in s} y_i / \pi_i$ be the Horvitz–Thompson total and $Y = \sum_{i \in U} y_i$ the population total, and let $\hat V_{\mathrm{SYG}}$ be the Sen–Yates–Grundy variance estimator. Expectations $\mathbb{E}_p$ are taken under the probability measure of $p$ on the samples, for any $\sigma$-algebra on the samples in which every single sample is measurable. Suppose $\pi_i > 0$ for every $i \in U$, $\pi_{ij} > 0$ for all distinct $i, j \in U$, and the design has fixed size $n$: every sample $s$ with $p(s) \neq 0$ has exactly $n$ elements. Then $\hat V_{\mathrm{SYG}}$ is unbiased for the mean squared error of the Horvitz–Thompson total:

$$\mathbb{E}_p\big[\hat V_{\mathrm{SYG}}\big] = \mathbb{E}_p\big[(\hat Y - Y)^2\big].$$

## Sources

- Shalabh, *Sampling Theory*, Chapter 7 "Varying Probability Sampling", lecture notes, Department of Mathematics and Statistics, IIT Kanpur.
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47(260) (1952), 663–685.
- F. Yates and P. M. Grundy, "Selection without replacement from within strata with probability proportional to size", *Journal of the Royal Statistical Society, Series B* 15(2) (1953).
- C.-E. Särndal, B. Swensson and J. Wretman, *Model Assisted Survey Sampling*, Springer (1992), Chapter 2.
