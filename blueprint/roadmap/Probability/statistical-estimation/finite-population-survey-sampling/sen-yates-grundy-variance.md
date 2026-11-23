# Yates–Grundy variance form

Let $U$ be a finite population and let $p$ be a sampling design on $U$: a probability mass function on the finite subsets $s \subseteq U$ (the samples). Write $\pi_i = \sum_{s \ni i} p(s)$ and $\pi_{ij} = \sum_{s \ni i,\, j} p(s)$ for the first- and second-order inclusion probabilities, and let $y : U \to \mathbb{R}$. The Yates–Grundy (Sen–Yates–Grundy) variance form is

$$V_{\mathrm{YG}} = \tfrac12 \sum_{i \in U} \sum_{j \in U,\, j \neq i} (\pi_i \pi_j - \pi_{ij}) \Big(\frac{y_i}{\pi_i} - \frac{y_j}{\pi_j}\Big)^2,$$

with the convention $y_i / 0 = 0$. For a design of fixed sample size with positive inclusion probabilities it is the variance of the Horvitz–Thompson total; for other designs it need not be.

## Sources

- Shalabh, *Sampling Theory*, Chapter 7 "Varying Probability Sampling", lecture notes, Department of Mathematics and Statistics, IIT Kanpur.
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47(260) (1952), 663–685.
- F. Yates and P. M. Grundy, "Selection without replacement from within strata with probability proportional to size", *Journal of the Royal Statistical Society, Series B* 15(2) (1953).
- C.-E. Särndal, B. Swensson and J. Wretman, *Model Assisted Survey Sampling*, Springer (1992), Chapter 2.
