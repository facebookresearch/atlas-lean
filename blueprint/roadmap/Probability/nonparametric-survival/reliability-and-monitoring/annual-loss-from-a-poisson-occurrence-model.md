# Annual loss from a Poisson occurrence model

Let $r\ge0$ be the occurrence rate in inverse years, and let $\lambda=r\,(1\,\mathrm{year})$ be the dimensionless mean one-year count. Suppose that the one-year event count $N$ has the Poisson law with mean $\lambda$. Let $L_1,L_2,\ldots$ be identically distributed, integrable real losses, each independent of $N$. The losses need not be mutually independent.

The annual loss $A=\sum_{i=1}^{N} L_i$, interpreted as zero for $N=0$, is integrable, and

$$E[A]=\lambda E[L_1],\qquad P(N>0)=1-e^{-\lambda}\le\lambda.$$

For the expectation, apply Wald's equation with the same information $\sigma(N)$ at every step: $N$ is known in this filtration, and each loss is independent of it. The occurrence probability follows from the Poisson mass at zero, and the inequality follows from $e^{-\lambda}\ge1-\lambda$.

Neither $r$ nor $\lambda$ is a probability, and $\lambda$ may exceed one. The occurrence probability is not in general the probability that the aggregate loss exceeds a specified threshold.

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd revised edition, American Mathematical Society, §5.1, equation (5.2), <https://math.dartmouth.edu/~prob/prob/prob.pdf>: the Poisson count law. The annual-loss identity and occurrence bound are derived here.
