# Annual loss from a Poisson occurrence model

Let the hazard occurrence rate be $r\ge0$ with units inverse years, and set the dimensionless expected one-year count
$\lambda=r\,(1\,\mathrm{year})$. Suppose that the event count $N$ in that year is Poisson with mean $\lambda$. Let losses
$L_1,L_2,\ldots$ be identically distributed, integrable real random variables, independent of each other and of $N$. The annual loss
$A=\sum_{i=1}^{N}L_i$ (zero for $N=0$) has $E[A] = \lambda\,E[L_1]$, and the probability of at least one event in the year is
$1 - e^{-\lambda} \le \lambda$. The occurrence rate $r$ is not a probability, and the mean count $\lambda$ may exceed one. For small $\lambda$, the one-year probability
of at least one modeled event is approximately $\lambda$. This is not the probability that aggregate loss exceeds an arbitrary
threshold; single-event risk is also a different quantity.

## Depends on

## Proof depends on

- [Wald's equation](../../martingales/wald-s-equations/wald-s-equation/wald-equation.md)

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd revised edition, American Mathematical Society, Section 5.1, the Poisson distribution, <https://math.dartmouth.edu/~prob/prob/prob.pdf>.
