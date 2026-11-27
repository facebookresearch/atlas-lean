# Poisson point process with finite intensity

Let $\mu$ be a finite measure on a measurable space $E$. The law of the Poisson point process with
intensity $\mu$ is the measure

$$\Pi_\mu = \sum_{n \ge 0} \frac{e^{-\mu(E)}}{n!}\, (\mu^{\otimes n}) \circ C_n^{-1}$$

on the space of measures on $E$, where $C_n(x_0, \dots, x_{n-1}) = \sum_{i < n} \delta_{x_i}$ is
the [counting measure](counting-measure.md). It is a probability measure (the [Poisson weights sum
to one](tsum-coeff-mul-pow.md)): this is the mixed binomial construction.

## Sources

- G. Last and M. Penrose, *Lectures on the Poisson Process*, IMS Textbooks, Cambridge University
  Press, 2017, Proposition 3.5.
