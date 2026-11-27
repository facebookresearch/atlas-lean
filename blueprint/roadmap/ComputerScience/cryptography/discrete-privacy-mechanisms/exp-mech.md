# Exponential mechanism as a probability mass function

Let $R$ be a finite nonempty type, $u : D \times R \to \mathbb{R}$ a utility function and $\varepsilon, \Delta \in \mathbb{R}$. On a database $d$, the exponential mechanism is the probability mass function on $R$ with

$$
\Pr[r] = \frac{\exp\big(\varepsilon\, u(d, r) / (2\Delta)\big)}{\sum_{r' \in R} \exp\big(\varepsilon\, u(d, r') / (2\Delta)\big)},
$$

the [output probabilities](../laplace-and-exponential-mechanisms/exp-mech-prob.md) of the exponential mechanism. With $\Delta = 0$ every exponent is $0$ and the distribution is uniform.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Definition 3.4.
