# Privacy of randomized response

In *randomized response* the respondent flips a fair coin; on tails it answers truthfully, and on heads it flips a second fair coin and answers yes on heads and no on tails. The answer agrees with the truth with probability $3/4$. For a single respondent whose bit may change arbitrarily, the mechanism is $(\ln 3, 0)$-differentially private, and $\ln 3$ is optimal: it is $(\varepsilon, 0)$-private exactly when $\varepsilon \ge \ln 3$. For every order $\alpha > 1$ it is $(\alpha, \varepsilon_\alpha)$-Rényi differentially private with

$$
\varepsilon_\alpha = \frac{1}{\alpha - 1}\log\Bigl(\tfrac34\, 3^{\alpha-1} + \tfrac14\, 3^{1-\alpha}\Bigr),
$$

the specialization to $p = 3/4$ of the Rényi divergence $\frac{1}{\alpha-1}\log\bigl(p^\alpha(1-p)^{1-\alpha} + (1-p)^\alpha p^{1-\alpha}\bigr)$ of binary randomized response with truthful probability $p$.

## Proof sketch

The $(\ln 3, 0)$ bound is the case $p = 3/4$ of the privacy of randomized response with truthful probability $p \in (1/2, 1)$, whose budget is $\ln(p/(1-p))$: the likelihood ratio of the outputs for the two inputs is $(3/4)/(1/4) = 3$ or its inverse, which also shows that no smaller $\varepsilon$ works. The Rényi divergence of two Bernoulli laws is a two-term sum.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Rényi divergence and Rényi differential privacy](../renyi-differential-privacy/renyi-differential-privacy.md)

## Proof depends on

- [Randomized response is differentially private](is-dp-rr-mech.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
- Ilya Mironov, "Rényi Differential Privacy", 2017 IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
