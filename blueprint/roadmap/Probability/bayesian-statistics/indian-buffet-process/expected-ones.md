# Closed-form expected number of ones of the finite feature model

For $\alpha \in \mathbb{R}$ and $N, K \in \mathbb{N}$, the expression

$$NK \cdot \frac{\alpha/K}{\alpha/K + 1}$$

(with $\alpha/K = 0$ when $K = 0$, and the fraction read as $0$ when $\alpha/K + 1 = 0$). Griffiths and Ghahramani (2011, Section 4.1: $K$ times the column expectation of Equation 11) give it as the expected number of ones $\mathbb{E}[\sum_{ik} z_{ik}]$ in the $N \times K$ matrix of the finite feature model with $\pi_k \sim \mathrm{Beta}(\alpha/K, 1)$: each entry is one with probability $\mathbb{E}[\pi_k] = (\alpha/K)/(\alpha/K + 1)$, the mean $r/(r + s)$ of $\mathrm{Beta}(r, s)$. The definition is that closed form; the entry probability itself is computed from the beta–Bernoulli model in [Entry probability of the finite feature model](entry-prob.md).

## Informally uses

- [Prior predictive probability of a success](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/binomial-kernel-one-comp-beta-measure.md): a Bernoulli trial whose success probability is $\mathrm{Beta}(a, b)$ succeeds with probability $a/(a + b)$.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 4.1, Equation 11 and the sentence after it.
