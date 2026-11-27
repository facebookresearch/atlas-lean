# Horvitz–Thompson estimator of the average indirect effect

In a Bernoulli design with probabilities $\pi_i \in (0, 1)$, suppose an interference graph $E_{ij} \in \{0, 1\}$ is known such that $Y_j(w_i = 0; w_{-i}) = Y_j(w_i = 1; w_{-i})$ whenever $E_{ij} = 0$ (this is vacuous if all $E_{ij} = 1$). The Horvitz–Thompson estimators are

$$\hat\tau_{\mathrm{ADE}}(\pi) = \frac{1}{n} \sum_{i=1}^{n} \Bigl(\frac{W_i Y_i}{\pi_i} - \frac{(1 - W_i) Y_i}{1 - \pi_i}\Bigr),$$

$$\hat\tau_{\mathrm{AIE}}(\pi) = \frac{1}{n} \sum_{i=1}^{n} \sum_{\{j \ne i \,:\, E_{ij} = 1\}} \Bigl(\frac{W_i Y_j}{\pi_i} - \frac{(1 - W_i) Y_j}{1 - \pi_i}\Bigr).$$

**Theorem.** $\mathbb{E}\{\hat\tau_{\mathrm{AIE}}(\pi)\} = \tau_{\mathrm{AIE}}(\pi)$, and likewise $\mathbb{E}\{\hat\tau_{\mathrm{ADE}}(\pi)\} = \tau_{\mathrm{ADE}}(\pi)$, for the [average direct and indirect effects](average-direct-and-indirect-effects-under-interference.md).

## Depends on

- [Average direct, indirect and overall effects under interference](average-direct-and-indirect-effects-under-interference.md)

## Expansion

$W_i Y_j = W_i Y_j(w_i = 1; W_{-i})$, and $W_i$ is independent of $W_{-i}$, so $\mathbb{E}\{W_i Y_j / \pi_i\} = \mathbb{E}\{Y_j(w_i = 1; W_{-i})\}$; similarly for the control term. Summing over pairs with $E_{ij} = 1$ recovers every nonzero term of $\tau_{\mathrm{AIE}}$, since pairs with $E_{ij} = 0$ contribute zero by assumption. Dropping the pairs with $E_{ij} = 0$ removes terms with mean zero, so a sparse interference graph *can* improve precision; it need not, since removing a single edge can also remove a cancellation between terms and increase the variance. The theorem asserts only unbiasedness.

## Sources

- Y. Hu, S. Li and S. Wager, *Average direct and indirect causal effects under interference*, Biometrika (2022). <https://doi.org/10.1093/biomet/asac008> Appendix A, Equations (A1)–(A3) and Theorem 2, with its proof.
