# Smoothed adversaries in online learning

Fix a base probability measure $\mu$ on the instance space $X$ and $\sigma \in (0,1]$. A distribution $D$ on $X$ is **$\sigma$-smooth** with respect to $\mu$ if $D(E) \le \mu(E)/\sigma$ for every measurable $E$, that is, $D$ has density at most $1/\sigma$ with respect to $\mu$. In **smoothed online learning** an adversary chooses at each round $t$ a $\sigma$-smooth distribution $D_t$ (adaptively, possibly depending on the history) and a labelling rule; nature draws $x_t \sim D_t$, the learner predicts $\hat y_t$, and then $y_t$ is revealed. Regret is measured against the best fixed hypothesis of a class $H$ on the realized sequence. For $\sigma = 1$ and $\mu$ fixed, the instances are i.i.d.; as $\sigma \to 0$ the model approaches the fully adversarial setting.

## Depends on

- [Online classification protocol, mistakes and regret](../online-classification-protocol-mistakes-and-regret.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129, Section 2 (with $\mu$ uniform).
- A. Block, Y. Dagan, N. Golowich, A. Rakhlin, "Smoothed Online Learning is as Easy as Statistical Learning", COLT (2022), arXiv:2202.04690.
