# Differentially private selection of a statistic generalizes in expectation

Let $M$ be an $(\varepsilon,\delta)$-differentially private algorithm that, given $S = (z_1, \dots, z_n) \sim D^n$, outputs a function $q : \mathcal{Z} \to [0,1]$. Then

$$
\Big| \mathbb{E}_{S, M}\Big[\frac1n\sum_{i=1}^n q_S(z_i)\Big] - \mathbb{E}_{S, M}\big[\mathbb{E}_{z \sim D}[q_S(z)]\big] \Big| \le e^{\varepsilon} - 1 + \delta,
$$

where $q_S = M(S)$: the empirical value of a privately selected statistic is an unbiased estimate of its population value up to $e^\varepsilon - 1 + \delta$.

## Proof sketch

Let $S^{(i)}$ replace $z_i$ by a fresh $z_i' \sim D$. Then $(S^{(i)}, z_i)$ has the same law as $(S, z_i')$, so $\mathbb{E}[q_{S^{(i)}}(z_i)] = \mathbb{E}[q_S(z_i')] = \mathbb{E}[\mathbb{E}_D q_S]$. Since $S$ and $S^{(i)}$ are neighbours and $q(z_i) \in [0,1]$, privacy gives $\mathbb{E}[q_S(z_i)] \le e^{\varepsilon}\mathbb{E}[q_{S^{(i)}}(z_i)] + \delta$ and the symmetric inequality; averaging over $i$ gives the claim.

## Depends on

- [Differential privacy](../../differential-privacy/differentially-private.md)

## Sources

- C. Dwork, V. Feldman, M. Hardt, T. Pitassi, O. Reingold, A. Roth, "Preserving Statistical Validity in Adaptive Data Analysis", STOC (2015), arXiv:1411.2664.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513.
