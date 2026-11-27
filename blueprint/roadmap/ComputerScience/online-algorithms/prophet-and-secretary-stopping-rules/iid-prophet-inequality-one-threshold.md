# I.i.d. prophet inequality with one randomized threshold: 1 - (1 - 1/n)^n

Let $X_1, \dots, X_n$ be i.i.d. nonnegative random variables with law $\mu$ (countable support), $n \ge 1$. There exist a threshold $\tau \ge 0$ and a tie-breaking probability such that the rule "accept the first $X_i > \tau$, or $X_i = \tau$ when an independent coin with that probability shows heads" accepts each value with probability exactly $1/n$ (the quantile rule with $q_i = 1/n$ at every step). Writing $R = \mathbb{E}[X_1;\, X_1 \text{ accepted}]$ for the expected reward collected at a step the rule reaches, one has $\mathbb{E}[\max_i X_i] \le nR$, and the rule collects

$$
\mathbb{E}[\text{reward}] = \sum_{i=0}^{n-1} \bigl(1 - \tfrac1n\bigr)^i R = \Bigl(1 - \bigl(1 - \tfrac1n\bigr)^n\Bigr)\, nR \ge \Bigl(1 - \bigl(1 - \tfrac1n\bigr)^n\Bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr] \ge \bigl(1 - \tfrac1e\bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr].
$$

Randomized tie-breaking is necessary for the constant with a single time-invariant threshold.

## Proof sketch

The prophet's value is at most $\tau + n\mathbb{E}[(X-\tau)^+] \le nR$, because the rule accepts every value above $\tau$, only values at least $\tau$, and in total probability exactly $1/n$. The gambler reaches step $i$ with probability $(1-1/n)^{i-1}$ and collects $R$ there, and the geometric sum equals $n(1-(1-1/n)^n)$; finally $(1 - 1/n)^n \le 1/e$. For continuous distributions this is the quantile computation of Correa, Foncea, Hoeksma, Oosterwijk and Vredeveld (2018 survey, Section 5, footnote 3); with atoms the coin at $\tau$ realizes the same quantile, as the survey notes for single thresholds (Section 4). On the instance in the proof of Theorem 21 of Ehsani, Hajiaghayi, Kesselheim and Singla, (each value is $n/(e-1)$ with probability $1/n^2$ and $(e-2)/(e-1)$ otherwise, so $\mathbb{E}[\max_i X_i] = 1 - O(1/n)$), a deterministic threshold either accepts the first value, collecting $(e-2)/(e-1) + O(1/n)$, or accepts only the value $n/(e-1)$, collecting $1/(e-1) + O(1/n)$; both are below $1 - 1/e$ for large $n$.

The optimal stopping rule, computed by backward induction, collects at least as much as this rule: a randomized rule is a mixture of deterministic ones, and none of them beats the optimal rule.

## Depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Proof depends on

- [Samuel-Cahn's median-threshold prophet inequality and optimality of 1/2](samuel-cahn-median-prophet-inequality.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk and Tjark Vredeveld, "Recent Developments in Prophet Inequalities", ACM SIGecom Exchanges 17(1), 2018, pp. 61-70, Section 4 (randomized tie-breaking for a single threshold) and Section 5, footnote 3 (the quantile rule $q_i = 1/n$).
- Soheil Ehsani, MohammadTaghi Hajiaghayi, Thomas Kesselheim and Sahil Singla, "Prophet Secretary for Combinatorial Auctions and Matroids", Proceedings of the 29th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2018, Section 5 (Theorem 19 and the proof of Theorem 21).
- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk and Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research, 2021.
