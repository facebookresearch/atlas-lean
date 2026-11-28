# I.i.d. prophet inequality with one randomized threshold: 1 - 1/e

Let $X_1, \dots, X_n$ be i.i.d. nonnegative random variables with law $\mu$, $n \ge 1$, observed one at a time, and consider single-threshold rules with randomized tie-breaking: for a threshold $\tau \ge 0$ and a probability $p \in [0, 1]$, accept the first $X_i$ with $X_i > \tau$, or with $X_i = \tau$ when an independent coin with probability $p$ shows heads. There exist $\tau$ and $p$ for which the rule accepts no value with probability exactly $1/e$ (for a continuous $\mu$, $\Pr[\max_i X_i \le \tau] = 1/e$), and this rule collects

$$
\mathbb{E}[\text{reward}] \ge \Bigl(1 - \frac1e\Bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr].
$$


## Proof sketch

Ehsani, Hajiaghayi, Kesselheim and Singla prove Theorem 19 for independent values in uniformly random order (prophet secretary); for i.i.d. values the order does not matter. Their proof takes a continuous CDF and finite mean without loss of generality, the continuous approximation corresponding to randomized tie-breaking at atoms (their footnote 4). If $\mathbb{E}[X_1] = \infty$, both sides are infinite, since the first step accepts every value above $\tau$ with positive probability. As $\tau$ and $p$ vary, the probability $\Pr[X_1 < \tau] + (1 - p)\Pr[X_1 = \tau]$ of not accepting at one step takes every value in $[0, 1)$, so it can be set to $e^{-1/n}$. The rule then accepts some value with probability $1 - 1/e$, which yields $(1 - 1/e)\tau$, and reaches step $j$ with probability $e^{-(j-1)/n}$, where it collects $\mathbb{E}[(X_1 - \tau)^+]$ above the threshold (a value equal to $\tau$ adds nothing above it). Since $\sum_{j=1}^{n} e^{-(j-1)/n} \ge n\int_0^1 e^{-x}\,dx = n(1 - 1/e)$ and $\mathbb{E}[(\max_i X_i - \tau)^+] \le n\,\mathbb{E}[(X_1 - \tau)^+]$, the reward is at least $(1 - 1/e)\bigl(\tau + \mathbb{E}[(\max_i X_i - \tau)^+]\bigr) \ge (1 - 1/e)\,\mathbb{E}[\max_i X_i]$.

Randomized tie-breaking is necessary for the constant $1 - 1/e$ with a single time-invariant threshold as $n \to \infty$: on the instance in the proof of Theorem 21 of Ehsani, Hajiaghayi, Kesselheim and Singla (each value is $n/(e-1)$ with probability $1/n^2$ and $(e-2)/(e-1)$ otherwise, so $\mathbb{E}[\max_i X_i] = 1 - O(1/n)$), a deterministic threshold either accepts the first value, collecting $(e-2)/(e-1) + O(1/n)$, or accepts only the value $n/(e-1)$, collecting $1/(e-1) + O(1/n)$, or accepts nothing; all are below $1 - 1/e$ for large $n$.

The quantile rule with $q_i = 1/n$ at every step gives the sharper constant $1 - (1 - 1/n)^n$. Choose $\tau$ and $p$ so that the rule accepts each value with probability exactly $1/n$, and write $R = \mathbb{E}[X_1;\, X_1 \text{ accepted}]$ for the expected reward collected at a step the rule reaches. The prophet's value is at most $\tau + n\mathbb{E}[(X_1-\tau)^+] \le nR$, because the rule accepts every value above $\tau$, only values at least $\tau$, and in total probability exactly $1/n$. The gambler reaches step $i$ with probability $(1-1/n)^{i-1}$ and collects $R$ there, so

$$
\mathbb{E}[\text{reward}] = \sum_{i=0}^{n-1} \bigl(1 - \tfrac1n\bigr)^i R = \Bigl(1 - \bigl(1 - \tfrac1n\bigr)^n\Bigr)\, nR \ge \Bigl(1 - \bigl(1 - \tfrac1n\bigr)^n\Bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr] \ge \bigl(1 - \tfrac1e\bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr],
$$

using $(1 - 1/n)^n \le 1/e$. For continuous distributions this is the quantile computation of Correa, Foncea, Hoeksma, Oosterwijk and Vredeveld (2018 survey, Section 5, footnote 3); with atoms the coin at $\tau$ realizes the same quantile, as the survey notes for single thresholds (Section 4).

The optimal stopping rule, computed by backward induction, collects at least as much as these rules: a randomized rule is a mixture of deterministic ones, and none of them beats the optimal rule.


## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk and Tjark Vredeveld, "Recent Developments in Prophet Inequalities", ACM SIGecom Exchanges 17(1), 2018, pp. 61-70, Section 4 (randomized tie-breaking for a single threshold) and Section 5, footnote 3 (the quantile rule $q_i = 1/n$).
- Soheil Ehsani, MohammadTaghi Hajiaghayi, Thomas Kesselheim and Sahil Singla, "Prophet Secretary for Combinatorial Auctions and Matroids", Proceedings of the 29th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2018, Section 5 (Theorem 19 with footnote 4, and the proof of Theorem 21).
- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk and Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research, 2021.
