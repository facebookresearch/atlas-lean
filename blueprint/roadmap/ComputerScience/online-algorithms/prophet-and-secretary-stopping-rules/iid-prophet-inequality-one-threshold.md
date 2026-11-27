# I.i.d. prophet inequality with one randomized threshold: 1 - (1 - 1/n)^n

Let $X_1, \dots, X_n$ be i.i.d. nonnegative random variables with law $\mu$ (countable support), $n \ge 1$. There exist a threshold $\tau \ge 0$ and a tie-breaking probability such that the rule "accept the first $X_i > \tau$, or $X_i = \tau$ when an independent coin with that probability shows heads" accepts each value with probability exactly $1/n$, and this rule collects

$$
\mathbb{E}[\text{reward}] \ge \Bigl(1 - \bigl(1 - \tfrac1n\bigr)^n\Bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr] \ge \bigl(1 - \tfrac1e\bigr)\,\mathbb{E}\bigl[\max_i X_i\bigr].
$$

The optimal (deterministic, backward-induction) stopping rule does at least as well. Randomized tie-breaking is necessary for the constant with a single time-invariant threshold.

## Proof sketch

Let $A = \mathbb{E}[X; \text{accept}]$. The prophet's value is at most $\tau + n\mathbb{E}[(X-\tau)^+] \le nA$, because the rule accepts every value above $\tau$ and only values at least $\tau$. The gambler reaches step $i$ with probability $(1-1/n)^{i-1}$ and collects $A$ there, and the geometric sum equals $n(1-(1-1/n)^n)$. A randomized rule is a mixture of deterministic ones, so the optimal rule is at least as good.

## Depends on

- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Proof depends on

- [Samuel-Cahn's median-threshold prophet inequality and optimality of 1/2](samuel-cahn-median-prophet-inequality.md)

## Sources

- Soheil Ehsani, MohammadTaghi Hajiaghayi, Thomas Kesselheim and Sahil Singla, "Prophet Secretary for Combinatorial Auctions and Matroids", Proceedings of the 29th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2018.
- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk and Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research, 2021.
