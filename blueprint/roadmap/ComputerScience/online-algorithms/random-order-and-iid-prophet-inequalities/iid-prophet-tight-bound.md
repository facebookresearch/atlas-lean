# Tight $0.745$ prophet inequality for i.i.d. values

For every $n$ and all i.i.d. nonnegative $X_1, \dots, X_n$, there are thresholds $\tau_1, \dots, \tau_n$ (those of the optimal threshold rule; the analysis goes through a quantile threshold rule with randomized tie-breaking at atoms of the distribution) such that the rule stopping at the first $i$ with $X_i \ge \tau_i$ satisfies $\mathbb{E}[X_\tau] \ge \beta\, \mathbb{E}[\max_i X_i]$, where $\beta \approx 0.745$ is the Hill–Kertz constant. By the Hill–Kertz upper bound, $\beta$ is the optimal i.i.d. prophet ratio, resolving a problem posed by Hill and Kertz in 1982; the same tight bound holds for adaptive posted-price mechanisms with i.i.d. buyers.

## Proof sketch

Correa, Foncea, Hoeksma, Oosterwijk and Vredeveld write the gambler's reward and the prophet's expected maximum in terms of the acceptance probabilities $q_1, \dots, q_n$, and choose the $q_i$ so that a sequence of per-step ratios $\rho_1 = \dots = \rho_n$ coincide, which reduces the guarantee to a condition on a recursively defined sequence. For every $n$ they dominate this sequence by the solution of $y' = y(\ln y - 1) - (\frac1\beta - 1)$ with $y(0) = 1$; requiring $y(1) = 0$ is exactly the integral equation defining the Hill–Kertz constant, which gives the guarantee for every $n$. The randomized rule is then dominated by the optimal deterministic threshold rule computed by dynamic programming.

## Depends on

- [Quantile threshold rules for i.i.d. prophets](quantile-threshold-rules.md)
- [The Hill–Kertz constant $\beta \approx 0.745$](hill-kertz-constant.md)

## Proof depends on

- [No stopping rule beats $\beta$ for i.i.d. values](iid-prophet-upper-bound.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017), Theorem 2 and Section 4.
