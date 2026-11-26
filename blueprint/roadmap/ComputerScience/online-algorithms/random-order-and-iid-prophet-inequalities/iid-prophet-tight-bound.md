# Tight $0.745$ prophet inequality for i.i.d. values

For every $n$ and every i.i.d. instance with a continuous distribution, there is a quantile threshold rule $\tau$ with $\mathbb{E}[X_\tau] \ge \beta\, \mathbb{E}[\max_i X_i]$, where $\beta \approx 0.745$ is the Hill–Kertz constant. By the Hill–Kertz upper bound, $\beta$ is the optimal i.i.d. prophet ratio, resolving a problem posed by Hill and Kertz in 1982; the same tight bound holds for adaptive posted-price mechanisms with i.i.d. buyers.

## Proof sketch

Correa, Foncea, Hoeksma, Oosterwijk and Vredeveld choose the acceptance probabilities $p_i$ as values of the solution of a differential equation in the limit $n \to \infty$, so that the ratio between the gambler's expected reward and the prophet's expected maximum is the same for every distribution $F$; computing this common ratio yields exactly the integral equation that defines $\beta$. A discretization argument handles finite $n$.

## Depends on

- [Quantile threshold rules for i.i.d. prophets](quantile-threshold-rules.md)
- [The Hill–Kertz constant $\beta \approx 0.745$](hill-kertz-constant.md)

## Proof depends on

- [No stopping rule beats $\beta$ for i.i.d. values](iid-prophet-upper-bound.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017).
