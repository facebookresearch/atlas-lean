# Alternating-series bounds for the line-of-descent probabilities

Let $\theta > 0$ and $t > 0$. The [entrance probabilities](transition-probabilities-q-theta-n-t-of-the-non.md) $q^\theta_m(t)$ of the line-of-descent process are alternating series
$q^\theta_m(t) = \sum_{k \ge m} (-1)^{k-m} b_k(m)$ with $b_k(m) = a^\theta_{km} e^{-k(k+\theta-1)t/2}$ and
$a^\theta_{km} = (\theta + 2k - 1)\,\Gamma(\theta + m + k - 1)\,/\,\bigl(\Gamma(\theta + m)\, m!\,(k - m)!\bigr)$ (with $b_0(0) = 1$). Let

$$C_m = \inf\{ i \ge 0 : b_{m+i+1}(m) < b_{m+i}(m) \} .$$

Then $C_m < \infty$ for every $m$; the terms $b_k(m)$ decrease to $0$ for $k \ge m + C_m$; and $C_m = 0$ for every $m > D_0$, where

$$D_\varepsilon = \inf\Bigl\{ k \ge \Bigl(\frac1t - \frac{\theta + 1}{2}\Bigr) \vee 0 : (\theta + 2k + 1)\, e^{-(2k + \theta)t/2} < 1 - \varepsilon \Bigr\} .$$

Consequently, for every $K \ge m + C_m$ the partial sums $S_K = \sum_{k=m}^K (-1)^{k-m} b_k(m)$ bracket $q^\theta_m(t)$, lying above it when
$K - m$ is even and below it when $K - m$ is odd, and converge to it monotonically from each side. This makes exact
sampling from $(q^\theta_m(t))_m$ possible with finitely many terms.

## Depends on

- [Finite and entrance transition probabilities for the mutation line-count process](transition-probabilities-q-theta-n-t-of-the-non.md)

## Sources

- P. A. Jenkins and D. Spanò, "Exact simulation of the Wright–Fisher diffusion", Annals of Applied Probability 27 (2017), 1478–1509, <https://doi.org/10.1214/16-AAP1236>; preprint <https://arxiv.org/abs/1506.06998>, Section 2.2, equation (5) and Proposition 1 with equations (7)–(8).
