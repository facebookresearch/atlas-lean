# Nonadaptive random-order prophet inequality: $1 - 1/e$ is tight

When independent (not necessarily identical) nonnegative values arrive in uniformly random order and the gambler must fix one threshold per variable in advance (nonadaptive), there is a threshold assignment achieving $\mathbb{E}[X_\tau] \ge (1 - 1/e)\,\mathbb{E}[\max_i X_i]$ for every instance and every $n$, and no nonadaptive rule achieves a better constant on all instances, even for i.i.d. values.

## Proof sketch

The core is a Bernoulli selection lemma: for independent Bernoulli variables $Y_i$ with $\Pr[Y_i = 1] = q_i$ and prizes $b_i$, some subset $S$ has $\mathbb{E}\big[\sum_{i \in S} b_i Y_i / \sum_{i \in S} Y_i\big] \ge (1 - 1/e)\,\mathbb{E}[\max_i b_i Y_i]$. Under random order every variable above its threshold is equally likely to be the first one, so the gambler's reward has exactly this averaged form. For continuous distributions, Correa, Foncea, Hoeksma, Oosterwijk and Vredeveld take $q_i$ the probability that $X_i$ is the maximum, set $\tau_i$ with $\Pr[X_i > \tau_i] = q_i$ for $i$ in the subset $S$ given by the lemma (with prizes $b_i = \mathbb{E}[X_i \mid X_i > \tau_i]$) and $\tau_i = \infty$ otherwise, and use that $X_i$ conditioned on $X_i > \tau_i$ stochastically dominates $X_i$ conditioned on being the maximum; atoms are handled by randomized thresholds. For tightness, $n^2$ i.i.d. values equal to $n/(e-2)$ with probability $n^{-3}$, to $1$ with probability $1/n$ and to $0$ otherwise give a prophet value tending to $(e-1)/(e-2)$, while the best nonadaptive rule tends to $\big(\frac{1}{e-2} + 1\big)(1 - 1/e)$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017), Theorem 1, Lemma 1 and Section 3.1.
