# Nonadaptive random-order prophet inequality: $1 - 1/e$ is tight

When independent (not necessarily identical) values arrive in uniformly random order and the gambler must fix one threshold per variable in advance (nonadaptive), there is a threshold assignment achieving $\mathbb{E}[X_\tau] \ge (1 - 1/e)\,\mathbb{E}[\max_i X_i]$ for every instance, and no nonadaptive rule achieves a better constant on all instances.

## Proof sketch

Set thresholds so that each variable is accepted with probability equal to its probability of being the maximum, scaled through a time-dependent factor; under random arrival this mimics a Poisson acceptance process whose success probability is $1 - 1/e$. For optimality, i.i.d. instances with many small atoms force any nonadaptive rule to lose the $1/e$ fraction.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Proof depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- José Correa, Patricio Foncea, Ruben Hoeksma, Tim Oosterwijk, Tjark Vredeveld, "Posted Price Mechanisms and Optimal Threshold Strategies for Random Arrivals", Mathematics of Operations Research 46(4) (2021); EC (2017).
