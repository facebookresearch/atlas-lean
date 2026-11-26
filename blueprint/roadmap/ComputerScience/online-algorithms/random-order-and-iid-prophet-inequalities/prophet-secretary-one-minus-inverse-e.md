# Prophet secretary: adaptive thresholds achieve $1 - 1/e$

For independent nonnegative values arriving in uniformly random order, there is a stopping rule whose threshold at the time an arrival is seen depends only on the fraction of time elapsed, with $\mathbb{E}[X_\tau] \ge (1 - 1/e)\,\mathbb{E}[\max_i X_i]$ for every instance.

## Proof sketch

Esfandiari, Hajiaghayi, Liaghat and Monemizadeh use a decreasing sequence of thresholds $\tau_j$ set so that the probability that no value exceeds $\tau_j$ is $e^{-j/n}$ relative to the prophet's distribution; a charging argument splits the prophet's value into a threshold part and an excess part, and the random order lets both be bounded by integrals giving $1 - 1/e$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- Hossein Esfandiari, MohammadTaghi Hajiaghayi, Vahid Liaghat, Morteza Monemizadeh, "Prophet Secretary", SIAM Journal on Discrete Mathematics 31(3) (2017); ESA (2015).
