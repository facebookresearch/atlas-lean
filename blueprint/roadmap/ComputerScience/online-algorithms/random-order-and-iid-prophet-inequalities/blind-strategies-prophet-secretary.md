# Blind strategies beat $1 - 1/e$ for prophet secretary

For independent nonnegative values in uniformly random order, there is a *blind* strategy that guarantees $\mathbb{E}[X_\tau] \ge 0.669\, \mathbb{E}[\max_i X_i]$ on every instance, improving the $1 - 1/e \approx 0.632$ guarantee. A blind strategy is a single nonincreasing function $\alpha : [0, 1] \to [0, 1]$, independent of the instance: for continuous distributions, the gambler draws independent uniform times $u_1, \dots, u_n \in [0, 1]$, sets the threshold $\tau_i$ for the $i$-th arrival so that $\Pr[\max_j X_j \le \tau_i] = \alpha(u_{[i]})$, where $u_{[i]}$ is the $i$-th order statistic, and stops at the first arrival exceeding its threshold. No blind strategy guarantees more than $0.675$.

## Proof sketch

Correa, Saona and Ziliotto bound the distribution of the gambler's stopping time for a given blind strategy uniformly over instances, using an argument inspired by Schur-convex functions, which yields a lower bound on the ratio that depends only on $\alpha$; optimizing this bound over $\alpha$ gives $0.669$. The upper bound $0.675$ comes from two instances on which no single $\alpha$ performs well. Discontinuous distributions are handled by randomized tie-breaking.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- José Correa, Raimundo Saona, Bruno Ziliotto, "Prophet Secretary Through Blind Strategies", Mathematical Programming 190 (2021); SODA (2019), arXiv:1807.07483, Section 1.2, Theorems 1.1 and 1.2.
