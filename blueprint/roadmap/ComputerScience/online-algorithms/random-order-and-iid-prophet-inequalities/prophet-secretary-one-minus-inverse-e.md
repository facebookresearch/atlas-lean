# Prophet secretary: step-dependent thresholds approach $1 - 1/e$

For independent nonnegative values $X_1, \dots, X_n$ arriving in uniformly random order, let $\mathrm{OPT} = \mathbb{E}[\max_i X_i]$ and define $\alpha_n = \frac{1}{n+1}$ and $\alpha_k = \frac{n\alpha_{k+1} + 1}{n+1}$ for $k < n$. The stopping rule that accepts the $k$-th arriving value if it is at least $\tau_k = \alpha_k\,\mathrm{OPT}$ satisfies

$$
\mathbb{E}[X_\tau] \ge \alpha_1\,\mathbb{E}[\max_i X_i], \qquad \alpha_1 = 1 - \left(\frac{n}{n+1}\right)^n,
$$

so its guarantee tends to $1 - 1/e$ as $n \to \infty$ (it is $5/9$ for $n = 2$). The thresholds are nonincreasing in the arrival step and depend on the distributions only through $\mathrm{OPT}$.

## Proof sketch

Esfandiari, Hajiaghayi, Liaghat and Monemizadeh split the gambler's reward according to the step $k$ at which a value between $\tau_{k+1}$ and $\tau_k$ is picked, and bound the expected value picked in such events in terms of the probability $\theta(k)$ of passing the first $k$ arrivals, using the random order to decouple the steps. Optimizing the threshold factors leads to the recursion for the $\alpha_k$, and unrolling it gives $1 - \alpha_1 = (n/(n+1))^n \to 1/e$.

## Depends on

- [Gambler-to-prophet ratios under different arrival models](prophet-ratio-by-arrival-model.md)

## Sources

- Hossein Esfandiari, MohammadTaghi Hajiaghayi, Vahid Liaghat, Morteza Monemizadeh, "Prophet Secretary", SIAM Journal on Discrete Mathematics 31(3) (2017); ESA (2015), arXiv:1507.01155, Theorem 1 and Section 6.
