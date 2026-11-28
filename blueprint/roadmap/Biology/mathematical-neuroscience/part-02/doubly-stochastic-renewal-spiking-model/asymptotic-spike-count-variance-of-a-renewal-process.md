# Asymptotic spike-count variance of a renewal process

Let spikes form a stationary (equilibrium) renewal process whose inter-spike intervals are i.i.d. with a probability density $f$, mean $\mu$, variance $\sigma^2$ and third central moment $\mu_3$, and let $N_T$ be the number of spikes in a window of length $T$. Then, as $T \to \infty$,

$$\mathbb{E}(N_T) = \frac{T}{\mu}, \qquad \operatorname{Var}(N_T) = \frac{\sigma^2}{\mu^3}\,T + \left(\frac{\sigma^4}{2\mu^4} + \frac{1}{6} - \frac{\mu_3}{3\mu^3}\right) + O(T^{-1})$$

(Aghamohammadi, Chandrasekaran and Engel 2025, Eqs. 9–10, Theorem 1 of Supplementary Note 1.1; a classical renewal-theory expansion).

In particular the Fano factor $\operatorname{Var}(N_T)/\mathbb{E}(N_T)$ tends to the squared coefficient of variation $\sigma^2/\mu^2$ of the intervals, and the constant term is a finite-window correction that depends on the interval skewness.

## Expansion

The leading term follows from the renewal central limit theorem, $N_T \approx \mathcal N(T/\mu, \sigma^2 T/\mu^3)$. The constant term comes from the second-order expansion of the renewal function and its variance analogue, obtained from the Laplace transform of the interval density near the origin, where the first three moments enter. For a Poisson process ($\sigma^2 = \mu^2$, $\mu_3 = 2\mu^3$) the constant vanishes and $\operatorname{Var}(N_T) = T/\mu$ exactly.

## Sources

- C. Aghamohammadi, C. Chandrasekaran and T. A. Engel, *A doubly stochastic renewal framework for partitioning spiking variability*, Nature Communications 16 (2025), 8656, Eqs. (9)–(10). <https://doi.org/10.1038/s41467-025-63821-4> (PMCID: PMC12484930)
