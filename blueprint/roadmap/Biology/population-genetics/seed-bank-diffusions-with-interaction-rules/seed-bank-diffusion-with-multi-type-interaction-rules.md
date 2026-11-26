# Seed-bank diffusion with multi-type interaction rules

**Setting.** A Wright-Fisher population of size $N$ has $K$ types. Each individual of generation $n+1$ samples a random number $m\ge1$ of *potential parents* (with law $Q_N$); each potential parent is drawn uniformly from the current generation with probability $r_N$, or otherwise from a past generation $n-j$, $j\ge1$, chosen geometrically with parameter $q_N$ (a seed bank of dormant individuals). Given the types $\mathbf j=(j_1,\dots,j_m)$ of the potential parents, the offspring type is assigned by a **coloring rule** $c^N_{\mathbf j}$, a probability vector on $[K]$ encoding the outcome of the interaction (for instance rock-paper-scissors: of two interacting types, the one that beats the other is passed on). Let $X^N(n)\in\Delta_K$ be the type frequencies and $Y^N(n)=q_N\sum_{j\ge1}(1-q_N)^{j-1}X^N(n-j)$ the geometrically weighted frequencies of the past (seed bank). The interaction drift is

$$\mu_i(x)=\lim_{N\to\infty}\rho_N^{-1}\Bigl(\sum_{m\ge1}Q_N(m)\sum_{\mathbf j\in[K]^m}\Bigl(\prod_{\ell=1}^m x_{j_\ell}\Bigr)c^N_{\mathbf j}(i)-x_i\Bigr),\qquad x\in\Delta_K,$$

for a time scale $\rho_N\to0$ (the strength of selection).

**Theorem 1 (scaling limit).** Assume that this limit $\mu$ exists, that $1/(N\rho_N)\to\sigma\in[0,\infty)$, that $(1-r_N)/\rho_N\to\alpha\ge0$ and $q_N/\rho_N\to\beta\ge0$, and that the mean number of potential parents is $O(\rho_N)$ away from one. Then $\bigl(X^N(\lfloor t/\rho_N\rfloor),Y^N(\lfloor t/\rho_N\rfloor)\bigr)$ converges weakly in the Skorokhod space $\mathbb D(\mathbb R_+,\Delta_K\times\Delta_K)$ to the unique strong solution of

$$dX_t=\mu(X_t)\,dt+\sqrt\sigma\,\zeta(X_t)\,dB_t+\alpha(Y_t-X_t)\,dt,\qquad dY_t=\beta(X_t-Y_t)\,dt,$$

where $B$ is a $K$-dimensional Brownian motion and $\zeta(x)$ is a lower-triangular square root of the Wright-Fisher covariance $\mathrm{diag}(x)-xx^{\mathsf T}$ (Proposition 1 gives existence and uniqueness).

## Expansion

Sampling a potential parent from the past mixes the current frequencies towards the seed-bank frequencies $Y$ at rate $\alpha$, while the seed bank is refreshed from the active population at rate $\beta$; interactions among the sampled parents contribute the polynomial drift $\mu$, and binomial resampling contributes Wright-Fisher noise of size $1/(N\rho_N)$ on the selective time scale. In the rock-paper-scissors case without seed bank and $\sigma>0$, the deterministic neutral cycles of $\mu$ are destroyed by drift and one type fixes; with a seed bank, $Y$ acts as a temporal refuge that lags the active population and pulls it back towards the interior. In the paper this stabilization (much longer fixation times than an equivalent increase in population size) is established by simulation of the limiting system, not by a theorem.

## Sources

- J. Chacón, A. González-Casanova, I. Nuñez, R. Peña-Miller, "Dormancy stabilizes non-transitive competitive dynamics", arXiv preprint (2026), Theorem 1 and Proposition 1 (Supplementary Information, Section A), <https://doi.org/10.48550/arXiv.2608.17179>.
