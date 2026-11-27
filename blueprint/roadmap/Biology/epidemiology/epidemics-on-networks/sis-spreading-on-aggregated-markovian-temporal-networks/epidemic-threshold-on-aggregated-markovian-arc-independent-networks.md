# Epidemic threshold on aggregated-Markovian arc-independent networks

**Spreading model.** In the heterogeneous networked SIS model on $n$ nodes, an infected node $i$ recovers at rate $\delta_i > 0$ and a susceptible node $i$ is infected at rate $\beta_i\sum_j a_{ij}(t)X_j(t)$. With $B = \mathrm{diag}(\beta_i)$, $D = \mathrm{diag}(\delta_i)$, the infection probabilities are upper-bounded by the linear system

$$\Sigma: \quad \dot p(t) = \big(BA(t) - D\big)p(t),$$

and almost sure exponential stability of $p = 0$ (with $\limsup_t t^{-1}\log\|p(t)\| \le -\lambda < 0$ a.s.) implies exponential extinction.

**Temporal network.** In an *aggregated-Markovian arc-independent* (AMAI) network, each arc indicator is $A_{ij}(t) = g_{ij}(\theta_{ij}(t))$ for independent finite-state Markov processes $\theta_{ij}$ and $\{0,1\}$-valued $g_{ij}$; aggregation lets on/off durations follow arbitrary phase-type laws, approximating any inter-switching distribution. Assume every $\sigma_{ij} = g_{ij}(\theta_{ij})$ is irreducible and set $\bar A_{ij} = \lim_{t\to\infty}\mathbb P(A_{ij}(t) = 1)$.

Let $\mu(M) = \eta\big((M + M^\top)/2\big)$ be the matrix measure ($\eta$ the largest real part of the spectrum), $\bar\beta = \max_i\beta_i$, $\underline\delta = \min_i\delta_i$, and

$$\kappa_{b,d}(s) = n\,e^{s/b}\Big(\frac{bs + d}{d}\Big)^{-(bs+d)/b^2}, \qquad \Delta_1 = \max_i\sum_j\Big(\beta_i^2\bar A_{ij}(1-\bar A_{ij}) + \beta_j^2\bar A_{ji}(1-\bar A_{ji})\Big),$$

$$c_1 = \mu\big(B\,\mathrm{sgn}(\bar A) - D\big) - \tfrac12\kappa^{-1}_{\bar\beta,\Delta_1}(1), \qquad \bar s_1 = 2\underline\delta + 2c_1^-.$$

**Theorem.** Let

$$\tau_A = \max_{s \in (\kappa^{-1}_{\bar\beta,\Delta_1}(1),\,\bar s_1]}\left(-\frac{s + 2c_1\kappa_{\bar\beta,\Delta_1}(s)}{2\big(1 - \kappa_{\bar\beta,\Delta_1}(s)\big)}\right).$$

If

$$\mu\big(B\bar A - D\big) < \tau_A,$$

then the disease-free equilibrium of $\Sigma$ is almost surely exponentially stable, with decay rate at least $-\mu(B\bar A - D)\big(1 - \kappa(s^*)\big) - s^*/2 - c_1\kappa(s^*)$, where $s^*$ is the maximizer and $\kappa = \kappa_{\bar\beta,\Delta_1}$.

The condition involves only $n\times n$ matrices, whereas the exact Itô-formula criterion requires the spectrum of a $2^m\times2^m$ generator over all $m$ arc states. Checking it costs $O(nm^2)$ operations for $m$ arcs instead of $O(nm^2 2^m)$, and it shows why thresholds computed from the static aggregated network $\bar A$ become more accurate for large networks.

## Expansion

Write $A(t) = \bar A + (A(t) - \bar A)$. The mean part gives the drift $\mu(B\bar A - D)$ of $\log\|p\|^2$; the fluctuation part is a sum of independent, bounded, centered matrix terms whose total variance is controlled by $\Delta_1$. A concentration inequality for sums of independent random matrices (of Chung–Radcliffe type) produces the function $\kappa_{b,d}$, which bounds the probability that the fluctuation term's matrix measure exceeds a level $s$. Ergodicity of the irreducible arc processes lets the time-average drift converge, and optimizing over the level $s$ trades the concentration loss against the margin, yielding $\tau_A$.

## Sources

- Masaki Ogura, Victor M. Preciado, "Stability of spreading processes over time-varying large-scale networks", arXiv (2015). Section 2 (HeNeSIS model, AMEI/AMAI random graph processes, Definitions 2.2, 2.4 and 2.5), Section 3 (Proposition 3.1, Theorem 3.2 and its edge-independent analogue Theorem 3.5). <https://doi.org/10.48550/arXiv.1507.07017>. Published version: IEEE Transactions on Network Science and Engineering 3(1) (2016), 44–57, <https://doi.org/10.1109/tnse.2016.2516346>; locators above refer to the arXiv version.
