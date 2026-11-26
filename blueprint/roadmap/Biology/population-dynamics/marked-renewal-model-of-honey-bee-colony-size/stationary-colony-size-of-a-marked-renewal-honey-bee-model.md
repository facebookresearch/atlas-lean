# Stationary colony size of a marked renewal model of a honey bee colony

**Model.** The queen lays batches of eggs at times forming a discrete-time renewal process: the gaps $\tau_i$ between batches are i.i.d. positive integers with distribution $f_j = \Pr(\tau_1 = j)$, finite mean and variance, and span $d = \gcd\{j : f_j > 0\}$. Batch $i$ has $\zeta_i$ eggs, each hatching independently with probability $r$, and the hatched bee $j$ of batch $i$ lives an integer lifetime $\eta_{ij}$ with $q_k = \Pr(\eta_{11} = k)$; the sequences $(\tau_i)$, $(\zeta_i)$, the hatching indicators and $(\eta_{ij})$ are independent and each i.i.d. The colony size at time $n$ is

$$ M_n = \sum_{i=1}^{N_n} \sum_{j=1}^{\xi_i} \mathbf{1}\{ S_i + \eta_{ij} \ge n \}, $$

where $S_i$ is the time of batch $i$, $N_n$ the number of batches up to time $n$, and $\xi_i$ the number of hatched eggs in batch $i$. Let $\tilde S_i = \tilde\tau_1 + \tau_2 + \dots + \tau_i$, where $\tilde\tau_1$ has the stationary forward-recurrence law $\pi_k = (1 - F_\tau(k-1))/\mathbb{E}\tau_1$, and define $\mathcal{M} = \sum_{i \ge 1} \sum_{j=1}^{\xi_i} \mathbf{1}\{ \tilde S_i \le \eta_{ij} + 1 \}$.

**Theorem 1.** Assume $d = 1$ and $\mathbb{E}\zeta_1 < \infty$. Then $M_n$ converges in total variation to $\mathcal{M}$, with

$$ d_{TV}(M_n, \mathcal{M}) \le \begin{cases} r\, \mathbb{E}\zeta_1\, \mathbb{E}\max\{\eta_{11} + 1 - n, 0\} = O(n^{-1}) & \text{if } \tau_1 \text{ is deterministic}, \\ O(n^{-1/2}) & \text{otherwise}, \end{cases} \qquad \mathbb{E}\mathcal{M} = \frac{r\, \mathbb{E}\zeta_1\, (\mathbb{E}\eta_{11} + 1)}{\mathbb{E}\tau_1}. $$

The variance of $\mathcal{M}$ is given explicitly in terms of $r$, the mean and variance of $\zeta_1$, $\mathbb{E}(\eta_{11} \wedge \eta_{12})$, the lifetime probabilities $q_v$, and the renewal function $H(n) = \mathbb{E} N_n$, which solves $H(n) = F_\tau(n) + \sum_{k=1}^{n} H(n-k) f_k$.

**Corollary 2.** If the gaps are deterministic, so that the $\tilde S_i$ are constants, then

$$ \mathbb{E} e^{\mathrm{i} u \mathcal{M}} = \prod_{i=1}^{\infty} \psi_\zeta\Bigl( r (e^{\mathrm{i} u} - 1)\bigl(1 - F_\eta(\tilde S_i - 2)\bigr) + 1 \Bigr), \qquad \psi_\zeta(s) = \mathbb{E} s^{\zeta_1}, $$

and if $\zeta_1 \sim \mathrm{Poisson}(\lambda)$ then $\mathcal{M} \sim \mathrm{Poisson}\bigl( r \lambda \sum_{i \ge 1} (1 - F_\eta(\tilde S_i - 2)) \bigr)$.

**Theorem 3 (seasonal cycle).** If batches are daily ($\tau_1 \equiv 1$), the batch-size law, hatching probability $r_i$ and lifetime law depend on the day within a cycle of length $D$, $\mathbb{E}\zeta_i < \infty$, and lifetimes are bounded by $K$, then $(M_{lD+n})_l$ is stationary once $lD + n > K$, with characteristic function $\prod_{i = n+lD-K}^{n+lD} \psi_{\zeta,i}\bigl( r_i (e^{\mathrm{i}t} - 1)(1 - F_{\eta,i}(n + lD - i - 1)) + 1 \bigr)$; with Poisson batch sizes the colony size is Poisson.

## Expansion

Each hatched bee present at time $n$ is a point of a marked renewal process thinned by survival of its lifetime past the elapsed time, so $M_n$ is a sum over past batches of independent thinned batch sizes. Viewing the process from time $n$ backwards, the time since the last batch is the backward recurrence time of the renewal process, whose law converges to the stationary law $\pi$ when $d = 1$; coupling the backward recurrence chain with its stationary version gives the total variation rate, $O(n^{-1/2})$ from the coupling time of a non-degenerate aperiodic renewal process and $O(n^{-1})$ from the lifetime tail when gaps are fixed. The mean follows from Wald's identity: batches arrive at rate $1/\mathbb{E}\tau_1$, each contributing $r \mathbb{E}\zeta_1$ bees that live $\mathbb{E}\eta_{11} + 1$ time steps on average. With deterministic gaps the thinned batch counts are independent across batches, so the characteristic function factorizes, and Poisson thinning preserves the Poisson law.

## Sources

- Aihua Xia, Richard M. Huggins, Martine J. Barons, Louis Guillot, "A marked renewal process model for the size of a honey bee colony", arXiv (2016). Section 2 (model), Theorem 1, Corollary 2, Theorem 3. <https://doi.org/10.48550/arXiv.1604.00051>
