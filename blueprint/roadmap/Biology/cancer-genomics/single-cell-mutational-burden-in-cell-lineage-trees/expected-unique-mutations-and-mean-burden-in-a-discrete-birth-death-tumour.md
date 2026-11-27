# Expected unique mutations and mean single-cell burden in a discrete birth–death tumour

**Model.** A discrete-time birth–death chain on population sizes: at each step a uniformly chosen living cell divides with probability $\beta$ or dies with probability $\delta = 1 - \beta$, with $\beta > \delta$. Each division gives the two daughters $\mathrm{Pois}(\mu)$ new (infinite-sites) mutations each. Start from $N_0 = 1$ mutation-free cell. Let $M_i$ be the number of distinct mutations present at step $i$ and $C_i$ the number of mutational occurrences (the total number of (cell, mutation) pairs, i.e. $C_i = \sum_k k B_{k,i} = \sum_j j S_{j,i}$, where $S_{j,i}$ is the site frequency spectrum). Then $C_i/N_i$ is the mean single-cell mutational burden.

**Proposition (pure birth, $\beta = 1$).**

$$\mathbb{E}[M_i] = 2\mu i, \qquad \mathbb{E}[C_i] = 2\mu(i+1)\big(H_{i+1} - 1\big),$$

where $H_n = \sum_{k=1}^n k^{-1}$. Hence the mean burden per cell is $2\mu(H_{i+1}-1) \sim 2\mu \log i$, growing logarithmically in the step count.

**Proposition (extinction).** With absorption at $0$ and at a cap $N$, the probability that the birth–death chain started from $N_0 = z \in \{0,\dots,N\}$ cells is absorbed at $0$ is

$$\gamma_z = \frac{(\delta/\beta)^N - (\delta/\beta)^z}{(\delta/\beta)^N - 1},$$

which tends to $(\delta/\beta)^z$ as $N \to \infty$.

## Proof sketch

Each division contributes $2\mu$ new mutations in expectation, so with $i$ divisions $\mathbb{E}[M_i] = 2\mu i$ in the pure-birth case. For occurrences, $N_i = i+1$, and a division duplicates the dividing cell's mutations (expected number $\mathbb{E}[C_i]/(i+1)$) and adds $2\mu$ new ones: $\mathbb{E}[C_{i+1}] = \frac{i+2}{i+1}\mathbb{E}[C_i] + 2\mu$ with $\mathbb{E}[C_0] = 0$, whose solution is the harmonic-number formula. The extinction probability solves the gambler's-ruin recursion $\gamma_z = \beta\gamma_{z+1} + \delta\gamma_{z-1}$ with $\gamma_0 = 1$, $\gamma_N = 0$.

With death, the same recursions hold with division and death weights and random $N_i$. Replacing ratios of expectations by their first-order values, the source obtains, conditioned on survival, the approximations (no error bound is proved)

$$\mathbb{E}[M_i] \approx 2\mu\Big(\beta - \frac{\beta(\beta-\delta)}{\delta}\log\Big(1 - \frac{\delta}{\beta}\Big)(i-1)\Big), \qquad \mathbb{E}[C_i] \approx 2\mu\beta\, \mathbb{E}[N_i]\sum_{i'=1}^{i}\frac{1}{\mathbb{E}[N_{i'}]},$$

the first by summing the first-order site frequency spectrum $\mathbb{E}[S_{j,i}] \approx \sum_{j' \ge 0} 2\mu(\delta/\beta)^{j'}\mathbb{E}[N_i]/((j+j')(j+j'+1))$ over $j$.

## Depends on

- [Division and mutational burden distributions of the discrete-time Yule process](division-and-mutational-burden-distributions-of-the-discrete-yule-process.md)

## Sources

- Christo Morison, Dudley Stark and Weini Huang, "Single-cell mutational burden distributions in birth–death processes", *PLOS Computational Biology* 21 (2025), e1013241, <https://doi.org/10.1371/journal.pcbi.1013241>. Preprint version: arXiv:2309.06355 (2023), Supplementary Propositions S1, S4, S7 and S8, <https://doi.org/10.48550/arXiv.2309.06355>.
