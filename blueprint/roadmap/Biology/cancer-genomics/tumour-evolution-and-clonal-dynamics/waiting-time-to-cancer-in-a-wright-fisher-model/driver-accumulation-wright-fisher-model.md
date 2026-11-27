# Driver-accumulation Wright–Fisher model

Fix integers $d \ge k \ge 1$ (susceptible driver genes and the number of driver mutations defining cancer), a per-gene mutation probability per cell division $u \in (0,1)$ and a selective advantage $s \ge 0$ per driver mutation. Each cell is a binary string of length $d$; since all drivers are exchangeable, it suffices to track the **error classes** $j = 0, 1, \dots, k$, where class $j < k$ consists of cells with exactly $j$ mutated drivers and class $k$ of cells with at least $k$ mutated drivers. Let $N(t)$ be the population size in generation $t$, $N_j(t)$ the number of cells in class $j$ and $x_j(t) = N_j(t)/N(t)$.

The relative fitness of class $j$ is

$$w_j = \frac{(1+s)^j}{\sum_{\ell=0}^{k} (1+s)^\ell x_\ell},$$

so each additional driver multiplies fitness by $1+s$ (no epistasis). Ignoring back mutation, a cell sampled for generation $t+1$ belongs to class $j < k$ with probability

$$\theta_j = \sum_{i=0}^{j} \binom{d-i}{j-i}\, u^{\,j-i} (1-u)^{\,d-j}\, w_i\, x_i(t),$$

i.e. a parent of class $i$ is chosen proportionally to fitness and then acquires exactly $j-i$ new mutations among its $d-i$ unmutated drivers, and to class $k$ with probability

$$\theta_k = \sum_{i=0}^{k} w_i\, x_i(t)\, \Pr\big[\mathrm{Bin}(d-i, u) \ge k-i\big],$$

the chance that the parent's mutated drivers reach at least $k$ (for $i = k$ this probability is $1$). Since $\sum_i w_i x_i = 1$ and, for each parent class $i$, the events "exactly $j - i$ new mutations" ($i \le j < k$) and "at least $k - i$" partition the outcomes, $\sum_{j=0}^{k} \theta_j = 1$. The next generation is multinomial,

$$\big(N_0(t+1), \dots, N_k(t+1)\big) \sim \mathrm{Multinomial}\big(N(t+1);\ \theta_0, \dots, \theta_k\big),$$

and the population grows approximately exponentially from $N(0) = N_{\mathrm{init}}$ to a final size $N_{\mathrm{fin}}$ (Beerenwinkel et al. take $N_{\mathrm{init}} = 10^6$ and $N_{\mathrm{fin}} = 10^9$ cells over about 11 years, one generation per day). The **waiting time to cancer** $t_k$ is the first generation in which $N_k(t) > 0$.

Because only the first appearance of a cell with at least $k$ mutated drivers matters, the $2^d$ genotypes collapse to $k+1$ classes, which makes simulation feasible even for $N \approx 10^9$.

## Depends on

- [Neutral Wright–Fisher transition matrix](../../../population-genetics/wright-fisher-markov-chain/wright-fisher.md)

## Expansion

The binomial factor counts the ways to choose which $j-i$ of the remaining $d-i$ genes mutate, each independently with probability $u$, while the other $d-j$ stay unmutated. Beerenwinkel et al. print the formula for $\theta_j$ for every $j \le k$ with class $k$ meaning exactly $k$ drivers; for $k < d$ those weights sum to less than $1$, so the top class here absorbs all cells with at least $k$ drivers, which leaves $t_k$ unchanged. With $s > 0$ the simulated class distribution quickly settles into a travelling wave of approximately constant variance that moves to higher classes at constant speed, so $t_k$ grows linearly in $k$; with $s = 0$ waiting times for realistic $u$ and $N$ are far longer than the clinical adenoma–carcinoma interval. The Wright–Fisher rather than Moran dynamics is chosen for computational efficiency; both behave similarly for large populations.

## Sources

- N. Beerenwinkel, T. Antal, D. Dingli, A. Traulsen, K. W. Kinzler, V. E. Velculescu, B. Vogelstein and M. A. Nowak, "Genetic progression and the waiting time to cancer", PLoS Computational Biology 3(11) (2007), e225, Methods ("Wright-Fisher process"), <https://doi.org/10.1371/journal.pcbi.0030225>, PMCID: PMC2065895.
