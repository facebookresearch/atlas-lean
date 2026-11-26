# Expected site frequency spectrum and mutational burden of a birth–death tumour

**Model.** Cells divide at rate $b$ and die at rate $d$ (rates may change between a growth phase and a treatment phase). At each division both daughter cells receive independent $\mathrm{Poisson}(m)$ numbers of new mutations under the infinite-sites assumption. Let $p(x \to y, t)$ be the probability that the process grows from $x$ to $y$ cells in time $t$, $N(t')$ the expected population size at time $t'$ of an interval $[0, t]$, and $N_0$ the initial size. $S_k$ is the number of mutations carried by exactly $k$ cells and $B = \sum_k S_k$ the total mutational burden; superscripts separate mutations newly arising in $[0,t]$ from those preexisting at time $0$.

**Compound Poisson structure.** If $W_k$ is the number of branches of the cell tree subtending exactly $k$ cells and $R$ the number of tree nodes with a living descendant, then $S_k$ and $B$ are Poisson sums over $W_k$ and $R$, so

$$E[S_k] = m\,E[W_k], \quad \mathrm{Var}[S_k] = m\,E[W_k] + m^2\,\mathrm{Var}[W_k], \qquad E[B] = m\,E[R], \quad \mathrm{Var}[B] = m\,E[R] + m^2\,\mathrm{Var}[R].$$

**Theorem 1 (SFS).** Conditioned on survival to time $t$,

$$E[S_k^{(new)}] = \frac{1}{1 - p(N_0 \to 0, t)}\int_0^t 2 m b\, N(t')\, p(1 \to k, t - t')\,dt',$$

$$E[S_k^{(pre)}] = \frac{1}{1 - p(N_0 \to 0, t)}\sum_{k'=1}^{N_0} E[S_{k'}^{(init)}]\, p(k' \to k, t),$$

where $E[S_{k'}^{(init)}]$ is the expected SFS at time $0$.

**Theorem 2 (tMB).** Under the same hypotheses,

$$E[B^{(new)}] = \frac{1}{1 - p(N_0 \to 0, t)}\int_0^t 2 m b\, N(t')\,\big(1 - p(1 \to 0, t-t')\big)\,dt',$$

$$E[B^{(pre)}] = \frac{1}{1 - p(N_0 \to 0, t)}\sum_{k'=1}^{N_0} E[S_{k'}^{(init)}]\,\big(1 - p(k' \to 0, t)\big).$$

**Special cases.** For a pure-birth process observed at a fixed size $N_d$, $B \approx \mathrm{Poisson}(2 m N_d)$. During a treatment phase with balanced rates $b_2 = d_2$ lasting time $t_f$, the population stays at expected size $N_f$ and, for large $N_f$ (when conditioning on survival is negligible), the expected burden of newly arising mutations is

$$E[B^{(new)}] = 2 m N_f \ln(1 + b_2 t_f).$$

## Expansion

A mutation born at time $t'$ arises on one of the two daughters of a division; divisions occur at expected rate $b N(t')$, giving the factor $2 m b N(t')$. The mutation is seen in exactly $k$ cells at time $t$ if the lineage founded by that one cell has size $k$ after time $t - t'$, with probability $p(1 \to k, t-t')$, and it contributes to the burden if that lineage survives, with probability $1 - p(1 \to 0, t-t')$. A preexisting mutation carried by $k'$ cells is the indicator of a subpopulation that evolves as an independent birth–death process started from $k'$. Dividing by $1 - p(N_0 \to 0, t)$ conditions on survival of the whole population. For $b_2 = d_2$ the critical process has $p(1 \to 0, s) = b_2 s/(1 + b_2 s)$, so $1 - p(1 \to 0, s) = 1/(1 + b_2 s)$ and integrating $2 m b_2 N_f/(1 + b_2 s)$ over $[0, t_f]$ gives the logarithm. Because $\mathrm{Var}[R] > 0$ whenever death or fixed-time sampling adds randomness to the number of divisions, the burden is overdispersed relative to a Poisson variable.

## Sources

- A. Stein, B. Werner, "On the patterns of genetic intra-tumor heterogeneity before and after treatment", Genetics (2025) iyaf101, Eqs. (4)–(6), (14)–(16), (19)–(21) and Theorems 1–2, <https://doi.org/10.1093/genetics/iyaf101>, PMCID PMC12341898.
