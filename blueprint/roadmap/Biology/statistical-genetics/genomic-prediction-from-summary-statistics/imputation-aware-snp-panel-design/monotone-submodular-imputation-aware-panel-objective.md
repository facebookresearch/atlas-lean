# Monotone submodular imputation-aware panel objective

Let $V = \{1,\dots,p\}$ be dense loci, each on a chromosome $c(i)$, and let $Q = [q_{ij}] \in [0,1]^{p\times p}$ be a recoverability matrix ($q_{ij}$ a proxy for the dosage $R^2$ of imputing locus $j$ from typed locus $i$, zero across chromosomes, $q_{ii} = 1$). For a panel $S \subseteq V$ define

$$C(S) = \sum_{j=1}^p w_j \max_{i\in S} q_{ij}, \qquad U(S) = \sum_{i\in S} u_i, \qquad B(S) = \sum_{c=1}^{C}\eta_c\log\left(1 + n_c(S)\right),$$

with $C(\emptyset) = 0$, locus weights $w_j \ge 0$, marker utilities $u_i \ge 0$ (training-only association, PCA leverage and heterozygosity scores), chromosome weights $\eta_c \ge 0$ and $n_c(S)$ the number of selected markers on chromosome $c$. The **imputation-aware panel optimization** objective is

$$F(S) = \alpha C(S) + \beta U(S) + \gamma B(S), \qquad |S| \le k,$$

with $\alpha,\beta,\gamma \ge 0$ (Xu and Tan 2026, Eqs. 2–6).

**Theorem.** $F$ is normalized, monotone and submodular (Theorem 1). Hence the greedy panel $S_k$, adding at each step the marker of largest marginal gain, satisfies $F(S_k) \ge \left(1 - (1 - 1/k)^k\right)F(S^\star) \ge (1 - e^{-1})F(S^\star)$ for an optimal panel $S^\star$ of size $k$ (Theorem 2); greedy panels are nested across budgets and each prefix carries its own guarantee (Lemma 1); and conditioning on a mandatory marker set $M$ preserves submodularity, so greedy augmentation of $M$ retains the $1 - 1/e$ guarantee (Proposition 2).

## Depends on

- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Expansion

The coverage term is a facility-location function: for each locus $j$, $f_j(S) = w_j\max_{i\in S}q_{ij}$ has marginal gain $w_j(q_{ej} - \max_{i\in S}q_{ij})_+$, which decreases as $S$ grows. $U$ is modular, and $B$ is a sum of concave functions of counts, which are submodular; nonnegative combinations preserve monotone submodularity. The greedy bound is the Nemhauser–Wolsey–Fisher argument: $F(S^\star) - F(S_t) \le k\,[F(S_{t+1}) - F(S_t)]$, iterated $k$ times.

## Sources

- Y. Xu and X. Tan, *Imputation-aware optimization of ultra-low-density SNP panels: synthetic benchmarking and evaluation*, Plants 15(21) (2026), 3346, Eqs. (2)–(6), Theorems 1–2, Lemma 1 and Proposition 2. <https://doi.org/10.3390/plants15213346>
