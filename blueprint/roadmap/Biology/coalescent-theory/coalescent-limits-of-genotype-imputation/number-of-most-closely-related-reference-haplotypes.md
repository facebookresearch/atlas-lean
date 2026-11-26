# Number of most closely related reference haplotypes under the Kingman coalescent

Consider a target haplotype and $n \ge 1$ reference haplotypes whose genealogy at a site is a Kingman coalescent tree on $n + 1$ exchangeable leaves (neutral, panmictic, constant or time-varying population size; only the topology matters below). The **most closely related reference haplotypes** of the target are the $u \ge 1$ reference leaves descending from the branch on which the target lineage first coalesces with the reference genealogy. An idealized imputation method that copies these haplotypes with equal weight imputes dosage $\hat g = j/u$ when $j$ of them carry the derived allele.

**Lemma (Si, Vanderwerff and Zöllner 2021, Eq. 1).** In a Kingman coalescent with $m$ lineages, the probability that a specified set of $k$ lineages ($1 \le k \le m - 1$) all coalesce among themselves before any of them coalesces with one of the other $m - k$ lineages is

$$q_{k, m-k} = \frac{2\,(k - 1)!\,(m - k)!}{(k + 1)\,(m - 1)!}.$$

**Proposition (Si, Vanderwerff and Zöllner 2021, Eqs. 2–3).** The number $U$ of most closely related reference haplotypes has law

$$\mathbb{P}(U = u; n) = \frac{4}{u(u + 1)(u + 2)} \quad (1 \le u \le n - 1), \qquad \mathbb{P}(U = n; n) = \frac{2}{n(n + 1)},$$

and mean

$$\mathbb{E}[U; n] = \frac{2n}{n + 1} \longrightarrow 2 \quad (n \to \infty).$$

In particular, however large the reference panel, the target typically has only one or two equally close templates, which bounds how well a rare variant private to a few closely related haplotypes can be imputed.

## Depends on

- [Kingman's coalescent](../coalescents/merger-rate-dirac-zero.md)
- [The Li–Stephens copying model](../../population-structure/li-stephens-haplotype-copying-model/hmm.md)

## Proof depends on

- [Clade probability](../multispecies-coalescent/random-joining-is-clade.md)
- [Kingman's coalescent](../coalescents/merger-rate-dirac-zero.md)

## Expansion

The event $\{U = u\}$ for a given set $A$ of $u$ reference leaves happens in two stages: the $u + 1$ lineages of $A$ and the target coalesce among themselves before meeting the other $n - u$ (probability $q_{u+1, n-u}$ among $n + 1$ lineages), and within that group the $u$ lineages of $A$ coalesce before meeting the target (probability $q_{u, 1} = 2/(u(u+1))$ among $u + 1$ lineages). Multiplying by the $\binom{n}{u}$ choices of $A$,

$$\binom{n}{u} \frac{2\,u!\,(n - u)!}{(u + 2)\, n!} \cdot \frac{2}{u(u + 1)} = \frac{4}{u(u+1)(u+2)}.$$

For $u = n$ only the second stage is needed, giving $q_{n,1} = 2/(n(n+1))$. The mean follows from the telescoping sum $\sum_{u=1}^{n-1} \frac{4}{(u+1)(u+2)} = 2 - \frac{4}{n+1}$, plus $n \cdot \frac{2}{n(n+1)}$.

## Sources

- Y. Si, B. Vanderwerff and S. Zöllner, "Why are rare variants hard to impute? Coalescent models reveal theoretical limits in existing algorithms", Genetics 217 (2021), iyab011, <https://doi.org/10.1093/genetics/iyab011> (PMC8049559); preprint bioRxiv (2021), Methods Section 2.1, Eqs. 1–3, <https://doi.org/10.1101/2020.08.10.245043>.
