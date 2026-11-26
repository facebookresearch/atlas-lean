# Site and branch statistics of a tree sequence and their duality

Let a genome segment $[0, L)$ carry a tree sequence: marginal trees $T_1, \dots, T_K$ on the same set of sample nodes, where $T_k$ covers the half-open interval $[a_{k-1}, a_k)$. Each sample node $v$ carries a weight $w(v) \in \mathbb{R}^d$, with total weight $w_{\mathrm{total}} = \sum_v w(v)$. For a node $u$ of $T_k$ let $x_k(u)$ be the total weight of the samples descending from $u$, and let $\beta_k(u)$ be the length (in time) of the branch from $u$ to its parent in $T_k$. A **summary function** is any $f : \mathbb{R}^d \to \mathbb{R}$; it is **strict** if $f(0) = f(w_{\mathrm{total}}) = 0$.

**Site statistic.** Mutations sit at positions (sites) $s \in [0, L)$, real numbers rather than integers. At a site $s$ with genotypes $g_s(v)$, let $\bar x_s(a) = \sum_{v : g_s(v) = a} w(v)$ be the weight of the samples carrying allele $a$. For a window $[i, j)$ with $0 \le i < j \le L$, sum over the mutated sites that fall in the window and normalize by its span:

$$\mathrm{Site}(f, w)_s = \sum_a f(\bar x_s(a)), \qquad \mathrm{Site}(f, w)_{[i, j)} = \frac{1}{j - i} \sum_{s \in S \cap [i, j)} \mathrm{Site}(f, w)_s ,$$

where $S$ is the (finite) set of sites carrying a mutation. Under the infinite-sites model below, $S$ is a set of random points of $[0, L)$, so the window sum runs over observed mutation positions, not over integer positions.

**Branch statistic.** For the tree $T_k$,

$$\mathrm{Branch}(f, w)_k = \sum_{u \in T_k} \beta_k(u) \Big( f(x_k(u)) + f(w_{\mathrm{total}} - x_k(u)) \Big),$$

and over a window,

$$\mathrm{Branch}(f, w)_{[i, j)} = \frac{1}{j - i} \sum_{k=1}^{K} \ell_k(i, j)\, \mathrm{Branch}(f, w)_k, \qquad \ell_k(i, j) = \max\big(0, \min(j, a_k) - \max(i, a_{k-1})\big).$$

**Duality (Ralph, Thornton and Kelleher 2020, Eq. 9).** Suppose mutations arise on the tree sequence under the infinite-sites model as a Poisson process with constant rate $\mu$ per unit time per unit sequence length, so that no site is hit twice. Then for any strict summary function $f$ and any window $[i, j)$,

$$\mathrm{Branch}(f, w)_{[i, j)} = \frac{1}{\mu}\, \mathbb{E}\!\left[ \mathrm{Site}(f, w)_{[i, j)} \,\middle|\, T_{[i, j)} \right],$$

where the expectation holds the genealogies on $[i, j)$ fixed and averages over mutations.

**Example.** With $d = 1$, unit weights on $n$ samples and $f(x) = x(n - x)/(n(n-1))$, the site statistic is nucleotide diversity per unit length and the branch statistic is the mean pairwise path length in the trees, so expected diversity equals $\mu$ times the mean pairwise branch distance. When all samples are contemporary (sampled at the same time), the path length between two samples is twice their time to the most recent common ancestor, and the branch statistic is twice the mean pairwise TMRCA; with samples taken at different times the two differ.

## Depends on

- [Coalescence records encode a sequence of local trees exactly](../two-locus-coalescent/tree-sequence-encoding-represents-local-trees-ex.md)

## Proof depends on

- [Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md)

## Expansion

A single mutation on the branch above $u$ in $T_k$ creates a biallelic site whose derived allele has weight $x_k(u)$ and whose ancestral allele has weight $w_{\mathrm{total}} - x_k(u)$, so it contributes $f(x_k(u)) + f(w_{\mathrm{total}} - x_k(u))$ to the site statistic. Given the trees, the number of mutations falling on that branch within the window is Poisson with mean $\mu\, \beta_k(u)\, \ell_k(i, j)$. Linearity of expectation over branches, together with strictness (branches above the root or ancestral to all samples contribute zero), gives the identity. Polarized versions, which sum only $f(x_k(u))$ over derived alleles, satisfy the same duality.

## Sources

- P. L. Ralph, K. Thornton and J. Kelleher, "Efficiently Summarizing Relationships in Large Samples: A General Duality Between Statistics of Genealogies and Genomes", Genetics 215 (2020), 779–797, Equations 3, 4, 6, 7 and 9, <https://doi.org/10.1534/genetics.120.303253> (PMC7337078).
