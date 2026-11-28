# Expected site frequency spectrum of a critical branching sample

Use the [coalescent point process of a sample from a critical birth–death tree](coalescent-point-process-of-a-sample-from-a-critical-birth-death-tree.md) and its laws $P^t_n$, $P^{(\infty)}_n$, $P^{(i)}_n$ with sampling parameter $p$. Mutations occur as a Poisson process of rate $\theta$ along lineages under the infinite-sites model, and $\xi_k$ is the number of mutations carried by exactly $k$ of the $n$ sampled individuals; $S = \sum_k \xi_k$ is the number of segregating sites.

**Proposition (fixed origin; Achaz–Delaporte–Lambert, Proposition 3.1).** For $1 \le k \le n-1$, $t > 0$ and $\tau = pt$,

$$E^t_n(\xi_k) = \frac{\theta}{p} \left\{ \frac{n-3k-1}{k} + \frac{(n-k-1)(k+1)}{k\tau} + \frac{(1+\tau)^{k-1}}{\tau^{k+1}} \Big[ 2\tau^2 - 2(n-2k-1)\tau - (n-k-1)(k+1) \Big] \Big[ \ln(1+\tau) - \sum_{i=1}^{k-1} \frac{1}{i}\Big(\frac{\tau}{1+\tau}\Big)^{i} \Big] \right\}.$$

**Proposition (Propositions 3.2 and 3.3).** Under $P^{(\infty)}_n$ every $\xi_k$ has infinite expectation, but the normalized spectrum is flat in the limit of an old origin:

$$\lim_{t\to\infty} \frac{E^t_n(\xi_k)}{E^t_n(S)} = \frac{1}{n-1}.$$

**Proposition (uniform prior; Proposition 3.4).** For $1 \le k \le n-1$,

$$E^{(0)}_n(\xi_k) = \frac{n\,\theta}{p\,k}.$$

**Proposition (prior $1/x$; Proposition 3.5).** For $1 \le k \le n-3$, with $\mathcal H_k = \sum_{j=1}^k j^{-1}$,

$$E^{(1)}_n(\xi_k) = \frac{\theta}{p}\cdot\frac{n(n-1)}{(n-k)(n-k-2)} \left[ \frac{n+k-2}{k} - \frac{2(n-1)}{n-k-1}\big(\mathcal H_{n-1} - \mathcal H_k\big) \right].$$

Under the uniform prior the expected spectrum is proportional to $1/k$, the same shape as the neutral spectrum under Kingman's coalescent, even though the genealogy is that of a critical branching population rather than a constant-size one.

## Depends on

- [Coalescent point process of a sample from a critical birth–death tree](coalescent-point-process-of-a-sample-from-a-critical-birth-death-tree.md)

## Expansion

In a coalescent point process, a mutation on the branch above individual $j$ at height $\ell$ is carried by individuals $j, j+1, \dots, j+k-1$ exactly when $\max(H_{j+1},\dots,H_{j+k-1}) < \ell < \min(H_j, H_{j+k})$, with the conventions for the boundary branches. Since the node depths are i.i.d., $E(\xi_k)$ reduces to $\theta$ times an expected length expressed through one-dimensional integrals of powers of the distribution function $F(x) = \frac{(1+pt)\,px}{pt\,(1+px)}$; these are integrals of the form $\int x^{k-l}(1+x)^{-k}dx$, evaluated in closed form in the appendix. Mixing over the posterior of the origin time gives the formulas for $P^{(0)}_n$ and $P^{(1)}_n$, while for infinite origin the heavy tail $1/(1+px)$ makes every expected branch length infinite.

## Sources

- G. Achaz, C. Delaporte and A. Lambert, *Sample genealogy and mutational patterns for critical branching populations*, published as "Mutational pattern of a sample from a critical branching population", *Journal of Mathematical Biology* 73 (2016), 627–664, <https://doi.org/10.1007/s00285-015-0964-2>; preprint arXiv:1407.7720, <https://doi.org/10.48550/arXiv.1407.7720>.
