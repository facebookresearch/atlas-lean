# Order of allele extinctions in the Λ-Wright–Fisher process

**Model.** Fix $d \in \mathbb{N}$ and a finite Borel measure $\Lambda$ on $[0,1]$. The $(d+1)$-type $\Lambda$-Wright–Fisher process without mutation is the Markov process $\mathbf{X}$ on the simplex $\Delta_d = \{\mathbf{x} \in [0,1]^d : \sum_i \mathbf{x}(i) \le 1\}$, with $\mathbf{x}(d+1) := 1 - \sum_{i \le d} \mathbf{x}(i)$, whose generator is
$$\mathcal{L} f(\mathbf{x}) = \frac{\Lambda(\{0\})}{2} \sum_{i,j=1}^d \mathbf{x}(i)\big(\mathbf{1}\{i=j\} - \mathbf{x}(j)\big) \partial_{ij} f(\mathbf{x}) + \int_{(0,1]} \sum_{i=1}^{d+1} \mathbf{x}(i) \big[f((1-r)\mathbf{x} + r \mathbf{e}_i) - f(\mathbf{x})\big] \frac{\Lambda(dr)}{r^2},$$
with $\mathbf{e}_{d+1} := 0$. The diffusion part is Wright–Fisher resampling; the jump part replaces a fraction $r$ of the population by the offspring of one individual (a large-offspring event). Assume the dual $\Lambda$-coalescent comes down from infinity, i.e. with $\lambda_{n,k} = \int_{(0,1]} r^{k-2}(1-r)^{n-k} \Lambda(dr)$,
$$\sum_{n \ge 2} \Big( \sum_{k=2}^n (k-1)\binom{n}{k}\big[\lambda_{n,k} + \mathbf{1}\{k=2\}\Lambda(\{0\})\big] \Big)^{-1} < \infty.$$
Let $T_{\mathrm{lost},i}^{\mathbf{x}}$ be the first time type $i$ vanishes when $\mathbf{X}_0 = \mathbf{x}$.

**Proposition.** For every ordering $(c_1, \dots, c_{d+1})$ of the $d+1$ types,
$$\mathbb{P}\big(T_{\mathrm{lost},c_{d+1}}^{\mathbf{x}} < \cdots < T_{\mathrm{lost},c_1}^{\mathbf{x}}\big) = \prod_{i=1}^{d+1} \frac{\mathbf{x}(c_i)}{1 - \sum_{j<i} \mathbf{x}(c_j)}.$$
In particular type $\eta$ is the first to disappear with probability $\sum \prod_{i=1}^{d} \mathbf{x}(c_i)/(1 - \sum_{j<i}\mathbf{x}(c_j))$, the sum over orderings $(c_1, \dots, c_d, \eta)$ ending in $\eta$.

The answer is the same for every $\Lambda$ satisfying the condition: survival order is a size-biased permutation of the initial frequencies, the eventual winner $c_1$ being type $i$ with probability $\mathbf{x}(i)$.

## Expansion

In the lookdown construction each level carries a type; level $k$ is assigned type $i$ by an i.i.d. uniform falling in an interval of length $\mathbf{x}(i)$. Without mutation the types that survive longest are those that appear first among the levels, because higher levels are overwritten by lower ones and a fixation line pushing upward eventually explodes. Hence the order of extinction reverses the order in which types first appear in an i.i.d. sequence with law $\mathbf{x}$, which is the size-biased permutation, independent of $\Lambda$; the coming-down condition guarantees finite explosion times so all extinctions happen in finite time.

## Sources

- Airam Blancas, Adrián González Casanova, Sebastian Hummel and Sandra Palau, "Fixation and stationary times for the Λ-Wright-Fisher process", arXiv:2308.09218 (2023), Section 2, condition on coming down from infinity, Proposition 1 and Corollary 3, <https://doi.org/10.48550/arXiv.2308.09218>.
