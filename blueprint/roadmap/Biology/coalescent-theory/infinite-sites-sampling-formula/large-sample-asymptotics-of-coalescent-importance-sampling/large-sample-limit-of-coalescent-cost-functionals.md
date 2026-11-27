# Large-sample limit of cost functionals of the coalescent block-counting chain

**Setting.** Consider the Kingman coalescent with mutation for a sample of $d$ allele types, mutation rate $\theta > 0$ and mutation transition matrix $P = (P_{ij})_{i,j=1}^d$. The backward-in-time block-counting chain $\mathbf{N}^{(n)}(k) \in \mathbb{N}^d$ records the number of lineages of each type after $k$ backward events; each step either merges two lineages of type $j$ (jump $-\mathbf e_j$) or replaces a type-$j$ lineage by a type-$i$ lineage through a mutation (jump $-(\mathbf e_j - \mathbf e_i)$). Write $\mathbf Y^{(n)} = \mathbf N^{(n)}/n$ for the scaled chain, $M^{(n)}_{ij}(k)$ for the number of mutation steps $\mathbf e_j - \mathbf e_i$ among the first $k$ steps, and, for positive one-step costs $c^{(n)}(\mathbf v \mid \mathbf y)$, the cumulative cost

$$C^{(n)}(k) = \prod_{k'=1}^{k} c^{(n)}\big(n\mathbf Y^{(n)}(k'-1) - n\mathbf Y^{(n)}(k') \,\big|\, \mathbf Y^{(n)}(k'-1)\big), \qquad C^{(n)}(0) = 1.$$

**Hypotheses.** (i) Large sample: $\mathbf Y^{(n)}(0) = \mathbf y_0^{(n)} \to \mathbf y_0 \in \mathbb R_+^d$ with $\|\mathbf y_0\|_1 = 1$. (ii) Asymptotic one-step costs: there are continuous functions $a_j$ and $b_{ij} \ge 1$ such that, for every $\delta > 0$, uniformly over lattice points $\mathbf y$ with all coordinates at least $\delta$,

$$n\big(c^{(n)}(\mathbf e_j \mid \mathbf y) - 1\big) \to a_j(\mathbf y), \qquad c^{(n)}(\mathbf e_j - \mathbf e_i \mid \mathbf y) \to b_{ij}(\mathbf y).$$

**Theorem.** Fix $t \in [0,1)$. Under the true backward dynamics, the processes $s \mapsto \big(C^{(n)}, \mathbf Y^{(n)}, M^{(n)}\big)(\lfloor sn \rfloor)$, $s \in [0,t]$, converge weakly as $n \to \infty$ to $(C, \mathbf Y, M)$, where

- the state is deterministic, $\mathbf Y(s) = \mathbf y_0 (1 - s)$;
- the $M_{ij}$ are independent time-inhomogeneous Poisson processes with intensities $\lambda_{ij}(s) = \theta P_{ij}\, y_{0,i} / (1 - s)$;
- the cost is

$$C(s) = \exp\Big\{ \sum_{i=1}^d y_{0,i}\int_0^s a_i\big(\mathbf y_0 (1-u)\big)\, du \Big\} \prod_{i,j=1}^d \prod_{k=1}^{M_{ij}(s)} b_{ij}\big(\mathbf y_0 (1 - \tau_{ij}^{k})\big),$$

with $\tau_{ij}^k$ the $k$-th jump time of $M_{ij}$.

So for large samples the coalescent forgets its randomness in the lineage counts (a law of large numbers along the ray $\mathbf y_0(1-s)$), keeps finitely many mutation events as Poisson noise, and the cost becomes an exponential functional of these two limits.

## Expansion

A backward step removes one lineage, so after $\lfloor sn \rfloor$ steps the total scaled count is $1 - s + O(1/n)$; coalescence steps happen with probability $1 - O(1/n)$ and occur in each type in proportion to its frequency, which yields the deterministic ray. Mutation steps have probability of order $\theta/\|\mathbf n\|$ per step, i.e. $O(1/n)$, so over $O(n)$ steps they form a Poisson process with the stated intensity. Writing $\log C^{(n)}$ as a sum over steps, coalescence steps contribute $\frac1n a_j + o(1/n)$ each, which sums to the Riemann integral, and each of the finitely many mutation steps contributes $\log b_{ij}$. The proof makes this rigorous by generator convergence for the triple $(C, \mathbf Y, M)$ on compact sets in the interior of the orthant (Ethier–Kurtz), which is why $t < 1$ is fixed and the coordinates stay bounded away from zero.

## Sources

- Martina Favero and Jere Koskela, "Large-sample analysis of cost functionals for inference under the coalescent", *Stochastic Processes and their Applications* 195 (2026), 104894, <https://doi.org/10.1016/j.spa.2026.104894>. Numbering as in the preprint arXiv:2412.06004v2, <https://arxiv.org/abs/2412.06004v2>: Definitions 2.2, 2.4–2.6, Assumptions 1.1, 3.1, 3.2 and Theorem 3.3.
