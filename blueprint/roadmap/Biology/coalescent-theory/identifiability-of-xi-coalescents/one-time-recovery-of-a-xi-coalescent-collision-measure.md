# One-time recovery of a Ξ-coalescent collision measure

**Setting.** Let $\mathcal K = \{p_1 \ge p_2 \ge \dots \ge 0 : \sum_j p_j \le 1\}$ be the Kingman simplex with the product topology, and write $V_2(p) = \sum_j p_j^2$. A finite collision measure $\Xi$ on $\mathcal K$ is split as $\Xi = a\delta_0 + \Xi_0$ with $\Xi_0(\{0\}) = 0$. The atom at the zero partition is the Kingman component. A specified collision of $r$ groups of sizes $k_1, \dots, k_r \ge 2$ among $b = k_1 + \dots + k_r + s$ blocks, leaving $s$ singletons, happens at Schweinsberg's rate

$$\lambda^\Xi_{b;k_1,\dots,k_r;s} = a\,\mathbf 1_{\{r=1,\,k_1=2\}} + \int_{\mathcal K\setminus\{0\}} \sum_{\ell=0}^{s}\binom{s}{\ell}(1 - |x|)^{s-\ell} \sum_{\substack{i_1,\dots,i_{r+\ell}\\ \text{distinct}}} x_{i_1}^{k_1}\cdots x_{i_r}^{k_r}\,x_{i_{r+1}}\cdots x_{i_{r+\ell}}\,\frac{\Xi_0(dx)}{V_2(x)},$$

with $|x| = \sum_i x_i$. Let $P^\Xi(t) \in \mathcal K$ be the ranked asymptotic block frequencies at time $t$ of the $\Xi$-coalescent started from singletons, with missing mass as dust. By Kingman's paintbox theorem, the law of $P^\Xi(t)$ is the same information as the exchangeable partition probability functions of all finite restrictions at time $t$.

**Theorem.** For every known $t > 0$, the map

$$\Xi \longmapsto \mathcal L\big(P^\Xi(t)\big)$$

is a topological embedding of the finite nonnegative collision measures on $\mathcal K$ into the probability measures on $\mathcal K$, both with the weak topology. Moreover

$$1 - \mathbb E\,V_2\big(P^\Xi(t)\big) = e^{-t\,\Xi(\mathcal K)} .$$

So one fixed-time snapshot of the genealogy's partition law identifies the collision measure. With an unknown time, the snapshot identifies exactly the product $t\Xi$, and it identifies $t$ itself under the normalization $\Xi(\mathcal K) = 1$.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescent-theory/coalescents/xi-coalescents-simultaneous-multiple-collisions.md)
- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../coalescent-theory/coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)

## Expansion

Work level by level on the partitions $\mathcal S_n$ of $[n]$. Let $r_n$ be the row of rates out of the singleton partition $0_n$ and $R_n$ its total. By consistency and exchangeability, a state with $b$ blocks evolves as a coalescent on $[b]$. So every entry of the generator after the first collision (the subgenerator $B_n$ on $\mathcal S_n \setminus \{0_n\}$) equals a coordinate of some $r_b$, $b < n$. Ordered by refinement, $B_n$ is triangular. Variation of constants writes the observed row of transition probabilities out of $0_n$ at time $t$ as the unknown row $r_n$ times a triangular matrix with strictly positive diagonal. Inverting it gives $r_n$, and induction on $n$ recovers the whole collision-rate array, from which Schweinsberg's representation theorem recovers $\Xi$. The pair identity comes from the two-sample restriction: two labels are still apart at time $t$ with probability $e^{-t\Xi(\mathcal K)}$.

## Sources

- J. Lenzi, "One marked-sum law determines random mass partitions and $\Xi$-coalescents", arXiv:2609.12790 (2026), Theorem 1.3, Lemma 4.1, Theorem 4.2, <https://doi.org/10.48550/arXiv.2609.12790>.
- J. Schweinsberg, "Coalescents with simultaneous multiple collisions", Electronic Journal of Probability 5 (2000), Theorem 2 and formula (11).
