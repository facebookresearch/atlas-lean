# Multi-type Cannings models and their exchangeable coalescent limits

**Model.** Individuals carry a type in a countable set $E$; subpopulation $k$ has constant size $N_k$. In each generation, the $i$-th individual of type $k$ has $\nu_{k,\ell,i}$ offspring of type $\ell$, with $\sum_k\sum_{i\le N_k}\nu_{k,\ell,i}=N_\ell$ for every $\ell$, i.i.d. across generations. The offspring numbers are assumed *jointly exchangeable* (A): for all permutations $\pi_{k,\ell}$ of $[N_k]$, $(\nu_{k,\ell,\pi_{k,\ell}(i)})$ has the same law as $(\nu_{k,\ell,i})$. This allows the between-type offspring totals $N_{k,\ell}$ (migration, mutation or type switching at reproduction) to be random. For a sample of $n$ individuals, the multi-type ancestral process $\mathcal A^{(n,N)}_r$ takes values in partitions of $[n]$ whose blocks are labelled by the type of the common ancestor $r$ generations back. Its transition probabilities from $\pi$ to a coarser $\pi'$ are

$$p_{\pi,\pi'}=\frac{\prod_k(N_k)_{j_k}}{\prod_\ell(N_\ell)_{i_\ell}}\,\mathbb E\Big[\prod_{k,\ell}\prod_{s=1}^{j_k}(\nu_{k,\ell,s})_{i_{k,\ell,s}}\Big]=:\Phi_j(T),$$

where $i_\ell$ is the number of $\ell$-blocks of $\pi$, $j_k$ the number of $k$-blocks of $\pi'$, and the tensor $T=(i_{k,\ell,s})$ records how many $\ell$-blocks merge into the $s$-th $k$-block.

**Theorem (consistency and limits).** Under (A):
1. The rate functions $\Phi_j$ satisfy a multi-type consistency identity and are monotone, so restricting the $n$-sample ancestral process to $m\le n$ individuals gives the $m$-sample process (natural coupling).
2. If $\Phi^{(N)}_j(T)\to\phi_j(T)$ as $N_{\min}=\min_kN_k\to\infty$ for all non-identity tensors, the ancestral process converges to a discrete-time Markov chain with transition probabilities $\phi_j(T)$.
3. If there are $c_N\to0$ with $\Phi^{(N)}_j(T)/c_N\to\phi_j(T)$, then $(\mathcal A^{(n,N)}_{\lfloor t/c_N\rfloor})_{t\ge0}$ converges in $D([0,\infty))$ to a continuous-time Markov chain with off-diagonal rates $q_{\pi,\pi'}=\phi_j(T)$; by consistency these chains extend, via Kolmogorov's theorem, to a *multi-type exchangeable coalescent* on labelled partitions of $\mathbb N$.

**Theorem (integral representation).** If the rates are concentrated on diagonal tensors (mergers produce a block of the same type as the merging blocks), there are $a_k\ge0$ and a finite measure $\Xi$ on $(\Delta\setminus\{0\})\times E^{\mathbb N}$, $\Delta$ the infinite simplex, such that

$$\phi_j(T)=\sum_ka_k\mathbf 1_{\{j=e_k,\,i_{k,1}=2\}}+\int\sum_{(m_{k,s})\ \text{distinct}}\ \prod_k\prod_{s=1}^{j_k}x_{m_{k,s}}^{i_{k,s}}\mathbf 1_{\{k\}}(y_{m_{k,s}})\ \frac{\Xi(d(x,y))}{(x,x)},$$

a typed analogue of the Schweinsberg $\Xi$-coalescent: Kingman-type pair mergers within each type at rate $a_k$, plus simultaneous multiple mergers driven by paintbox frequencies $x$ with type labels $y$.

## Depends on

- [Cannings model of a haploid population](../cannings-models/cannings-model.md)
- [Möhle–Sagitov classification of the coalescent limits of Cannings models](mohle-sagitov-classification-limiting-merger-rat.md)

## Expansion

Joint exchangeability within each subpopulation implies the random assignment of parents to offspring of each type, which yields the factorial-moment formula and, by summing over the possible placements of one extra sampled individual, the consistency identity. Consistency is the multi-type replacement for the sampling consistency of single-type Cannings models, and it makes the limiting family of finite chains projective. Worked examples are multi-type Wright–Fisher models and a multi-type pure mutation model without merging events, in which lineages only change type.

## Sources

- M. Flamm, M. Möhle, "On the genealogy of multi-type Cannings models and their limiting exchangeable coalescents", arXiv:2504.10744 (2025), model assumption (A) and the transition formula (introduction and ancestral-structure sections), Proposition 1, Corollaries 1–2, Theorems 1–3, Proposition 2 and the examples section (multi-type Wright–Fisher and pure mutation models), <https://doi.org/10.48550/arXiv.2504.10744>.
