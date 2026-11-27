# Uniform sampling of transmission trees on a phylogeny

Use the notation of [Counting transmission trees compatible with a phylogeny](counting-transmission-trees-compatible-with-a-phylogeny.md): $T$ is a rooted binary phylogeny with root $r$, children $r_L, r_R$ and tips $t_1, \dots, t_n$; $\mathcal{P}(T)$ is the set of admissible partitions. Let $\mathcal{P}_i(T) \subseteq \mathcal{P}(T)$ be the partitions in which $r$ lies in the same part as $t_i$, so $\sum_i |\mathcal{P}_i(T)| = |\mathcal{P}(T)|$, and $|\mathcal{P}_1(T)| = 1$ when $T$ is the single tip $t_1$.

**Proposition 4.** If $T$ has at least two tips, then for each $i$,

$$|\mathcal{P}_i(T)| = \begin{cases} |\mathcal{P}_i(T_{r_L})|\;|\mathcal{P}(T_{r_R}^{*})| & \text{if } t_i \in T_{r_L},\\ |\mathcal{P}_i(T_{r_R})|\;|\mathcal{P}(T_{r_L}^{*})| & \text{if } t_i \in T_{r_R}.\end{cases}$$

All values $|\mathcal{P}_i(T_u)|$ over internal nodes $u$ are computed by one postorder traversal in $O(n^2)$ time.

**Sampler.** Assign $r$ to the part of $t_i$ with probability $|\mathcal{P}_i(T)|/|\mathcal{P}(T)|$. Then traverse in preorder: when a node $u$ is reached whose parent is in the part of $t_i$, put $u$ in the same part if $t_i$ descends from $u$ (forced by connectedness); otherwise put $u$ in its parent's part with probability $(|\mathcal{P}(T_u^*)| - |\mathcal{P}(T_u)|)/|\mathcal{P}(T_u^*)|$, and in the part of tip $t_j$ of $T_u$ with probability $|\mathcal{P}_j(T_u)|/|\mathcal{P}(T_u^*)|$. The output is a uniformly distributed element of $\mathcal{P}(T)$, and each sample costs $O(n)$ after preprocessing.

## Depends on

- [Counting transmission trees compatible with a phylogeny](counting-transmission-trees-compatible-with-a-phylogeny.md)

## Expansion

If $r$ shares $t_i$'s part and $t_i$ lies in the left subtree, the left subtree must be partitioned with its root also in $t_i$'s part, counted by $|\mathcal{P}_i(T_{r_L})|$, while the right subtree's root is free to join $r$'s part or not, counted by $|\mathcal{P}(T_{r_R}^*)|$; this is Proposition 4. The sampler is a sequential decomposition of the uniform law: at each node, the conditional probability of each choice equals the number of admissible completions consistent with it divided by the number consistent with the choices so far, and these counts are exactly the precomputed quantities. The same recursions extend to incomplete sampling (unsampled hosts), several samples per host, and bounds on infectious periods, giving a fast reference distribution for comparing model-based reconstructions of who infected whom.

## Sources

- M. D. Hall, C. Colijn, "Transmission trees on a known pathogen phylogeny: enumeration and sampling", Molecular Biology and Evolution 36(6) (2019) 1333–1343, sections "Enumeration of Partitions with a Known Root Part" (Proposition 4) and "Sampling Uniformly", <https://doi.org/10.1093/molbev/msz058>, PMCID PMC6526902.
