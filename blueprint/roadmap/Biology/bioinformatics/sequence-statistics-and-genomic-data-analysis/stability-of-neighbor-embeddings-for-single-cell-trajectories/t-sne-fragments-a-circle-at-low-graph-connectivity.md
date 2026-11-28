# Conditional distortion blow-up of optimal t-SNE embeddings of a sampled circle

**Setting.** t-SNE embeds points $x_1,\dots,x_n$ (e.g. single-cell expression profiles along a continuous trajectory) as $y_1,\dots,y_n\in\mathbb{R}^2$ by maximizing

$$C^*(y)=\sum_{i\ne j}p_{ij}\log q_{ij},\qquad q_{ij}=\frac{(1+\|y_i-y_j\|^2)^{-1}}{\sum_{k\ne l}(1+\|y_k-y_l\|^2)^{-1}},$$

where the input affinities $p_{ij}$ have an effective neighborhood size (graph connectivity parameter, controlled by perplexity). In the prototypical case of the discrete unit circle $P_n=\{(\cos\frac{2\pi i}{n},\sin\frac{2\pi i}{n})\}_{i\le n}$ take $k$-nearest-neighbor affinities $p_{ij}=1/(2nk)$ for neighbors and $0$ otherwise. A map $\phi$ is **bilipschitz** with scaling $S>0$ and distortion $L\ge1$ if $S\le\|\phi(x)-\phi(x')\|/\|x-x'\|\le SL$ for all $x\ne x'$.

**Theorem (t-SNE artifact).** Let $\phi^*$ be an optimal t-SNE embedding of $P_n$ with these affinities and $k=O(1)$ as $n\to\infty$. If $\phi^*$ is bilipschitz with scaling factor $S(\phi^*)=n^\tau$ for some $0<\tau<1$, then its distortion is unbounded: $L(\phi^*)\to\infty$ as $n\to\infty$. The statement is conditional on both hypotheses, fixed-order connectivity $k=O(1)$ **and** the power-law scaling $S(\phi^*)=n^\tau$; the source states that this scaling behaviour has not been proved, and the theorem concerns only the discrete circle $P_n$.

**Interpretation (not part of the theorem).** Diverging distortion means that some neighbouring pairs are embedded much farther apart than others. The source reads this, together with simulations, as t-SNE fragmenting a closed trajectory into pieces with gaps when connectivity stays fixed; that fragmentation, and any analogue for general smooth closed curves, is an empirical observation and is not implied by the distortion estimate.

**NESS stability scores.** To choose the connectivity parameter, run the embedding $N$ times from random initializations, record for each pair $(j,l)$ the number $K[j,l]$ of runs in which $l$ is among the $k$ nearest embedded neighbors of $j$, and symmetrize $K\leftarrow\max(K,K^\top)$. The local stability of cell $j$ is the $\lambda$-quantile ($\lambda=0.75$ by default) of $\{K[j,l]/N:K[j,l]>0\}$, and the global stability is the mean of the local scores; the connectivity is tuned to make the embedding stable across runs.

## Expansion

With only $O(1)$ attractive neighbors per point, the attraction term of $C^*$ is local while the normalization of $q_{ij}$ acts as a repulsion among all $n^2$ pairs. Heuristically, if the embedding grows like $n^\tau$ with $\tau<1$, consecutive points cannot all stay at the spacing $\asymp n^{\tau-1}$ of a uniform scaled circle without the repulsion term outweighing the gain from attraction, so, under the scaling hypothesis, an optimal embedding must place some neighbors at much larger distances than others: the distortion diverges. Increasing the connectivity with $n$ removes the mechanism. In data, the fragmentation observed empirically shows up as low stability across random initializations.

## Sources

- Rong Ma, Xi Li, Jingyuan Hu and Bin Yu, "Uncovering smooth structures in single-cell data with PCS-guided neighbor embeddings", arXiv:2506.22228 (2025), Theorem 1 (t-SNE artifact) with its proof in the Supplement, and the NESS score definitions in Section 2, <https://doi.org/10.48550/arXiv.2506.22228>.
