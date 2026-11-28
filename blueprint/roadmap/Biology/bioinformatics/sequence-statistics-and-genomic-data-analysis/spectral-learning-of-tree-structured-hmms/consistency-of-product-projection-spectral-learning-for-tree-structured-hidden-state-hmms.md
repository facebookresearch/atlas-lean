# Consistency of product-projection spectral learning for tree-structured hidden-state HMMs

**Model (tree HMM for comparative epigenomics).** Chromatin-mark sequences from $D$ related cell types are modeled jointly along genomic position $t$. A directed tree $G=(V,E)$ of known shape has one node per cell type; at each position the hidden state $z_t=(z^u_t)_{u\in V}$, $z^u_t\in[m]$ (regulatory state), and the observation $x_t=(x^u_t)_{u\in V}$, $x^u_t\in[n]$. The parameters are emission matrices $O^u=P(x^u_t\mid z^u_t)$, transition tensors $T^u=P(z^u_{t+1}\mid z^u_t,z^{\pi(u)}_{t+1})$ (each node's state depends on its own previous state and its parent's current state) and initial laws $W^u=P(z^u_1\mid z^{\pi(u)}_1)$. Given $z^u_t$, $x^u_t$ is independent of all other variables.

**Assumptions.** (Node-wise rank) every $O^u$ has rank $m$ and the pair co-occurrence matrix $P^{u,u}_{2,1}=\mathbb{E}[x^u_2\otimes x^u_1]$ has rank $m$. (Path-wise rank) for every $u$, with $H_u$ the root-to-$u$ path, the meta-observation co-occurrence matrix $P^{H_u,H_u}_{1,2}$ has rank $m^{|H_u|}$.

**Algorithm (product projections).** For each node take the top $m$ left singular vectors $\hat U^u$ of $\hat P^{u,u}_{1,2}$ and project path meta-observations onto $\hat U^{H_u}=\bigotimes_{v\in H_u}\hat U^v$ instead of the full $n^{|H_u|}$-dimensional space. Symmetrize the projected second- and third-order co-occurrences of $(x_1,x_2,x_3)$, orthogonalize and decompose the projected third-order tensor (the tensor power method), and undo the projection: $\hat O^u=\hat U^u\hat\Theta^u$.

**Theorem (consistency).** Run on the first three observations of $N$ i.i.d. sequences, for every node $u$ there is, with high probability, an $m\times m$ permutation matrix $\Pi^u$ with $\|O^u-\hat O^u\Pi^u\|\le\varepsilon(N)$ (right multiplication relabels the columns, that is, the hidden states), where $\varepsilon(N)\to0$ as $N\to\infty$. The permutations are globally consistent across nodes, so transition tensors and initial laws are also recovered, and finite-sample bounds hold.

## Expansion

The range of the path-level emission matrix $O^{H_u}=\bigotimes_{v\in H_u}O^v$ is contained in $\bigotimes_v\operatorname{range}(O^v)$, which each single-node SVD estimates, so projecting onto the product of node-wise subspaces loses nothing while replacing $n^{|H_u|}$-dimensional moments by $m^{|H_u|}$-dimensional ones. The cost then depends on the depth of the tree through $m^{|H_u|}$ rather than exponentially on the number of cell types, and the tree depth is small in epigenomic designs. Because each node's moments are symmetrized with the same root-to-node meta-state, the hidden-state labels are aligned across nodes, which plain per-node spectral learning would not guarantee. On real data from nine human cell types the method was much faster than EM.

## Sources

- Chicheng Zhang, Jimin Song, Kevin C Chen and Kamalika Chaudhuri, "Spectral Learning of Large Structured HMMs for Comparative Epigenomics", arXiv:1506.01744 (2015), Section 2 (model), Algorithm 1, Assumptions 1–2, Theorem 1 and the finite-sample theorem in the Appendix, <https://doi.org/10.48550/arXiv.1506.01744>.
