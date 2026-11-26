# Generic identifiability of the rooted tree under the CFN molecular clock model

**Model.** In the Cavender–Farris–Neyman (CFN) model a binary character evolves on a rooted binary tree $T$ with $n$ leaves: the root state is uniform on $\{0,1\}$ and along each edge $e$ the state flips with probability $\tfrac12(1 - e^{-2t_e})$, where $t_e > 0$ is the edge length. The model $\mathcal M_T$ is the set of leaf-pattern distributions in the probability simplex $\Delta_{2^n-1}$. A tree is *ultrametric* if, for every internal node $v$, all root-to-leaf path lengths from $v$ to leaves below it are equal (a molecular clock). The CFN-MC model $\mathcal M_T$ consists of the distributions arising from ultrametric edge lengths on $T$.

Because the CFN model is group-based and time-reversible, without a clock only the unrooted topology is identifiable.

**Definition.** The rooted tree parameter is *generically identifiable* if for every pair of distinct rooted trees $T^1 \ne T^2$ with $n$ leaves,

$$\dim(\mathcal M_{T^1}\cap\mathcal M_{T^2}) < \min\{\dim\mathcal M_{T^1}, \dim\mathcal M_{T^2}\}.$$

**Theorem.** The rooted tree parameter of the CFN model with a molecular clock is generically identifiable, for every number of leaves $n$.

**Key proposition.** In Fourier coordinates $q_{\mathbf g}$ (indexed by subsets of leaves), for leaves $i,j,k,\ell$ (not necessarily distinct) the most recent common ancestors satisfy $\mathrm{lca}(i,k) = \mathrm{lca}(j,\ell)$ if and only if the linear binomial $q_{\mathbf 1_{i,k}} - q_{\mathbf 1_{j,\ell}}$ lies in the vanishing ideal $I_T$ of the CFN-MC model on $T$.

## Expansion

In Fourier coordinates, $q_{\mathbf 1_{i,k}} = E[(-1)^{X_i + X_k}] = e^{-2d(i,k)}$, where $d(i,k)$ is the path length between leaves $i$ and $k$. Under a clock $d(i,k) = 2(h - \mathrm{depth}(\mathrm{lca}(i,k)))$, so two pairwise coordinates agree on the whole model exactly when the two pairs have the same most recent common ancestor, giving the linear binomials. Distinct rooted binary trees on the same leaves differ in some pair of rooted triples, so some binomial $q_{\mathbf 1_{i,k}} - q_{\mathbf 1_{j,\ell}}$ lies in $I_{T^1}$ but not in $I_{T^2}$, and conversely. Since the models are irreducible varieties (prime ideals), an ideal-membership separation of this kind forces $\dim(\mathcal M_{T^1}\cap\mathcal M_{T^2})$ to drop below both dimensions (the standard algebraic-statistics criterion for generic identifiability), which proves the theorem.

## Sources

- Jane Ivy Coons and Benjamin Hollering, "Identifiability of the Rooted Tree Parameter under the Cavender-Farris-Neyman Model with a Molecular Clock", arXiv:2303.12058 (2023), main theorem, definitions of ultrametric trees, CFN-MC model and generic identifiability, the ideal-separation proposition and the linear-forms proposition, <https://doi.org/10.48550/arXiv.2303.12058>.
