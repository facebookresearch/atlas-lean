# Local limits of random simplex networks

**Setting.** Let $\mathcal N_n$ be a uniformly random simplex tree-child network on $n$ taxa: a planted binary phylogenetic network that is tree-child (each non-leaf vertex has a tree-vertex or leaf child) and one-component (each reticulation's unique child is a leaf). Local weak convergence of a rooted graph means convergence in distribution of every finite-radius neighbourhood of the root, up to isomorphism of rooted directed graphs.

**Theorem (around the root).** There is an infinite deterministic network $\hat{\mathcal N}$ with $\mathcal N_n\to\hat{\mathcal N}$ locally at the root.

**Theorem (around typical vertices).** There are (deterministic) rooted networks $(\hat{\mathcal L},p_0)$, $(\hat{\mathcal R},\rho_0)$, $(\hat{\mathcal N}^{\rm lf},\ell_0)$ such that $\mathcal N_n$ rooted at a uniform tree vertex, a uniform reticulation, or a uniform leaf converges locally to them, respectively. If $v_n$ is a uniform vertex of $\mathcal N_n$, then $(\mathcal N_n,v_n)$ converges locally to the mixture

$$(N^*,v^*)\ \overset{d}{=}\ \begin{cases}(\hat{\mathcal L},p_0)&\text{with probability }1/2,\\ (\hat{\mathcal R},\rho_0)&\text{with probability }1/4,\\ (\hat{\mathcal N}^{\rm lf},\ell_0)&\text{with probability }1/4,\end{cases}$$

the weights being the asymptotic proportions of tree vertices, reticulations and leaves.

**Theorem (quenched version).** For every radius $R\ge0$ and finite rooted directed graph $G$, the fraction of tree vertices (respectively reticulations, leaves) whose radius-$R$ neighbourhood is isomorphic to $G$ converges in probability to the probability of the same event in $(\hat{\mathcal L},p_0)$ (respectively $(\hat{\mathcal R},\rho_0)$, $(\hat{\mathcal N}^{\rm lf},\ell_0)$).

## Expansion

Only order $\sqrt n$ leaves have a tree-vertex parent, so almost every leaf hangs below a reticulation and, since each reticulation has exactly one leaf child, reticulations and leaves are asymptotically equinumerous. Counting in- and out-degrees in a planted binary network with $t$ tree vertices, $r$ reticulations and $\ell$ leaves gives $1+2t+r=t+2r+\ell$, i.e. $t=r+\ell-1$, hence the proportions $1/2,1/4,1/4$. The limit $(\hat{\mathcal R},\rho_0)$ consists of two disjoint decorated spines meeting at a common child reticulation that carries a pendant leaf, and $(\hat{\mathcal N}^{\rm lf},\ell_0)$ is $\hat{\mathcal R}$ re-rooted at that leaf; the two parents of a typical reticulation are far apart in the network, which is why locally they appear on disjoint spines. Although $\mathcal N_n$ is random, each type-specific limit is deterministic; only the mixture over vertex types is random.

## Sources

- Víctor J. Macià, Benedikt Stufler, "Limit laws of random simplex tree-child networks", arXiv:2607.15370: Theorems 1.6–1.11 and Corollary 1.12 (local limits at the root, at typical vertices of each type, at a uniform vertex, and quenched versions). <https://doi.org/10.48550/arXiv.2607.15370>
