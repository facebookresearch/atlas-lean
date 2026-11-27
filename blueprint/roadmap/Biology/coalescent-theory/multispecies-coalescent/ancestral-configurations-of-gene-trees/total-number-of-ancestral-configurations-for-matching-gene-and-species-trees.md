# Total number of ancestral configurations for matching gene and species trees

**Setting.** Let a gene-tree labeled topology $G$ and a species tree $S$ have the same labeled topology $t$ with $n$ leaves. With time running from the leaves to the root, an *ancestral configuration* at a node $k$ of $S$ is a set of gene lineages that can be present at $k$, at the time point immediately before node $k$ (that is, immediately below it), in some realization of $G$ in $S$, each lineage named by its immediate descendant node of $G$. The single lineage $\{k\}$ is therefore not a configuration at $k$, and a leaf has no configurations. These configurations index the terms in recursive formulas for the gene-tree probability under the multispecies coalescent. For matching trees, the number $R(t)$ of root configurations satisfies $R(\bullet)=0$ for a leaf and

$$R(t)=\big(R(t_L)+1\big)\big(R(t_R)+1\big)$$

for $t$ with root subtrees $t_L,t_R$. The *total number* is $T(t)=\sum_{k}R(t^k)$, summed over internal nodes $k$. Let $T_n$ be the total for a random labeled topology of size $n$.

**Theorem.**

1. *(Uniform model.)* For a uniformly random labeled topology,

    $$\mathbb E[T_n]\sim\sqrt6\,(4/3)^n\sim2\,\mathbb E[R_n],\qquad \mathbb V[T_n]\sim\frac{2}{17}(15+11\sqrt2)\sqrt{\frac{7(11-\sqrt2)}{34}}\Big[\frac{4}{7(8\sqrt2-11)}\Big]^n,$$

    and $\mathbb V[T_n]\sim\mathbb E[T_n^2]$.

2. *(Yule model.)* For a Yule–Harding random labeled topology,

    $$\mathbb E[T_n]\sim\mathbb E[R_n]\sim\Big(\frac1{1-e^{-2\pi\sqrt3/9}}\Big)^n,\qquad \mathbb V[T_n]\sim\mathbb V[R_n]\sim(2.0449954971\ldots)^n,$$

    the correlation of $T_n$ and $R_n$ tends to $1$, and $\log T_n$ satisfies a central limit theorem with $\mathbb E[\log T_n]\sim\mu n$ and $\mathbb V[\log T_n]\sim\sigma^2n$, where $(\mu,\sigma^2)\approx(0.351,0.008)$.

## Depends on

- [Cartesian product decomposition of the ancestral configuration lattice](../lattices-of-ancestral-configurations/cartesian-product-decomposition-of-the-ancestral-configuration-lattice.md)

## Expansion

The distribution of the configuration counts depends only on the shape of the tree. Uniform labeled topologies correspond to uniform ordered unlabeled (Catalan) trees, and Yule topologies correspond to uniform ordered histories (increasing trees). Under both models the root split $I_n$ has an explicit law: $\mathbb P[I_n=j]=C_{j-1}C_{n-1-j}/C_{n-1}$ for the uniform model and uniform on $\{1,\dots,n-1\}$ for the Yule model. This gives distributional recursions $T_n\overset d=T_{I_n}+T^*_{n-I_n}+R_n$ and $R_n+1\overset d=(R_{I_n}+1)(R^*_{n-I_n}+1)+1$. Generating functions and singularity analysis solve the uniform case. The Yule case leads to a Riccati-type differential equation whose blow-up point $\alpha_1=1-e^{-2\pi\sqrt3/9}$ sets the exponential growth rate. The counts grow exponentially but much more slowly than the number of labeled histories. Under the Yule model, a typical species tree yields about $1.42^n$ configurations, which bounds the cost of exact gene-tree probability computation.

## Sources

- Filippo Disanto, Michael Fuchs, Chun-Yen Huang, Ariel R. Paningbatan and Noah A. Rosenberg, "The distributions under two species-tree models of the total number of ancestral configurations for matching gene trees and species trees", *Advances in Applied Mathematics* 152 (2024), 102594, <https://doi.org/10.1016/j.aam.2023.102594>. Numbering as in the preprint arXiv:2305.04192v1, <https://arxiv.org/abs/2305.04192v1>: Lemma 1 (reduction to unlabeled shapes), Lemma 2 and Lemma 7 (distributional recursions), Proposition 3 and Theorem 6 (uniform model), Propositions 8–9 and Theorem 10 (Yule model and log-normal CLT).
