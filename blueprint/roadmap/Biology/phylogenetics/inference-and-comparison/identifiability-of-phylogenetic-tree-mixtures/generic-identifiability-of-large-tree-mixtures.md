# Generic identifiability of large phylogenetic tree mixtures

Let $\mu$ be a group-based or general Markov model on $\kappa$ states and, for an $n$-leaf binary tree $T$, let $\psi^\mu_T:S^\mu_T\to\Delta^{\kappa^n-1}$ be its parametrization of leaf-pattern distributions. For an $r$-tuple $\mathbf T=(T_1,\dots,T_r)$ of $n$-leaf trees the **$r$-tree mixture model** is

$$\psi^\mu_{\mathbf T}(s_1,\dots,s_r,\pi)=\pi_1\psi^\mu_{T_1}(s_1)+\dots+\pi_r\psi^\mu_{T_r}(s_r),\qquad \pi\in\Delta^{r-1}.$$

Tree parameters are generically identifiable on a class of tuples if, for generic parameters, equality of two mixture distributions forces $\mathbf T'=\sigma\cdot\mathbf T$ for a permutation $\sigma$; continuous parameters are generically identifiable if moreover $s'_i=s_{\sigma(i)}$ and $\pi'_i=\pi_{\sigma(i)}$. Let $\mathcal T(r,n,k)$ be the set of $r$-tuples of $n$-leaf binary trees for which there is one leaf tripartition $A|B|C$ with $|A|\ge|B|\ge|C|$ and $|B|\ge k$ that is induced by an inner vertex of every $T_i$.

**Theorem.** Suppose $\mu$ on $\kappa>2$ states is standard (generically identifiable on single trees, containing the identity, and containing two transition matrices with suitably independent columns), has the rank property $RP(r,k)$ (stacking the leaf-given-root conditional matrices of $r$ generic $k$-leaf tree distributions gives full row rank $\kappa r$), the extended rank property $ERP(r,k)$, and the No Shuffling Property (rows of single-leaf flattenings from different mixture components cannot be recombined into a distribution of the model unless they come from one component), and $r\le\kappa^{k-1}$, $n\ge 2k+1$. Then both tree parameters and continuous parameters of the mixture are generically identifiable on $\mathcal T(r,n,k)$.

**Corollary.** For the Jukes-Cantor, Kimura 2- and 3-parameter, strand symmetric and general Markov models, if $n\ge 2k+1$ and $r\le 2^k-k$ then tree and continuous parameters of $r$-tree mixtures are generically identifiable on $\mathcal T(r,n,k)$. Thus the number of identifiable mixture components grows exponentially in the number of leaves.

## Expansion

At the shared vertex the mixture distribution, viewed as a three-way tensor indexed by the states on $A$, $B$ and $C$, is a sum of $r\kappa$ rank-one terms. The rank properties make two of the three factor matrices full rank and the standard property bounds the Kruskal rank of the third, so Kruskal's theorem recovers the $r\kappa$ rank-one terms up to permutation. The No Shuffling Property groups these terms into the $r$ components, after which each component tree is recovered from flattening ranks of its own distribution (edge invariants) and single-tree identifiability. For Jukes-Cantor the rank properties reduce, after the discrete Fourier transform, to the nonvanishing of Vandermonde-type determinants.

## Sources

- Bryson Kagy, Seth Sullivant, "Identifiability of Large Phylogenetic Mixtures for Many Phylogenetic Model Structures", *Bulletin of Mathematical Biology* 88(11) (2026), 211, Theorem 2.5 and Corollary 2.6, <https://doi.org/10.1007/s11538-026-01782-5> (preprint arXiv:2508.05832).
