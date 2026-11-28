# Generic identifiability of large phylogenetic tree mixtures

Let $\mu$ be a group-based or general Markov model on $\kappa$ states and, for an $n$-leaf binary tree $T$, let $\psi^\mu_T:S^\mu_T\to\Delta^{\kappa^n-1}$ be its parametrization of leaf-pattern distributions. For an $r$-tuple $\mathbf T=(T_1,\dots,T_r)$ of $n$-leaf trees the **$r$-tree mixture model** is

$$\psi^\mu_{\mathbf T}(s_1,\dots,s_r,\pi)=\pi_1\psi^\mu_{T_1}(s_1)+\dots+\pi_r\psi^\mu_{T_r}(s_r),\qquad \pi\in\Delta^{r-1}.$$

Tree parameters are generically identifiable on a class of tuples if, for generic parameters, equality of two mixture distributions forces $\mathbf T'=\sigma\cdot\mathbf T$ for a permutation $\sigma$; continuous parameters are generically identifiable if moreover $s'_i=s_{\sigma(i)}$ and $\pi'_i=\pi_{\sigma(i)}$. Let $\mathcal T(r,n,k)$ be the set of $r$-tuples of $n$-leaf binary trees for which there is one leaf tripartition $A|B|C$ with $|A|\ge|B|\ge|C|$ and $|B|\ge k$ that is induced by an inner vertex of every $T_i$.

For a distribution $P$ on $n$ leaves and a split $A|B$ of the leaves, $\mathrm{Flat}_{A|B}(P)$ is the $\kappa^{|A|}\times\kappa^{|B|}$ matrix of joint probabilities with rows indexed by states on $A$ and columns by states on $B$; write $[n-1]=\{1,\dots,n-1\}$. The model $\mu$ has:

- the **rank property** $RP(r,n)$ if for any $n$-leaf trees $T_1,\dots,T_r$ and generic $P_i\in\mathcal M^\mu_{T_i}$ the $\kappa^{n-1}\times r\kappa$ matrix $\big[\mathrm{Flat}_{[n-1]|n}(P_1)\ \cdots\ \mathrm{Flat}_{[n-1]|n}(P_r)\big]$ has rank $r\kappa$ (full column rank);
- the **extended rank property** $ERP(r,n)$ if for any $(n+1)$-leaf tree $T_1$ not containing the split $[n-1]|\{n,n+1\}$, any $n$-leaf trees $T_2,\dots,T_r$ and generic $P_i\in\mathcal M^\mu_{T_i}$, the matrix $\big[\mathrm{Flat}_{[n-1]|\{n,n+1\}}(P_1)\ \mathrm{Flat}_{[n-1]|n}(P_2)\ \cdots\ \mathrm{Flat}_{[n-1]|n}(P_r)\big]$ has rank $(r-1)\kappa+\kappa^2$;
- the property of being **standard** if it is generically identifiable on trees, contains the identity matrix, and contains two transition matrices $M_1,M_2$ such that any two columns of $M_1$, or one column of $M_1$ and one of $M_2$, are linearly independent;
- the **No Shuffling Property** if for any trees $T_1,\dots,T_r$ with $n\ge3$ leaves, generic $P_i\in\mathcal M^\mu_{T_i}$ and generic $\pi\in\Delta^{r-1}$, whenever $\kappa$ (not necessarily distinct) columns of $\big[\pi_1\mathrm{Flat}_{[n-1]|n}(P_1)\ \cdots\ \pi_r\mathrm{Flat}_{[n-1]|n}(P_r)\big]$ form, as a tensor, a distribution in $\mathcal M^\mu_T$ for some tree $T$, all of them come from the same $P_i$.

**Theorem.** Suppose $\mu$ on $\kappa>2$ states is standard, has $RP(r,k)$, $ERP(r,k)$ and the No Shuffling Property, and $r\le\kappa^{k-1}$, $n\ge 2k+1$. Then both tree parameters and continuous parameters of the mixture are generically identifiable on $\mathcal T(r,n,k)$.

**Corollary.** For the Jukes-Cantor, Kimura 2- and 3-parameter, strand symmetric and general Markov models, if $n\ge 2k+1$ and $r\le 2^k-k$ then tree and continuous parameters of $r$-tree mixtures are generically identifiable on $\mathcal T(r,n,k)$. Thus the number of identifiable mixture components grows exponentially in the number of leaves.

## Expansion

At the shared vertex the mixture distribution, viewed as a three-way tensor indexed by the states on $A$, $B$ and $C$, is a sum of $r\kappa$ rank-one terms. The rank properties make two of the three factor matrices full rank and the standard property bounds the Kruskal rank of the third, so Kruskal's theorem recovers the $r\kappa$ rank-one terms up to permutation. The No Shuffling Property groups these terms into the $r$ components, after which each component tree is recovered from flattening ranks of its own distribution (edge invariants) and single-tree identifiability. For Jukes-Cantor the rank properties reduce, after the discrete Fourier transform, to the nonvanishing of Vandermonde-type determinants.

## Sources

- Bryson Kagy, Seth Sullivant, "Identifiability of Large Phylogenetic Mixtures for Many Phylogenetic Model Structures", *Bulletin of Mathematical Biology* 88(11) (2026), 211, Theorem 2.5, Corollary 2.6 and Definitions 6.1, 6.2, 6.4 and 6.6, <https://doi.org/10.1007/s11538-026-01782-5> (preprint arXiv:2508.05832).
