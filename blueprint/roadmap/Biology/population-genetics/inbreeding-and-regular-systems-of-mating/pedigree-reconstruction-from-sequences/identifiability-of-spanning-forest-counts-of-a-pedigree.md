# Identifiability of spanning-forest counts of a pedigree under recombination and mutation

**Pedigrees.** A pedigree $P$ on a set $X$ of extant individuals is a directed acyclic graph in which every vertex has in-degree $0$ (founders) or $2$ (two parents), and $X$ is the set of vertices of out-degree $0$; two pedigrees are isomorphic if they are isomorphic as graphs by a map fixing $X$ pointwise. A **spanning forest** $G$ of $P$ keeps exactly one of the two parental arcs at every non-founder vertex; there are $2^{e(P)/2}$ of them. Each spanning forest contains a unique directed $X$-forest (the ancestry of $X$ in $G$, rooted at founders), whose underlying unrooted forest with leaf set $X$ is denoted $T_u(G)$. For an undirected $X$-forest $T$ let $n(G > T : P)$ be the number of spanning forests $G$ with $T_u(G) \cong T$.

**Model RM$(p,\mu)$.** Founders receive i.i.d. uniform sequences in $\Sigma^L$. A child $u$ of $v$ and $w$ copies, site by site, from the parent indicated by a stationary two-state Markov chain $X_1, X_2,\dots$ on $\{v,w\}$ with switching (crossover) probability $p$ and $\mathbb P(X_1 = v) = 1/2$; each copied symbol is then replaced by each other symbol with probability $\mu$ (so it is kept with probability $1 - (|\Sigma|-1)\mu$). Model R is the case $\mu = 0$; Model M$(\mu)$ is the mutation process alone on a fixed forest.

**Theorem.**

1. (Single sites are forest mixtures.) If $e(P) = 2e$, the $k$-th column $C_k$ of the alignment of extant sequences has, for every character $C\in\Sigma^X$,

$$\mathbb P\{C_k = C \mid P, \mathrm{RM}(p,\mu)\} = \sum_{T} \frac{n(G > T : P)}{2^{e}}\ \mathbb P\{C \mid T, \mathrm M(\mu)\},$$

the sum running over isomorphism classes of undirected $X$-forests of $P$; in particular it does not depend on $k$.
2. (Forests are identifiable under mutation.) For every $\mu \in (0, 1/|\Sigma|)$ and undirected $X$-forests $T_1, T_2$ with a bounded number of edges, if $\mathbb P\{C\mid T_1, \mathrm M(\mu)\} = \mathbb P\{C\mid T_2, \mathrm M(\mu)\}$ for all characters $C$, then $T_1 \cong T_2$.
3. (Counting forest sequences.) Let $P$ and $Q$ be pedigrees with $e(P) = e(Q) = 2e$ arcs and let $\mathbf T = (T_1,\dots,T_m)$ be a sequence of undirected $X$-forests with consecutive terms non-isomorphic. For every $\mu \in (0,1/|\Sigma|)$ there is $p_0 = p_0(e,m,\mu) \in (0,1)$ such that for all $p\in(0,p_0)$: if $P$ and $Q$ induce the same distribution on alignments of every length $L$ under RM$(p,\mu)$, then $n(\mathbf G > \mathbf T : P) = n(\mathbf G > \mathbf T : Q)$, where $n(\mathbf G > \mathbf T : P)$ counts sequences of spanning forests $G_1,\dots,G_m$ of $P$ with $T_u(G_i)\cong T_i$ and consecutive $G_i$ differing by a single recombination. In particular $P$ and $Q$ have the same number of spanning forests of each $X$-forest type.

In particular, the non-reconstructible pedigree pairs constructed in Thatte (2008), *SIAM Journal on Discrete Mathematics* 22, that are not distinguished by their collections of extant subpedigrees are distinguished from the alignment distribution under RM (Thatte Corollary 5.15), although equal $X$-forest counts alone do not distinguish all pedigree pairs.

## Depends on

- [Pedigree kinship and inbreeding](../../../quantitative-genetics/pedigree-kinship-and-inbreeding/README.md)

## Expansion

Along the sequence, the vector of parental choices at all non-founder vertices is a Markov chain on spanning forests, each vertex switching parent with probability $p$ between adjacent sites; given the spanning forest at a site, the extant column is distributed as Model M on its $X$-forest. Hence the alignment is a hidden Markov model with hidden states the spanning forests, and item 1 is its stationary one-site marginal, every spanning forest having probability $2^{-e}$. Item 2 is a phylogenetic identifiability statement for the symmetric mutation model on forests. For item 3, when $p$ is small long runs of sites share one spanning forest; concatenations of long blocks, each typical for a given forest $T_i$, have probabilities whose leading term in $p$ is $n(\mathbf G > \mathbf T : P)$ times a factor depending only on $\mathbf T$, $\mu$ and block lengths, and the consistency of forest classification from block frequencies separates these terms.

## Sources

- Bhalchandra D. Thatte, "Reconstructing pedigrees: some identifiability questions for a recombination-mutation model", *Journal of Mathematical Biology* 66 (2013), 37–74, <https://doi.org/10.1007/s00285-011-0503-8>; preprint arXiv:1008.0153, <https://doi.org/10.48550/arXiv.1008.0153>. Numbering of the arXiv version: Section 2 (pedigrees, spanning forests, $X$-forests), Section 3 (Models R, RM, M), Proposition 4.1, Theorem 5.1, Corollary 5.3, Theorem 5.13, Corollaries 5.14–5.15.
