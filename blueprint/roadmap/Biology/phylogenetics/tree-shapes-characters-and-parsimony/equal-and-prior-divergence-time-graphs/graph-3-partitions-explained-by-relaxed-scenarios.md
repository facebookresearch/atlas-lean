# Graph 3-partitions explained by relaxed scenarios

**Setting.** A *time map* for a rooted tree $T$ is a map $\tau_T : V(T) \to \mathbb{R}$ with $\tau_T(x) < \tau_T(y)$ whenever $x$ is a proper descendant of $y$. A *relaxed scenario* $\mathscr{S} = (T, S, \sigma, \mu, \tau_T, \tau_S)$ consists of a dated gene tree $(T,\tau_T)$, a dated species tree $(S,\tau_S)$, a leaf coloring $\sigma : L(T) \to M \subseteq L(S)$ and a map $\mu : V(T) \to V(S) \cup E(S)$ such that the planted roots correspond, leaves map to leaves with $\mu(x) = \sigma(x)$, $\tau_S(\mu(x)) = \tau_T(x)$ whenever $\mu(x) \in V(S)$, and $\tau_S(v) < \tau_T(x) < \tau_S(u)$ whenever $\mu(x) = uv \in E(S)$. No ancestry constraint is imposed, so horizontal gene transfer (HGT) is allowed.

For distinct genes $x, y \in L(T)$ compare the gene divergence time $\tau_T(\mathrm{lca}_T(x,y))$ with the species divergence time $\tau_S(\mathrm{lca}_S(\sigma(x),\sigma(y)))$. The pair $xy$ is an edge of the *later-divergence-time* graph $G_<$, the *equal-divergence-time* (EDT) graph $G_=$, or the *prior-divergence-time* (PDT) graph $G_>$ according as the comparison $\tau_T(\mathrm{lca}_T(x,y)) \;\{<,=,>\}\; \tau_S(\mathrm{lca}_S(\sigma(x),\sigma(y)))$ holds, respectively. Since time maps increase towards the root, $G_<$ collects gene pairs that diverged more recently than their species, and $G_>$ gene pairs that diverged before their species. Every unordered pair lies in exactly one of the three graphs, so $\mathscr{G}(\mathscr{S}) = (G_<, G_=, G_>, \sigma)$ is a *colored graph 3-partition* of $\binom{L}{2}$.

For an abstract colored 3-partition $\mathscr{G} = (G_<, G_=, G_>, \sigma)$ on $L$, the *informative species triples* $\mathscr{R}_S(\mathscr{G})$ contain $XY|Z$ whenever there are $x,y,z \in L$ of pairwise distinct colors $X,Y,Z$ with either $xz, yz \in E(G_<)$ and $xy \notin E(G_<)$, or $xy \in E(G_>)$ and $xz, yz \notin E(G_>)$. The *forbidden species triples* $\mathscr{F}_S(\mathscr{G})$ contain $XZ|Y$ and $YZ|X$ whenever such $x,y,z$ satisfy $xz, yz \in E(G_=)$ and $xy \notin E(G_=)$. The pair $(\mathscr{R}, \mathscr{F})$ is *consistent* if some tree displays every triple of $\mathscr{R}$ and no triple of $\mathscr{F}$.

**Theorem.** A colored graph 3-partition $\mathscr{G} = (G_<, G_=, G_>, \sigma)$ is explained by a relaxed scenario if and only if
1. $G_<$ and $G_=$ are properly colored,
2. $G_<$ and $G_>$ are cographs, and
3. $(\mathscr{R}_S(\mathscr{G}), \mathscr{F}_S(\mathscr{G}))$ is consistent.

Consequently:
- explainability is hereditary: $\mathscr{G}$ is explainable if and only if its restriction to every subset $L' \subseteq L$ is;
- it can be decided in $O(|L|^4 \log |L|)$ time whether $\mathscr{G}$ is explainable, and a scenario is constructed when it is;
- $\mathscr{G}$ is explained by a relaxed scenario if and only if it is explained by a *restricted* scenario, one with no unobservable transfers.

## Expansion

Necessity: two genes of the same species have $\mathrm{lca}_S(\sigma(x),\sigma(y)) = \sigma(x)$, a leaf whose time equals the gene-leaf times, which are strictly smaller than $\tau_T(\mathrm{lca}_T(x,y))$; so such pairs always lie in $G_>$, never in $G_<$ or $G_=$. The relation "gene lca later than species lca" depends only on $T$'s and $S$'s lca vertices and orders, which forces $G_<$ and $G_>$ to be explained by cotrees built from $T$, hence to be cographs; the triple conditions record which species must be clustered or separated in $S$. Sufficiency is constructive: a top-down recursion over a species tree displaying $\mathscr{R}_S$ and avoiding $\mathscr{F}_S$ splits the genes using auxiliary graphs built from $G_<$ and $G_=$ at each species vertex and assigns compatible times. The restricted-scenario statement follows by modifying the same construction so that every transfer leaves an observable descendant.

## Sources

- David Schaller, Tom Hartmann, Manuel Lafond, Nicolas Wieseke, Peter F. Stadler and Marc Hellmuth, "Relative timing information and orthology in evolutionary scenarios", Algorithms for Molecular Biology 18 (2023), 16, <https://doi.org/10.1186/s13015-023-00240-4>; numbering as in arXiv:2212.02201: Definitions in Section 2–3, Theorem 10, Corollaries 7–8 (Section 5) and Theorem 13 (Section 6).
