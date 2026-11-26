# Uniform sampling by mass-equivalent compound substitution

**Setting.** A metabolic network is a directed bipartite graph $G = (V_c \cup V_r, E)$ of compounds and reactions, with substrates $r_{\mathrm{in}}$, products $r_{\mathrm{out}}$ and stoichiometric coefficients $s_{c,r} \in \mathbb N_{>0}$. Each compound has a mass vector $m_c \in \mathbb N^n$ of element counts (e.g. over C, H, N, O, P, S). A reaction is **mass balanced** iff

$$\sum_{c \in r_{\mathrm{in}}} s_{c,r} m_c = \sum_{c \in r_{\mathrm{out}}} s_{c,r} m_c.$$

Two compounds are **mass equivalent** iff their (non-zero) mass vectors are linearly dependent; this is an equivalence relation with classes $\sigma(c)$. In reaction $r$, a substrate (product) $c$ is *substitutable* by $c'$ iff $c' \in \sigma(c)$ and $c'$ is not already a substrate (product) of $r$; replacing $c$ by $c'$ and rescaling coefficients keeps $r$ mass balanced. Let $\Psi_s(r)$ be the set of such substitutions. The **transition graph** $\Sigma_G$ has as nodes the networks reachable from $G_0$ by substitutions and an edge for each substitution; it is undirected (substitutions are reversible) and connected.

**Theorem.**
1. Substitutions preserve the number of reactions, the in- and out-degree of every reaction and mass balance of every reaction; only compound degrees and coefficients change.
2. If only individual compounds are substituted, every network $G \in \Sigma_G$ has the same number of available substitutions, $d(G) = \sum_{r \in V_r}|\Psi_s(r)| = d(G_0)$, i.e. $\Sigma_G$ is regular.
3. Consequently the random walk that picks one of the $d(G)$ available substitutions uniformly at random has the uniform distribution on $\Sigma_G$ as its stationary distribution, and converges to it when $\Sigma_G$ is non-bipartite.

When pairs of compounds may also be substituted (requiring a solvable mass-balance system for the new coefficients), $\Sigma_G$ need not be regular; under an empirically supported power-law model of degree differences along the walk, a generalized Azuma inequality bounds the probability that sampling deviates from almost-uniform.

## Expansion

Part 2: suppose $x$ in reaction $r$ is replaced by $y \in \sigma(x)$, giving $r'$. The available substitutions for $y$ in $r'$ are those for $x$ in $r$, with $x \sim_r y$ traded for $y \sim_{r'} x$, by symmetry of mass equivalence. For any other participant $z$, transitivity gives $z \in \sigma(x) \iff z \in \sigma(y)$, so $z$'s options also merely trade $y$ for $x$. Hence $|\Psi_s(r')| = |\Psi_s(r)|$ and all other reactions are untouched, so the degree of the network in $\Sigma_G$ is unchanged. Part 3 is the standard fact that a simple random walk on a connected regular graph has uniform stationary distribution, convergent for non-bipartite graphs. Unlike degree-preserving edge switches, which ignore chemistry and can create infeasible reactions, these randomizations remain chemically meaningful null models; precomputing the equivalence classes costs $O(|V_c|^2)$ once, after which each substitution is cheap. The single-compound sample space is astronomically large (about $10^{957}$ networks for one genome-scale *E. coli* model), which is why uniformity of the sampler matters.

## Sources

- G. Basler, O. Ebenhöh, J. Selbig, Z. Nikoloski, "Mass-balanced randomization of metabolic networks", Bioinformatics 27(10) (2011) 1397–1403, Eqs. (1)–(4), Section 3.1 (conditions S1–S2, P1–P3), Theorem 1, Theorem 2 and Corollary, <https://doi.org/10.1093/bioinformatics/btr145>, PMCID PMC3087954.
