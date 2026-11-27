# Quasi-best match graphs and their triple characterization

**Definitions.** Let $(T, \sigma)$ be a rooted tree with leaf set $L$ and leaf coloring $\sigma \colon L \to S$ (genes colored by their species), with ancestor order $\preceq_T$ and last common ancestor $\mathrm{lca}_T$. A leaf $y$ is a *best match* of $x$ if $\sigma(x) \ne \sigma(y)$ and $\mathrm{lca}_T(x, y) \preceq_T \mathrm{lca}_T(x, y')$ for every leaf $y'$ with $\sigma(y') = \sigma(y)$. A *truncation map* $u_T \colon L \times S \to V(T)$ assigns to each leaf $x$ and color $s$ a vertex on the path from the root to $x$, with $u_T(x, \sigma(x)) = x$. A leaf $y$ is a *quasi-best match* of $x$ if $y$ is a best match of $x$ and $\mathrm{lca}_T(x, y) \preceq_T u_T(x, \sigma(y))$. The digraph on $L$ with an arc $xy$ for each quasi-best match is the *quasi-best match graph* (qBMG) $G(T, \sigma, u_T)$; with the trivial truncation map (always the root) it is the best match graph (BMG). For a properly colored digraph $(G, \sigma)$, write $N(x, s)$ for the out-neighbors of $x$ of color $s$, and define the *informative* and *forbidden* triples

$$\mathscr{R}(G,\sigma) = \{ab|b' : \sigma(a) \ne \sigma(b) = \sigma(b'),\ ab \in E(G),\ ab' \notin E(G)\},$$

$$\mathscr{F}(G,\sigma) = \{ab|b' : \sigma(a) \ne \sigma(b) = \sigma(b'),\ b \ne b',\ ab, ab' \in E(G)\}.$$

**Theorem.**

1. $(G, \sigma)$ is a qBMG if and only if there is a BMG $(\tilde G, \sigma)$ on the same vertex set such that for every $x$ and color $s$, either $N_G(x, s) = N_{\tilde G}(x, s)$ or $N_G(x, s) = \emptyset$. Hence qBMGs form a hereditary class.
2. A properly colored digraph $(G, \sigma)$ is a qBMG if and only if the pair $(\mathscr{R}(G,\sigma), \mathscr{F}(G,\sigma))$ is consistent, i.e. some tree displays every triple in $\mathscr{R}$ and none in $\mathscr{F}$. Every such tree explains $(G, \sigma)$ with a suitable truncation map, and recognition takes $O(|E|\,|L|^2 \log |L|)$ time.
3. $(G, \sigma)$ is a BMG if and only if it is a qBMG that is *color-sink-free*: $N(x, s) \ne \emptyset$ for every $x$ and every color $s \ne \sigma(x)$.

## Expansion

Truncation models gene loss or incomplete sampling: once the search for a best match of $x$ in species $s$ climbs above $u_T(x, s)$, the match is discarded, so qBMGs keep only best matches that are "close enough". A truncation can delete the whole color-$s$ neighborhood of $x$ but never a proper part of it, which is item 1. Every explaining tree must separate $b$ from $b'$ below $a$ when $a$ prefers $b$, and must not separate two equally good matches, which gives the triple conditions; the BMG characterization by informative and forbidden triples needs color-sink-freeness in addition, and item 3 shows this is the only difference.

## Sources

- Annachiara Korchmaros, David Schaller, Marc Hellmuth and Peter F. Stadler, "Quasi-best match graphs", Discrete Applied Mathematics 331 (2023), 104–125, <https://doi.org/10.1016/j.dam.2023.01.015>; numbering as in arXiv:2109.10235: Definitions 3.1–3.2, Theorem 3.4, Corollary 3.6, Theorems 4.2–4.3 and Corollary 4.4.
