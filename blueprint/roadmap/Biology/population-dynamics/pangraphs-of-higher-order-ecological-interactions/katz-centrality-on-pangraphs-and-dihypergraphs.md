# Katz centrality on pangraphs and dihypergraphs

Let $\mathcal P$ be a weighted pangraph with $n$ fundamental vertices and $m$ panedges and let $\mathcal L(\mathcal P)$ be its [Levi digraph](pangraphs-and-their-levi-digraphs.md), with in- and out-adjacency matrices $\mathcal A^{\mathrm{in}}_{\mathcal L}, \mathcal A^{\mathrm{out}}_{\mathcal L}$ (vertices ordered by layer).

**Katz centrality.** For a digraph with adjacency matrix $\mathcal A^{x}$ ($x \in \{\mathrm{in}, \mathrm{out}\}$), damping $\alpha \ge 0$ and baseline vector $\beta$, the Katz centrality solves $c^{x} = \alpha \mathcal A^{x} c^{x} + \beta$, so

$$c^{x} = (I - \alpha \mathcal A^{x})^{-1}\beta = \sum_{k \ge 0} (\alpha \mathcal A^{x})^k \beta$$

whenever $\|\alpha \mathcal A^{x}\| < 1$; it weights all walks ending (in-centrality) or starting (out-centrality) at a vertex. The *pangraph Katz centrality* uses the adjacency among fundamental vertices and those panedges that occur inside other panedges, so walks may pass from panedge to panedge only through nesting; the Levi-digraph Katz centrality instead walks through every panedge and in general ranks vertices differently.

**Generalized pangraph Katz centrality.** Define the *generalized adjacency matrix* $\tilde{\mathcal A}^{x}_{\mathcal P} \in [0,\infty)^{(n+m)\times(n+m)}$ by $(\tilde{\mathcal A}^{x}_{\mathcal P})_{ij} = (\mathcal A^{x}_{\mathcal L})_{ij}$ for $i \ge j$, $(\tilde{\mathcal A}^{x}_{\mathcal P})_{ij} = 1$ for $i < j$ with $(\mathcal A^{x}_{\mathcal L})_{ij} \ne 0$, and $0$ otherwise, and let $\tilde c^{x} = \tilde\alpha^{x} \tilde{\mathcal A}^{x}_{\mathcal P} \tilde c^{x} + \tilde\beta^{x}$, assigning centralities to vertices and interactions alike.

**Theorem 2 (dihypergraphs).** Let $\mathcal H$ be a dihypergraph with weighted incidence matrices $\overline{\mathcal I}^{\mathrm{in}}_{\mathcal H}, \overline{\mathcal I}^{\mathrm{out}}_{\mathcal H}$, and split $\tilde c^{x} = (\tilde c^{x}(v), \tilde c^{x}(e))$ and $\tilde\beta^{x} = (\tilde\beta^{x}(v), \tilde\beta^{x}(e))$ into vertex and hyperedge parts. There are parameter pairs $(\alpha^x, \beta^x)$ and $(\tilde\alpha^x, \tilde\beta^x)$ for which both centralities are well defined, and if, with $y$ the direction opposite to $x$,

$$\alpha^{x} = (\tilde\alpha^{x})^2, \qquad \beta^{x} = \tilde\alpha^{x} \big(\overline{\mathcal I}^{\,y}_{\mathcal H}\big)^{\!\top} \tilde\beta^{x}(e) + \tilde\beta^{x}(v),$$

then the generalized Katz centrality of the fundamental vertices equals the ordinary Katz centrality of $\mathcal H$ with parameters $(\alpha^x, \beta^x)$, for $x = \mathrm{in}, \mathrm{out}$.

## Expansion

For a dihypergraph the Levi digraph is bipartite, so the generalized adjacency matrix has zero diagonal blocks and off-diagonal blocks given by the two incidence matrices. Eliminating the hyperedge block from $(I - \tilde\alpha \tilde{\mathcal A})\tilde c = \tilde \beta$ by a Schur complement turns every vertex-hyperedge-vertex path of length two into one step of the vertex adjacency, which squares the damping factor and pushes the hyperedge baselines onto the vertices through the incidence matrix. For deeper pangraphs no such reduction exists in general: the paper shows that a consistent generalization of recursive measures cannot be reduced to the Levi digraph. In a coffee agroecosystem network, switching from the dihypergraph to the pangraph representation changes Katz values and vertex ranks.

## Depends on

- [Pangraphs and their Levi digraphs](pangraphs-and-their-levi-digraphs.md)

## Sources

- M. Iskrzyński, A. Puchalska, A. Grzelik, G. Mutlu, "Pangraphs as models of higher-order interactions" (2025), Section 6.2 (Katz centrality on pangraphs and Levi digraphs), Section 6.3 (generalized adjacency matrix, generalized Katz centrality and Theorem 2), Section 7.2 (coffee agroecosystem comparison), <https://doi.org/10.48550/arXiv.2502.10141>.
