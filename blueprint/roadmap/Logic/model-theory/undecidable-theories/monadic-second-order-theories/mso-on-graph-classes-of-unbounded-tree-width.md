# MSO finite satisfiability on graph classes of unbounded tree-width is undecidable

For every class of finite graphs of unbounded tree-width, it is undecidable whether a monadic second-order sentence, with quantification over sets of edges as well as of vertices, holds in some graph of the class; in particular this holds for planar graphs.

**Setting.** Graphs are finite simple undirected graphs, given as structures with one binary edge relation; *monadic second-order logic* $\mathrm{MSO}_2$ extends first-order logic by variables for sets of vertices and for sets of edges (subsets of the edge relation), and quantification over them. This is the logic $\mathrm{MS}_2$ of Courcelle and Engelfriet, who express it over incidence structures. The *tree-width* of a graph measures how close it is to a tree: a graph has tree-width at most $k$ iff it is a partial $k$-tree. A class $\mathcal{K}$ has *unbounded tree-width* if for every $k$ some graph in $\mathcal{K}$ has tree-width greater than $k$. *Finite satisfiability of $\mathrm{MSO}_2$ by graphs in $\mathcal{K}$* asks, for an $\mathrm{MSO}_2$ sentence $\varphi$, whether some graph in $\mathcal{K}$ satisfies $\varphi$.

**Theorem (Seese).** For each class $\mathcal{K}$ of graphs of unbounded tree-width, finite satisfiability of $\mathrm{MSO}_2$ by graphs in $\mathcal{K}$ is undecidable.

For instance, finite satisfiability of $\mathrm{MSO}_2$ on planar graphs is undecidable, since planar graphs have unbounded tree-width. By contrast, finite satisfiability of $\mathrm{MSO}_2$ by graphs of tree-width at most $k$ is decidable for each $k$ (Courcelle), so tree-width marks the boundary.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Tree-width at most $k$](../../../../GraphTheory/planar-graphs-and-minors/tree-width/has-treewidth-at-most.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The copy read cites the result without proof. A good expansion would present Seese's proof and link the undecidable problem it reduces from; neither has a page.

## Sources

- D. Seese, "The structure of the models of decidable monadic theories of graphs", *Annals of Pure and Applied Logic* 53(2):169–195, 1991, doi:10.1016/0168-0072(91)90054-P (original source, cited beside the copy read).
- T. Kotek, H. Veith and F. Zuleger, "Monadic second order finite satisfiability and unbounded tree-width", in *25th EACSL Annual Conference on Computer Science Logic (CSL 2016)*, Leibniz International Proceedings in Informatics 62, Schloss Dagstuhl, 2016, article 13, doi:10.4230/LIPIcs.CSL.2016.13; read as arXiv:1505.06622v2, <https://arxiv.org/abs/1505.06622v2>: Section 1, items (2) and (3) and the remark on planar graphs, and Section 2 (tree-width).
