# A sample-resolved genome ARG is determined by its node-labelled local trees

Let $G=(N,S,E)$ be a [genome ARG](genome-arg-interval-annotated-inheritance-graph.md) on the sites $X=\{1,\dots,L\}$ satisfying:

1. **single-parent inheritance:** for each node $c$ and site $x$ at most one edge $(c,p,I)\in E$ has $x\in I$;
2. **one edge per pair:** distinct edges have distinct pairs $(c,p)$, and every annotation $I$ is nonempty;
3. **sample resolution:** for every edge $(c,p,I)$ and every $x\in I$, the node $c$ is ancestral to a sample at $x$, that is, there is a path $s=v_0\to v_1\to\cdots\to v_m=c$ with $s\in S$ ($m\ge0$) whose edges all contain $x$.

Let $\pi^x=(\pi^x_1,\dots,\pi^x_n)$ be the local tree at $x$, an oriented parent vector on the node labels of $G$ with $0$ for roots and absent nodes. Define the local edge set

$$E_x=\{(u,\pi^x_u,\{x\}) : \pi^x_u\ne0\}$$

and merge all $E_x$ by pair: $\widehat E=\{(c,p,I_{cp}) : I_{cp}\ne\emptyset\}$ with $I_{cp}=\{x:\pi^x_c=p\}$. Then $\widehat E=E$. Hence the map from such gARGs to their sequences of node-labelled local trees $(\pi^x)_{x\in X}$ is injective, and $G$ is recovered exactly (with $N$ and $S$ given).

The hypotheses matter. Without (3), only the sample-resolved restriction of $G$ is recovered: material on an edge that is not ancestral to $S$ never appears in a local tree. Without (2), edges sharing a pair are recovered as one edge carrying the union of their intervals. The statement uses **labelled** internal nodes that persist across trees and keeps **locally unary** nodes in each $\pi^x$. Conventional trees, whose internal nodes are unlabelled and whose unary nodes are suppressed, discard exactly the information (shared ancestors and passages through non-coalescing genomes) needed for the reconstruction.

## Depends on

- [Genome ARGs: interval-annotated inheritance graphs and their local trees](genome-arg-interval-annotated-inheritance-graph.md)
- [Coalescence records encode a sequence of local trees exactly](tree-sequence-encoding-represents-local-trees-ex.md)

## Proof depends on

- [Genome ARGs: interval-annotated inheritance graphs and their local trees](genome-arg-interval-annotated-inheritance-graph.md)

## Expansion

Fix $x$. If $(c,p,I)\in E$ and $x\in I$, then by (3) some sample's pastward trace at $x$ reaches $c$. By (1) the edge it then follows from $c$ is $(c,p,I)$, so $\pi^x_c=p$, and $x\in I_{cp}$. If a trace stops at $c$ because $\pi^x_c$ was already set, then $c$ was reached before and the same argument applies. Conversely, every assignment $\pi^x_c=p\ne0$ is made from an edge $(c,p,I)$ with $x\in I$, so $I_{cp}\subseteq I$. Together $I_{cp}=I$ for each edge, and by (2) the pairs index the edges, which proves $\widehat E=E$.

The theorem answers the claim that an ARG holds more information than its interval trees: it does only when the trees are written in the conventional unlabelled and unary-free form. Simplification steps that delete locally unary nodes or rewrite edge annotations remove the corresponding recombination information (timing, or even the existence of an event), and that loss shows up as merged or less informative local trees.

## Sources

- Y. Wong, A. Ignatieva, J. Koskela et al., "A general and efficient representation of ancestral recombination graphs", Genetics (2024), iyae100, <https://doi.org/10.1093/genetics/iyae100>, PMCID PMC11373519. Appendix E ("ARGs and local trees"), the local edge sets $E_x$ and their recombination into the original edges; Appendices F and G ("Locally unary nodes", "Levels of simplification") for the role of unary nodes. The explicit hypotheses (1)-(3) and the injectivity proof above are spelled out here from the paper's definitions.
