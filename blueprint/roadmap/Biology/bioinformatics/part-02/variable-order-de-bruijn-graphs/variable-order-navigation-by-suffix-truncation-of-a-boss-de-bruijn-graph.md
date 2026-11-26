# Variable-order navigation by suffix truncation of a BOSS de Bruijn graph

**Setting.** Let $\Sigma$ be an alphabet of size $\sigma$ (for DNA, $\sigma=4$) together with a sentinel symbol. The BOSS representation of a $K$-th order de Bruijn graph built from a set of $(K+1)$-mers sorts the $(K+1)$-mers (padded with sentinel-prefixed and sentinel-suffixed dummies) by the co-lexicographic (right-to-left) order of their first $K$ characters, ties broken by the last character. A node is a maximal interval $[i,j]$ of rows sharing the same $K$-character label, and its outgoing edges are labelled by the last characters of those rows. With $n$ nodes there are at most $\sigma n$ rows. It supports three primitive queries: $\mathsf{forward}(v,a)$ (follow the out-edge labelled $a$), $\mathsf{backward}(v)$ (list in-neighbours) and $\mathsf{lastchar}(v)$.

**Lower orders inside one matrix.** Deleting the first $K-k$ columns of the matrix almost yields the BOSS matrix of the $k$-th order graph: because the order is co-lexicographic, every $k$-th order node is again an interval $[i,j]$ of the same rows, namely the union of the $K$-th order intervals whose labels end with the same length-$k$ suffix. Hence nodes of all orders $0\le k\le K$ coexist as intervals in one matrix. Define

- $\mathsf{shorter}(v,k)$: the node whose label is the last $k$ characters of $v$'s label;
- $\mathsf{longer}(v,k)$: all nodes with label length $k$ whose labels end with $v$'s label;
- $\mathsf{maxlen}(v,a)$: some $K$-th order node whose label ends with $v$'s label and that has an out-edge labelled $a$ (or none); $\mathsf{maxlen}(v,*)$ ignores the edge.

**Theorem (reduction).** For a node $v$ whose label has length $k_v<K$,

$$\mathsf{forward}(v,a)=\mathsf{shorter}\big(\mathsf{forward}(\mathsf{maxlen}(v,a),a),\,k_v\big),\qquad \mathsf{lastchar}(v)=\mathsf{lastchar}(\mathsf{maxlen}(v,*)),$$

$$\mathsf{backward}(v)=\mathsf{shorter}\Big(\mathsf{backward}\big(\mathsf{maxlen}(\mathsf{longer}(v,k_v+1),*)\big),\,k_v\Big)\ \ \text{(duplicates removed)},$$

where queries are applied elementwise to lists. Thus the $K$-th order primitives, plus the three order-changing queries, navigate the de Bruijn graph of every order $k\le K$ simultaneously, which lets an assembler shorten $k$ where coverage is low and lengthen it where repeats demand it.

## Expansion

For $\mathsf{backward}$: if $v$ has label $\alpha a$, then $\mathsf{longer}(v,k_v+1)$ lists the $d\le\sigma$ nodes $b\alpha a$; $\mathsf{maxlen}$ lifts each to a $K$-th order node $\beta_i b_i\alpha a$; $\mathsf{backward}$ there returns nodes $c\beta_ib_i\alpha$, of which one per list entry suffices; and $\mathsf{shorter}(\cdot,k_v)$ maps them to exactly the in-neighbours $b_i\alpha$ of $v$. The $\mathsf{forward}$ identity holds because appending $a$ and then truncating to the last $k_v$ characters commutes with first extending the label on the left. The order-changing queries are symmetric: if $x\in\mathsf{longer}(v,k_x)$ then $\mathsf{shorter}(x,k_v)=v$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Sources

- C. Boucher, A. Bowe, T. Gagie, S. J. Puglisi and K. Sadakane, *Variable-order de Bruijn graphs*, arXiv:1411.2718 (2014), Sections 3 (BOSS representation) and 4 (Changing order). <https://doi.org/10.48550/arXiv.1411.2718>
