# Sibling or quasi-sibling leaves and node-count bounds in tree-sibling time-consistent networks

**Networks.** In a rooted DAG, a *tree node* has in-degree at most $1$ and a *hybrid node* in-degree at least $2$. A *phylogenetic network* on $S = \{1, \dots, n\}$ is a rooted DAG in which no tree node has out-degree $1$, every hybrid node has out-degree $1$ with a tree-node child, and the leaves are bijectively labelled by $S$; it is *semi-binary* if every hybrid node has in-degree exactly $2$. It is *tree-sibling* if every hybrid node has a sibling (a node sharing a parent) that is a tree node, and *time consistent* if there is $\tau : V \to \mathbb{N}$ with $\tau(\text{root}) = 0$, $\tau(u) = \tau(v)$ for every arc $(u,v)$ into a hybrid node and $\tau(u) < \tau(v)$ for every arc into a tree node. Write sbTSTC for semi-binary tree-sibling time-consistent networks. Two nodes are *siblings* if they share a parent; a tree node $v$ is a *quasi-sibling* of a tree node $u$ if the parent of $v$ is a hybrid node that is a sibling of $u$.

**Lemma.** Every sbTSTC network with more than one leaf has a pair of leaves that are siblings or quasi-siblings.

**Proposition (size bounds).** Let an sbTSTC network have $n$ leaves, $h$ hybrid nodes and $t$ internal tree nodes. If $n \le 2$ then $h = 0$ and $t = n - 1$; otherwise

$$h \le 2n - 4, \qquad t \le 3n - 6,$$

and both bounds are attained for every $n \ge 3$. In particular there are finitely many sbTSTC networks on a given leaf set up to isomorphism (for $n = 1, \dots, 5$: $1, 1, 10, 444, 61\,176$).

## Expansion

For the lemma, take the internal nodes of maximal time. If none is hybrid, pick one, $u$: a tree-node child of $u$ would have larger time and a hybrid child equal time, so all children of $u$ are leaves, and since $\operatorname{outdeg}(u) \ge 2$ two of them are siblings. If one is a hybrid node $v$, its two parents have the same time as $v$ and, by the tree-sibling property, one parent has a tree child, which must be a leaf $i$ by maximality; the single child $j$ of $v$ is also a leaf, and $j$ is a quasi-sibling of $i$. Tightness of the bounds is shown by a recursive family $N_3, N_4, \dots$: $N_3$ has $3$ internal tree nodes and $2$ hybrid nodes, and each step adds one leaf, $3$ internal tree nodes and $2$ hybrid nodes while preserving semi-binarity, the tree-sibling property and a time assignment, giving $t = 3(n-2)$ and $h = 2(n-2)$.

## Sources

- G. Cardona, M. Llabrés, F. Rosselló and G. Valiente, "A distance metric for a class of tree-sibling phylogenetic networks", Bioinformatics 24 (2008), 1481–1488, Section 2 (Lemma 1, Proposition 2, Example 1, Table 1), <https://doi.org/10.1093/bioinformatics/btn231>, PMCID: PMC2718672.
