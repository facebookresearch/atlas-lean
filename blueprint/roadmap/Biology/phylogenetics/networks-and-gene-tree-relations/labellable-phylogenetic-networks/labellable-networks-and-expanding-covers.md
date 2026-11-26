# Labellable phylogenetic networks and expanding covers

**Networks.** A rooted phylogenetic network on $n$ leaves is a finite directed acyclic graph with a single root (in-degree $0$) and $n$ leaves (out-degree $0$, in-degree $1$) labelled by $[n] = \{1, \dots, n\}$. Internal vertices may have any non-zero in- and out-degree. Write $c_N(x)$ for the set of children of $x$. An internal vertex is *degenerate* if its in- and out-degree are both $1$, or both greater than $1$, and $N$ is *non-degenerate* if it has no degenerate vertex.

**Labelling algorithm.** Order finite sets of integers by $A \prec B$ if $A \subseteq B$ or $\min A \setminus (A \cap B) < \min B \setminus (A \cap B)$. Starting with the leaves labelled $1, \dots, n$, repeatedly choose the $\prec$-minimal set of labelled sibling vertices whose common parent is still unlabelled, and give that parent the next unused integer $n+1, n+2, \dots$ until every non-root vertex is labelled. A network is *labellable* if this procedure is well defined, i.e. every set of labelled siblings selected has a unique parent.

**Theorem (characterization).** A labelling step is always available: if some vertex is unlabelled, then some unlabelled vertex has all of its children labelled. Consequently $N$ is labellable if and only if $c_N(x) \ne c_N(y)$ for all distinct non-leaf vertices $x, y$, i.e. iff $c_N$ is injective.

**Covers.** The sets of sibling labels of a labelled network form a *cover* $C$ of $[m]$, a set of non-empty subsets of $[m]$ whose union is $[m]$. A label that appears in two or more sets of $C$ marks a reticulation. If $C$ comes from a network on $n$ leaves, then

$$n = m - |C| + 1 .$$

A cover $C$ is *expanding* if (1) no element of $[n]$ is repeated in $C$, and (2) for each $i = 1, \dots, |C|$, $C$ contains at least $i$ subsets of $[n + i - 1]$.

**Theorem (bijection).** Labellable phylogenetic networks on $n$ leaves are in bijection with expanding covers, via the cover of sibling sets in one direction and a deterministic reconstruction in the other.

**Non-degenerate networks.** List the sets of $C$ in *labelling order*: $C_i$ is the $\prec$-minimal set of $C \setminus \{C_1, \dots, C_{i-1}\}$ contained in $[n + i - 1]$. The cover satisfies the *order condition* if, for each $i$, $|C_i| > 1$ implies that $n + i$ appears at most once in $C$, and $|C_i| = 1$ implies that $n + i$ appears more than once. Non-degenerate labellable networks are in bijection with expanding covers that satisfy the order condition. The labelling order is built in time linear in $|C|$, and the whole check takes at most cubic time.

## Expansion

For existence of a step, take an unlabelled vertex and follow unlabelled vertices downward. The length of the longest path to a leaf strictly decreases along the way and is at least $1$ for unlabelled vertices, so the walk stops at an unlabelled vertex whose children are all labelled. Uniqueness fails exactly when two candidate parents share a child set, since $\prec$ cannot separate them. The vertex count gives $n + |C| = m + 1$: there are $|C|$ non-leaf vertices and every vertex except the root carries a label in $[m]$. Leaves have one parent, which gives property (1). Property (2) holds because at step $i$ the selected sibling set lies in $[n + i - 1]$ and differs from the $i - 1$ sets used before. Conversely, an expanding cover is turned into a network by repeatedly taking the labelling-order set, creating a parent with the next label and adding arcs to the members. Finiteness and the expanding property keep the process going until a single unlabelled root remains. In the cover, the in-degree of label $k$ is the number of sets containing it and the out-degree is $|C_i|$ when $k = n + i$. Non-degeneracy says each vertex has in-degree $1$ or out-degree $1$ but not both, which is exactly the order condition. Example: $C = \{\{2\}, \{5\}, \{1,6\}, \{4,8\}, \{3,6,9\}, \{10\}, \{7,11\}, \{8,12\}\}$ is an expanding cover of $[12]$ with $n = 5$. It fails the order condition at $C_6 = \{10\}$, because $11$ appears only once, and the vertex labelled $11$ is a degenerate vertex of in- and out-degree $1$.

## Sources

- A. Francis, M. Steel, "Labellable phylogenetic networks", Bulletin of Mathematical Biology 85 (2023) 46, Algorithm 1, Definition 3.1, Lemma 3.2, Theorem 3.3, Lemmas 4.1–4.2, Definition 4.3, Theorem 4.4, Example 4.5, Theorem 5.1 and Example 5.2, <https://doi.org/10.1007/s11538-023-01157-0> (PMC10129972).
