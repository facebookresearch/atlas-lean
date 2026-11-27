# Gene duplications as rooted-triple inconsistencies

**Setting.** Let $S$ be a rooted binary species tree and $G$ a rooted binary gene tree with a leaf-labelling $L_{G,S} : L(G) \to L(S)$. The **LCA mapping** $M_{G,S} : V(G) \to V(S)$ sends a node $u$ to $\mathrm{LCA}_S\big(L_{G,S}(L(G(u)))\big)$, the least common ancestor in $S$ of the species below $u$. An internal node $g$ is a **duplication** if $M_{G,S}(g) = M_{G,S}(c)$ for some child $c$ of $g$. The duplication cost of a collection $\mathcal G$ of gene trees is

$$\mathrm{Dup}(\mathcal G, S) = \sum_{G \in \mathcal G} \big|\{g \in V(G) : g \text{ is a duplication}\}\big|,$$

and the **gene duplication (GD) problem** asks for $\mathrm{Dup}(\mathcal G) = \min_S \mathrm{Dup}(\mathcal G, S)$ and a minimizing species tree.

A **rooted triple** $xy|z$ is the binary tree on three leaves in which the path between $x$ and $y$ avoids the path from $z$ to the root; a tree $T$ displays $xy|z$ if $\mathrm{LCA}_T(x,y) <_T \mathrm{LCA}_T(x,z)$. Write $\mathrm{Trip}_G(u)$ for the triples of $G$ whose three leaves have LCA $u$, and $\mathrm{Trip}(S)$ for the triples displayed by $S$. A node $u \in V(G)$ is **triple-inconsistent** with $S$ if some triple in $\mathrm{Trip}_G(u)$ is not in $\mathrm{Trip}(S)$; let $\mathrm{Tin}(\mathcal G, S)$ count such nodes.

**Theorem.** For every internal node $u$ of a binary gene tree $G$, $u$ is a duplication with respect to $S$ if and only if $u$ is triple-inconsistent with $S$. Consequently $\mathrm{Dup}(\mathcal G, S) = \mathrm{Tin}(\mathcal G, S)$ for every $S$, and the GD problem and the triple-inconsistency problem have the same optimal species trees.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)
- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)

## Expansion

If $u$ with children $v, w$ is not a duplication, then $M(v)$ and $M(w)$ are incomparable in $S$, so for any $ab|c \in \mathrm{Trip}_G(u)$ with $a,b$ below $v$ and $c$ below $w$, the species $a, b$ lie below $M(v)$ and $c$ below $M(w)$, and $S$ displays $ab|c$. Conversely, if $u$ is a duplication with $M(u) = M(v) = x$, pick leaves under the two children of $x$ in $S$ that both descend from $v$; a case analysis on where a third leaf sits produces a triple of $G$ rooted at $u$ whose resolution in $S$ differs. The equivalence turns a mapping-based cost into a statement about which rooted triples the species tree displays, which is the form an integer program can express.

## Sources

- W.-C. Chang, G. J. Burleigh, D. F. Fernández-Baca, O. Eulenstein, "An ILP solution for the gene duplication problem", BMC Bioinformatics 12 (Suppl 1): S14 (2011), Definitions 1–6, Theorem 1 and Corollary 1, <https://doi.org/10.1186/1471-2105-12-s1-s14>, PMCID PMC3044268.
