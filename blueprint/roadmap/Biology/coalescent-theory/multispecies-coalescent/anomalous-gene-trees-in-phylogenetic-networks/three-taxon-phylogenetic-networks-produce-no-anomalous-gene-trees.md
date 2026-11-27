# Three-taxon phylogenetic networks produce no anomalous gene trees

**Setting.** A binary phylogenetic network $\psi$ on a taxon set $X$ is a rooted directed acyclic graph
whose root has out-degree 2, whose other non-leaf vertices are tree nodes (in-degree 1, out-degree 2)
or reticulation nodes (in-degree 2, out-degree 1), with leaves bijectively labeled by $X$, branch
lengths $\lambda$ in coalescent units, and inheritance probabilities $\Gamma$: for the two edges
$b_1, b_2$ entering a reticulation, $\gamma_{b_1}, \gamma_{b_2} \ge 0$ with
$\gamma_{b_1} + \gamma_{b_2} = 1$. Gene tree topologies $G$ then have a probability mass function
$P_{\psi, \lambda, \Gamma}(G = g)$ under the multispecies network coalescent.

**Displayed and parental trees.** A tree is **displayed** by $\psi$ if it is obtained by deleting one
incoming edge of every reticulation and suppressing degree-two vertices; $U(\psi)$ is the set of
displayed trees, and $|U(\psi)| \le 2^k$ for $k$ reticulations. Converting $\psi$ to a multi-labeled
tree $T$ (copy the subtree below each reticulation onto both parents) and keeping, for each taxon, a
nonempty subset of its leaf copies gives the **parental trees**; $W(\psi)$ denotes their set. Always
$U(\psi) \subseteq W(\psi)$, and $W(\psi)$ can be much larger.

**Network anomaly.** A gene tree topology $g$ is **anomalous** for $(\psi, \lambda, \Gamma)$ if

$$P_{\psi, \lambda, \Gamma}(G = g) > P_{\psi, \lambda, \Gamma}(G = t) \quad \text{for all } t \in W(\psi),$$

and $\psi$ **produces anomalies** if some $(\lambda, \Gamma)$ admits an anomalous gene tree.

**Lemma.** No phylogenetic network on three taxa produces anomalies.

**Consequences.** Since species trees are networks with no reticulation, every species tree with $n \ge 5$
leaves produces anomalies. A network with reticulations need not: if it displays every rooted
binary tree on its taxa, every gene tree lies in $U(\psi) \subseteq W(\psi)$, so none is anomalous. In contrast with three taxa, some symmetric four-taxon networks do produce
anomalies.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../network-multispecies-coalescent-fixed-network-ge.md)
- [Every species tree with at least five species has an anomaly zone](../every-species-tree-with-5-species-has-an-anomaly.md)

## Proof depends on

- [No anomalous gene trees for three species](../triple-no-anomaly.md)

## Expansion

Restricted to distinct topologies, a three-taxon network has one, two or three parental trees. With
three, every gene tree is parental and none can beat all of them. With two, say $((A,B),C)$ and
$(A,(B,C))$, the only candidate is $((a,c),b)$, which requires $a$ and $c$ to coalesce above the root in
both parental trees; each of the other two gene trees can arise from the same above-root events and
also from coalescences below the root, so each is at least as probable. With one parental tree the
argument reduces to the three-species tree result. Anomaly is defined against all parental trees
rather than a designated species tree; defined against one backbone tree, three-taxon networks can
show anomalies, which is why the two notions must not be conflated.

## Sources

- J. Zhu, Y. Yu, L. Nakhleh, "In the light of deep coalescence: revisiting trees within networks",
  BMC Bioinformatics (2016), Methods, Definitions 1-4, and Results, Lemma 1,
  <https://doi.org/10.1186/s12859-016-1269-1> (PMC5123307).
