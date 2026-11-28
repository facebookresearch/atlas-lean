# Closed-form constant in the asymptotic number of tree-child networks with k reticulations

A rooted binary phylogenetic network on $\ell$ labelled leaves is a directed acyclic graph without double edges having a root (indegree $0$, outdegree $1$), leaves (indegree $1$, outdegree $0$), tree vertices (indegree $1$, outdegree $2$) and reticulation vertices (indegree $2$, outdegree $1$). It is **tree-child** if every non-leaf vertex has a child that is not a reticulation vertex, and **normal** if moreover the two parents of each reticulation vertex are incomparable in the ancestor relation. Let $\mathrm{TC}_{\ell,k}$ and $N_{\ell,k}$ be the numbers of tree-child and normal networks with $\ell$ leaves and $k$ reticulation vertices.

**Theorem 1.** For fixed $k \ge 0$ and $\ell \to \infty$,

$$ \mathrm{TC}_{\ell,k} \sim \frac{2^{k-1} \sqrt{2}}{k!} \Bigl( \frac{2}{e} \Bigr)^{\ell} \ell^{\ell + 2k - 1}. $$

**Corollary 2.** For fixed $k$ and $\ell \to \infty$, $N_{\ell,k} \sim \frac{2^{k-1} \sqrt{2}}{k!} \bigl( \frac{2}{e} \bigr)^{\ell} \ell^{\ell + 2k - 1}$.

The constant $c_k = 2^{k-1}\sqrt{2}/k!$ recovers the earlier values $c_0 = \sqrt{2}/2$, $c_1 = c_2 = \sqrt{2}$, $c_3 = 2\sqrt{2}/3$, and refutes the expectation that no closed form exists. For $k = 0$ the formula is the Stirling asymptotics of the $(2\ell - 3)!!$ rooted binary phylogenetic trees.

## Expansion

The proof uses the component-graph decomposition of Cardona and Zhang. Deleting the incoming edges of all reticulation vertices of a tree-child network leaves $k+1$ tree components; the component graph records how they are joined, and is a rooted DAG (double edges allowed) in which every non-root vertex has indegree two. Every tree-child network arises by choosing a component graph with $k+1$ vertices, reducing it, replacing its root part by a one-component tree-child network (every reticulation directly followed by a leaf), whose number with $\ell$ leaves and $k$ reticulations is $\mathrm{O}_{\ell,k} = \frac{(2\ell-2)!}{2^{\ell-1}(\ell-k-1)!}$ (Lemma 3), substituting phylogenetic trees for the remaining components, and re-inserting the deleted edges, counted using that a network with $\ell$ leaves and $k$ reticulations has $2\ell + 3k - 1$ edges (Lemma 4). One special component graph contributes the main term, computed exactly through $\mathrm{O}_{\ell,k}$ and Stirling's formula; for every other component graph the number of networks is bounded by a smaller order in $\ell$, and since there are finitely many component graphs for fixed $k$, the dominant term gives the asymptotics. Normal networks are asymptotically all tree-child networks with $k$ reticulations, giving Corollary 2.

## Sources

- Michael Fuchs, En-Yu Huang, Guan-Ru Yu, "Counting phylogenetic networks with few reticulation vertices: A second approach", Discrete Applied Mathematics 320 (2022), 140–149, <https://doi.org/10.1016/j.dam.2022.03.026>. Published version of arXiv:2104.07842, cited next; locators there refer to the arXiv version.
- Michael Fuchs, En-Yu Huang, Guan-Ru Yu, "Counting Phylogenetic Networks with Few Reticulation Vertices: A Second Approach", arXiv (2021). Theorem 1, Corollary 2, Lemmas 3 and 4, Section 3. <https://doi.org/10.48550/arXiv.2104.07842>
