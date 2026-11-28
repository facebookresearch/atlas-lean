# Edmonds' weight-shift reductions

Let $h > \sum_{e \in E(G)} |w(e)|$. Adding $h$ to every arc weight makes every optimum branching of the shifted weights a branching of $G$ with the maximum number of arcs, of maximum $w$-weight among those. In particular, if $G$ contains a spanning out-arborescence then the shifted optimum branching is a maximum-weight spanning out-arborescence. If $G$ contains a spanning out-arborescence rooted at a prescribed vertex $r_0$, let $G'$ be obtained from $G$ by adjoining a new arc $e_0$ (of arbitrary weight) directed into $r_0$ from a new vertex that has no other incident arcs. Then $T$ is a spanning out-arborescence of $G$ rooted at $r_0$ if and only if $T \cup \{e_0\}$ is a spanning out-arborescence of $G'$, so removing $e_0$ from a maximum-weight spanning out-arborescence of $G'$ gives a maximum-weight spanning out-arborescence of $G$ rooted at $r_0$.

## Proof sketch

One extra arc gains $h$, which exceeds any possible difference in original weight, so a branching with more arcs has larger shifted weight; among branchings with the same number of arcs the shifted and original weights differ by the same constant. A spanning out-arborescence is a branching with $|V(G)| - 1$ arcs, the most a branching can have. The new vertex of $G'$ has no entering arc, so it is the root of every spanning out-arborescence of $G'$, which therefore contains $e_0$; deleting $e_0$ leaves a spanning out-arborescence of $G$ rooted at $r_0$, and conversely adding $e_0$ to one gives a spanning out-arborescence of $G'$, with weights differing by the constant $w(e_0)$.

Equivalently, deleting the arcs into $r_0$ before the shift gives a maximum-weight spanning out-arborescence rooted at $r_0$: after the deletion $r_0$ has in-degree $0$, so every spanning out-arborescence of the new graph is rooted at $r_0$, and the spanning out-arborescences of $G$ rooted at $r_0$ use no arc into $r_0$, so all of them survive.

## Depends on

- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)

## Proof depends on

- [Optimum branchings by the super-root reduction](optimum-branching-reduction.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967, Section 2.
