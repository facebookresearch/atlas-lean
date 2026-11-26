# Edmonds' weight-shift reductions

Let $h > \sum_{e \in E(G)} |w(e)|$. Adding $h$ to every arc weight makes every optimum branching of the shifted weights a branching of $G$ with the maximum number of arcs, of maximum $w$-weight among those. In particular, if $G$ contains a spanning out-arborescence then the shifted optimum branching is a maximum-weight spanning out-arborescence; if $G$ contains a spanning out-arborescence rooted at a prescribed vertex $r_0$, deleting the arcs into $r_0$ first gives a maximum-weight spanning out-arborescence rooted at $r_0$.

## Proof sketch

One extra arc gains $h$, which exceeds any possible difference in original weight.

## Depends on

- [Spanning arborescences and branchings](spanning-arborescences-and-branchings.md)

## Proof depends on

- [Optimum branchings by the super-root reduction](optimum-branching-reduction.md)

## Sources

- J. Edmonds, "Optimum Branchings", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
