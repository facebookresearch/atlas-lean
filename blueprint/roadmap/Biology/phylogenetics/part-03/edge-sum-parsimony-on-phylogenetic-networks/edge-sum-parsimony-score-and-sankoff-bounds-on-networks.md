# Edge-sum parsimony score and Sankoff bounds on networks

**Setting.** Let $N$ be a rooted phylogenetic network (a rooted DAG with leaves $[n]$, tree vertices of in-degree one and reticulate vertices of in-degree two), $\Sigma$ a finite state set, and $\lambda : [n] \to \Sigma$ a character. An **extension** is a map $\hat\lambda : V(N) \to \Sigma$ agreeing with $\lambda$ on leaves. For a cost matrix $C = (c_{ij})$ and edge $e = (u,v)$, write $w_e(\hat\lambda) = c_{\hat\lambda(u)\hat\lambda(v)}$. Two parsimony criteria are

$$P_1(\hat\lambda) = \min_{T \in \mathcal T(N)} \sum_{e \in E(T)} w_e(\hat\lambda), \qquad P_2(\hat\lambda) = \sum_{e \in E(N)} w_e(\hat\lambda),$$

where $\mathcal T(N)$ is the set of trees displayed by $N$. The edge-sum (hardwired) score is $\min_{\hat\lambda} P_2(\hat\lambda)$. If $N$ has $r$ reticulations and no two reticulate vertices are siblings, deleting one incoming edge per reticulation and suppressing degree-two vertices yields exactly $2^r$ displayed trees on the full leaf set.

**Lower bound.** Run Sankoff's recursion in post-order over $N$ but let each reticulate vertex take two possibly different states, one for each incoming edge: the cost $S_v(i)$ at a vertex is the minimum over children of $c_{ij} + S_{\text{child}}(j)$, summed over children, and each reticulate edge is charged with its own optimal choice. Then

$$\min_i S_{\mathrm{root}}(i) \le \min_{\hat\lambda} P_2(\hat\lambda),$$

since the relaxation drops only the requirement that a reticulate vertex's two copies agree. If the relaxed optimum is conflict-free at every reticulate vertex, it is optimal.

**Upper bound.** Any conflict-free extension gives an upper bound; one is obtained by a pre-order pass that fixes the root state, propagates Sankoff back-pointers, and at each conflicting reticulate vertex $w$ chooses the single state $j$ minimizing the updated total $S' - c_{i'j'} + c_{i'j}$. A Fitch-style variant gives an upper bound on the number of state changes under unit costs for any network and a lower bound for networks without sister reticulations.

## Depends on

- [Sankoff's algorithm](../../small-parsimony-problem/sankoff.md)

## Expansion

On a tree, Sankoff's algorithm is exact because each vertex has a single parent and subtrees interact only through it. In a network a reticulate vertex is reachable from two parents, so treating its two incoming edges as independent copies turns the DAG into a tree-shaped relaxation whose optimum can only be lower. The edge-sum criterion charges substitutions on every reticulate edge, so adding reticulations is penalized rather than rewarded, in contrast with $P_1$, which can only decrease as edges are added and so tends to overestimate reticulation; that makes $P_2$ suited to comparing networks with different numbers of reticulations. On networks with at most ten leaves and two reticulations, the lower and upper bounds coincided with the exhaustive optimum in almost all cases tested.

## Sources

- L. Kannan, W. C. Wheeler, "Maximum Parsimony on Phylogenetic networks", Algorithms for Molecular Biology 7:9 (2012), parsimony criteria $P_1$, $P_2$, Algorithms 1–2 (extended Sankoff lower and upper bounds) and the Fitch extension, <https://doi.org/10.1186/1748-7188-7-9>, PMCID PMC3377548.
