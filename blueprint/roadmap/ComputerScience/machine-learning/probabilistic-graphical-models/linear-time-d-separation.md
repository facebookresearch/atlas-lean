# Linear-time d-separation (Bayes-ball reachability)

Let $G = (V, E)$ be a finite DAG, $X \subseteq V$ a query set and $Z \subseteq V$ a conditioning set
with $X \cap Z = \emptyset$. A trail is active given $Z$ if every collider on it is in $Z$ or has a
descendant in $Z$ and every non-collider on it is outside $Z$. Search over states $(v, \mathrm{dir})$,
where $\mathrm{dir}$ records whether $v$ was entered from a child or from a parent, with the standard
passing rules (a non-collider passes the search only if it is not in $Z$; a collider passes it only if it
is an ancestor of $Z$ or in $Z$), returns exactly the set of $y \notin Z$ such that some active trail
joins $X$ and $y$, that is, such that $X$ and $\{y\}$ are not d-separated by $Z$. With adjacency lists and
the ancestors of $Z$ precomputed, it runs in $O(\lvert V \rvert + \lvert E \rvert)$ time on a random-access
machine with unit-cost operations.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [Bayesian network](bayesian-networks/bayes-net.md)
- [d-separation](causal-bayesian-networks/dseparated.md)

## Sources

- R. D. Shachter, *Bayes-Ball: the rational pastime (for determining irrelevance and requisite information in belief networks and influence diagrams)*, UAI 1998, 480–487: Theorem 1 (d-separation), the passing rules of Figure 2 and the algorithm's linear running time; it credits Geiger's linear-time reachability algorithms for finding active paths. <https://arxiv.org/pdf/1301.7412>
