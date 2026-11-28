# Pattern-matching rejection of regulatory network models

**Setting.** From experimental time series of $N$ gene products, record the times of local maxima and minima of each product with error bars; the induced partial order on these extremal events is a *poset of extrema* $(P, <)$. Its *pattern graph* is a labeled directed graph whose root-to-leaf paths are the sequences of events consistent with the data: it is built from the *down-set graph* of $P$, whose vertices are down-sets (order ideals) of $P$ and whose edges add one element. A regulatory network model with switching (Boolean-like) nonlinearities and a parameter region, as computed by DSGRN, yields a *search graph*: a labeled directed graph on the cells of a cubical decomposition of $(0,\infty)^N$ whose paths over-approximate all trajectories of all systems compatible with the model, with labels recording which variables can have a maximum or minimum on crossing a wall.

**Theorem.**

1. The down-set graph of a finite poset $(P,<)$ is a directed acyclic graph with unique root $\emptyset$ and unique leaf $P$, and its root-to-leaf paths are in bijection with the linear extensions of $<$.
2. *(No false negatives.)* If the model admits a domain-wall trajectory, that is, one of a system compatible with the model that is extrema-pattern-matchable with respect to the cubical decomposition (Definitions 3.5–3.6 of the source), whose sequence of extremal events is a linear extension of $P$, then some root-to-leaf path of the pattern graph matches some path of the search graph under the extremal-event matching relation. Hence, if no matching pair of paths exists, the model (at that parameter region) is rejected by the data.
3. Whether such matching paths exist can be decided in polynomial time, by reachability in the product (alignment) graph, which can be built in $O(|V||V'| + |E||E'|)$ time; for posets whose incomparability graph is chordal with maximum antichain size $d$, the down-set graph has at most $2^d|P|$ vertices.

## Expansion

The search graph is a conservative combinatorial model: it contains every possible order of wall crossings, so failure to embed even one ordering of the observed extrema is a proof that no parameter in the region can reproduce the qualitative shape of the data. Matching reduces to a graph alignment problem, solved by searching for a path in the product of the two labeled graphs. Applied to the yeast cell-cycle regulatory network, this rejects large parts of parameter space and some candidate wiring diagrams, without simulating any ODE.

## Sources

- Bree Cummins, Tomas Gedeon, Shaun Harker and Konstantin Mischaikow, "Model Rejection and Parameter Reduction via Time Series", SIAM Journal on Applied Dynamical Systems 17 (2018), 1589–1616, <https://doi.org/10.1137/17m1134548>; numbering as in arXiv:1706.04234: Theorems 2.5, 2.10 and 3.8 and Propositions 2.12–2.14 and 2.17.
