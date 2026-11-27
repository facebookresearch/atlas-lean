# Directed expander decompositions computable in O~(m/phi) time and maintainable under deletions in O~(1/phi^2) amortized time

There is an absolute constant $c>0$ such that for every $\phi\le c/\log^{12}m$ and every directed $m$-edge graph $G$ undergoing a sequence of edge deletions, a randomized data structure constructs and maintains a pair $(\mathcal{X},E^r)$ in which every cluster induces an $\Omega(\phi/\log^{12}m)$-expander, $|E^r|=\tilde O(\phi m)$, and $(G\setminus E^r)/\mathcal{X}$ is acyclic. Initialization takes $O(m\log^{20}m/\phi)$ time and each edge deletion is processed in $O(\log^{28}m/\phi^2)$ amortized time. More precisely, the maintained pair is an $(O(\log^{19}m),\Omega(\phi/\log^{12}m),\psi)$-expander decomposition with $\psi=O(1/\log^{8}m)$, in which every cluster carries a witness certifying its expansion. For up to $O(\phi\psi m)$ deletions the maintained partition is refining (every cluster is contained in a cluster of every earlier version) and $|E^r|$ never exceeds $\tilde O(\phi m)$. The only randomness lies in a subroutine that finds balanced sparse cuts or certifies their absence.

## Proof sketch

The algorithm follows the cut-repeatedly meta-algorithm for decompositions, whose dynamic implementation via sparse-cut maintenance was shown to work for directed graphs with subpolynomial overhead. To reach polylogarithmic overhead, the flow problems certifying expansion in both directions are solved by a push-pull-relabel framework that generalizes push-relabel: it pushes excess forward and pulls deficits backward with level labels, and it is dynamized so that each deletion only locally repairs the flow. Amortizing the relabel work against potential decrease bounds the update time by $\tilde O(1/\phi^2)$ per deletion, and pruned vertex sets are refined monotonically, which yields the refinement property.

## Depends on

- [Amortized cost of an operation](../../../ComputerScience/data-structures/amortized-analysis/amortized-cost.md)
- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)
- [Las Vegas and Monte Carlo algorithms](../../../ComputerScience/randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)
- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)

## Proof depends on

- [Every directed graph has a phi-expander decomposition whose backward edges number O(phi m log m)](directed-expander-decomposition-existence.md)

## Sources

- Aurelio L. Sulser, Maximilian Probst Gutenberg, "Near-Optimal Algorithm for Directed Expander Decompositions", ICALP (2025), LIPIcs 334, 132:1-132:20.
- Yiding Hua, Rasmus Kyng, Maximilian Probst Gutenberg, Zihang Wu, "Maintaining Expander Decompositions via Sparse Cuts", SODA (2023), arXiv:2204.02519.
