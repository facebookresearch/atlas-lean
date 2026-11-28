# Shortest common superstring via maximum-overlap Hamiltonian paths

String overlap, merging and their specification are separate definitions and are not part of this node. This node
collects the shortest-common-superstring clauses.

## Expansion

A sound expansion has separate pages for:

1. **Overlap characterization.** For a substring-free collection $s_1, \dots, s_m$ of distinct nonempty strings, with
   $\mathrm{ov}(s, t)$ the length of the longest suffix of $s$ that is a prefix of $t$ and is shorter than both, every shortest common
   superstring is obtained from some ordering $\pi$ by merging consecutive strings with maximal overlap, and its length is
   $\sum_i \lvert s_i \rvert - \max_\pi \sum_j \mathrm{ov}(s_{\pi(j)}, s_{\pi(j+1)})$; equivalently, a maximum-weight Hamiltonian path
   problem in the overlap graph.
2. **Greedy merging,** as a separate algorithm; its approximation ratio is the research question of the related page.

## Related topics

- [Approximation ratio of the greedy superstring algorithm](../../ComputerScience/approximation-algorithms/approximation-ratio-of-the-greedy-superstring-algorithm.md)

## Sources

- The Greedy Superstring Conjecture Is False — N. Chukhin et al., arXiv:2609.01365v2 (2026), Sec. 2.1 (overlaps and overlap merges) and Sec. 2.2 (permutations; shortest common superstring as a maximum-weight Hamiltonian path in the overlap graph, after Blum, Jiang, Li, Tromp and Yannakakis). <https://arxiv.org/abs/2609.01365v2>
- An Eulerian path approach to DNA fragment assembly — P. A. Pevzner, H. Tang, M. S. Waterman, PNAS 2001 (PubMed Central PMC55524), Introduction (the overlap–layout formulation leads to the Hamiltonian path problem). <https://pmc.ncbi.nlm.nih.gov:443/articles/PMC55524/>
