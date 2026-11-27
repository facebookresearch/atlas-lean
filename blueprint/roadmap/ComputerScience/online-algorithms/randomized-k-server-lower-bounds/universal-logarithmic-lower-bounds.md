# Universal logarithmic lower bounds for randomized k-server and MTS

For all integers $k < n$ and every $n$-point metric space, the randomized competitive ratio of the $k$-server problem is $\Omega(\log k)$, and the randomized competitive ratio of metrical task systems is $\Omega(\log n)$. Both bounds are asymptotically tight for suitable families of metrics, and they improve the previous universal bounds $\Omega(\log k / \log\log k)$ and $\Omega(\log n / \log\log n)$.

## Proof sketch

Bubeck, Coester and Rabani prove an $\Omega(\log n)$ lower bound for metrical service systems with request sets of size $n - 1$ (equivalently, for $(n-1)$-server and for metrical task systems) on every $n$-point ultrametric (1-HST): for a subspace with the same diameter they construct a distribution of request sequences, built recursively from chunks of inductive sequences, on which every deterministic algorithm pays $\Omega(\log n)$ times the optimum, and apply Yao's principle. The metric Ramsey theorem of Bartal, Linial, Mendel and Naor gives every $n$-point metric a subspace with $n^{\Omega(1)}$ points that is a 1-HST up to distortion $2 + \epsilon$, which transfers the bound to all metrics; the $k$-server bound follows by restricting to a subspace of $k + 1$ points.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Metrical task systems](../metrical-task-systems-and-hst-embeddings/metrical-task-system.md)

## Proof depends on

- [Yao's minimax principle](../../../TheoryOfComputation/randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md)

## Sources

- Sébastien Bubeck, Christian Coester, Yuval Rabani, "The Randomized k-Server Conjecture Is False!", STOC (2023), arXiv:2211.05753, Section 5 (Theorem 16, Lemma 18, Theorem 19, Corollary 20).
- Yair Bartal, Nathan Linial, Manor Mendel, Assaf Naor, "On Metric Ramsey-Type Phenomena", Annals of Mathematics 162(2) (2005); STOC (2003).
