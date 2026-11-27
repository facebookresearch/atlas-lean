# Partial sums over permutation groups reduce to connectivity of disjoint paths

Let $k = \sqrt{n}$. Dynamic partial sums over the symmetric group $S_k$ on an array of length $k$, with *verify-sum* queries (given $i$ and $\pi \in S_k$, decide whether $A[1] A[2] \cdots A[i] = \pi$), reduces to dynamic connectivity on a graph with $\Theta(n)$ vertices that is always a disjoint union of $k$ paths. The vertices $(x, y)$ form a grid with columns $x = 0, \dots, k$ and rows $y \in [k]$; the edges between columns $i - 1$ and $i$ form the perfect matching given by $A[i]$. An $\mathrm{update}(i, \pi)$ is realized by $k$ edge deletions and $k$ edge insertions, and $\mathrm{verify\text{-}sum}(i, \pi)$ by the $k$ connectivity queries asking whether $(0, y)$ is connected to $(i, \pi(y))$ for all $y \in [k]$.

## Proof sketch

The graph is a union of $k$ vertex-disjoint paths through the columns, and following the path from $(0, a)$ through columns $1, \dots, i$ applies $A[1], \dots, A[i]$ in turn. Replacing one matching changes $2k$ edges. Each element of $S_k$ carries $\delta = \Theta(k \lg k) = \Theta(\sqrt{n}\lg n)$ bits, so with $w = \Theta(\lg n)$ the Pătraşcu–Demaine lower bound of $\Omega((\delta/w) \lg n)$ per macro-operation, proved for verify-sum queries via their treatment of low-entropy (nondeterministic) queries, is $\Omega(\sqrt{n}\lg n)$; dividing by the $O(\sqrt{n})$ elementary operations per macro-operation gives $\Omega(\lg n)$ per connectivity operation.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](../disjoint-sets-and-dynamic-trees/fully-dynamic-connectivity-and-spanning-forests/fully-dynamic-connectivity-problems.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
