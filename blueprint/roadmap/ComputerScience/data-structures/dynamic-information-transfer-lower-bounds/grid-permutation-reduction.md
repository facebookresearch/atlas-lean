# Partial sums over permutation groups reduce to connectivity of disjoint paths

Let $k = \sqrt{n}$. Dynamic partial sums over the symmetric group $S_k$ on an array of length $k$ reduces to dynamic connectivity on an $n$-vertex graph that is always a disjoint union of paths: vertices form a $k \times k$ grid of columns $0, \dots, k$, the edges between columns $i-1$ and $i$ form the perfect matching given by $A[i] \in S_k$, an $\mathrm{update}(i, \pi)$ is realized by $O(k)$ edge deletions and insertions, and the value of $\mathrm{sum}(i)$ at a point $a$ equals the unique $b$ in column $i$ connected to $(0, a)$, which can be identified by connectivity queries.

## Proof sketch

The graph is a union of $k$ vertex-disjoint paths through the columns, and following the path from $(0, a)$ through columns $1, \dots, i$ applies $A[1], \dots, A[i]$ in turn. Replacing one matching changes $2k$ edges. Since each element of $S_k$ carries $\Theta(k\lg k)$ bits, the partial-sums lower bound with $\delta = \Theta(k \lg k)$ bits per element transfers to connectivity after dividing by the $O(k)$ edge operations per update.

## Depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Dynamic graph connectivity](dynamic-connectivity-problem.md)

## Proof depends on

- [Dynamic partial sums over a group](dynamic-partial-sums-problem.md)
- [Dynamic graph connectivity](dynamic-connectivity-problem.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
