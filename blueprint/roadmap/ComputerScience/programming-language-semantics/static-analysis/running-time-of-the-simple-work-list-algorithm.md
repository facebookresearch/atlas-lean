# Running time of the simple work-list algorithm

Let $L$ be a complete lattice of finite height $h \ge 1$, the largest number of strict steps $a_0 \sqsubset a_1 \sqsubset \cdots \sqsubset a_h$ in a chain of $L$. Let constraint functions $f_1, \dots, f_n : L^n \to L$ of the $n \ge 1$ nodes $v_1, \dots, v_n$ of a control-flow graph have a monotone combined function, and let dependency sets $\mathrm{dep}(v_i)$ contain every $v_j$ for which $f_j$ depends on $x_i$, as for the [simple work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md). Write $\mathrm{dep}^{-1}(v) = \{w \mid v \in \mathrm{dep}(w)\}$, and suppose that $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ are at most a constant $c$ for every node $v$. Suppose that setting $x_i = \bot$, testing whether the work-list is empty, adding a node to it and removing one each take time at most $1$, that retrieving $\mathrm{dep}(v_i)$ and enumerating its members take time at most $1 + |\mathrm{dep}(v_i)|$ together, and that computing $y = f_i(x_1, \dots, x_n)$, comparing $y$ with $x_i$ and assigning $x_i = y$ take time at most $k \ge 1$ together, for every $i$ and every $(x_1, \dots, x_n) \in L^n$.

**Theorem.** The simple work-list algorithm runs in time $O(n \cdot h \cdot k)$, whatever node each iteration removes, with a constant that depends only on $c$. The time to construct the dependency sets is not counted.

## Proof sketch

The initialization and the final test of the work-list take time at most $2n + 1$. Each iteration removes one node from the work-list, which initially holds $n$ nodes. Every time $x_i$ changes it moves strictly up in $L$, so it changes at most $h$ times, and each change adds at most $|\mathrm{dep}(v_i)|$ nodes. So every run performs at most $n + h \sum_{i=1}^{n} |\mathrm{dep}(v_i)| \le n(1 + c h)$ iterations, and an iteration that removes $v_i$ takes time at most $2 + k$, plus $1 + 2|\mathrm{dep}(v_i)|$ to retrieve $\mathrm{dep}(v_i)$, enumerate it and add its members if $x_i$ changes, so at most $(4 + 2c) k$.

## Comparison with the source

Møller and Schwartzbach state the bound on p. 61 when “$|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ are bounded by a constant for all nodes $v$”, with $k$ “the worst-case time required to compute a constraint function $f_i(x_1, \dots, x_n)$”, and Exercise 5.20 there, which asks for a proof of the bound, finds it “reasonable to assume that the work-list operations ‘add’ and ‘removeNext’ take constant time”. Here $k$ also covers comparing the computed value with $x_i$ and assigning it; setting the initial values and testing the work-list for emptiness take constant time too; and time is counted so that these constant-time operations take at most $1$ and $k \ge 1$. The source takes $\mathrm{dep}$ as given, and the theorem here does not count the time to construct it either. The source does not state the time to retrieve $\mathrm{dep}(v_i)$ and enumerate its members. For its bound it suffices that this time be $O(1 + |\mathrm{dep}(v_i)|)$, as for dependency lists, here at most $1 + |\mathrm{dep}(v_i)|$ in the units above, but the bounds on $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ alone do not: for the constraints $x_1 = \mathrm{true}$ and $x_{i+1} = x_i$ over the Booleans with $\mathrm{false} \sqsubset \mathrm{true}$, and with $\mathrm{dep}(v_i) = \{v_{i+1}\}$ for $i < n$ and $\mathrm{dep}(v_n) = \emptyset$, each stored as a bit vector of length $n$ and enumerated by scanning it, each $x_i$ changes once and the enumerations alone take time $\Theta(n^2)$, while $h = c = 1$ and $k$ is constant. The conditions $n \ge 1$ and $h \ge 1$ are not in the source: for $h = 0$ the algorithm still performs $n$ iterations while $n \cdot h \cdot k = 0$. The proof uses only the bound on $|\mathrm{dep}(v)|$.

## Depends on

- [One iteration of the simple work-list algorithm](step.md)
- [Monotone frameworks and the work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md)
- [Complete lattice](../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/spa.pdf>, archived at <https://web.archive.org/web/20261015192618/https://cs.au.dk/~amoeller/spa/spa.pdf>, Section 5.3, pp. 60–61 (the map $\mathrm{dep}$, its inverse $\mathrm{dep}^{-1}$ and the procedure SimpleWorkListAlgorithm on p. 60; the bound $O(n \cdot h \cdot k)$ and Exercise 5.20 on p. 61)
