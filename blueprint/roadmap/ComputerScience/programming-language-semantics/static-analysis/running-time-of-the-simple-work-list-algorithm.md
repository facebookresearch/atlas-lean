# Running time of the simple work-list algorithm

Let $L$ be a complete lattice of finite height $h \ge 1$, the largest number of strict steps $a_0 \sqsubset a_1 \sqsubset \cdots \sqsubset a_h$ in a chain of $L$. Let constraint functions $f_1, \dots, f_n : L^n \to L$ of the $n \ge 1$ nodes $v_1, \dots, v_n$ of a control-flow graph have a monotone combined function, and let dependency sets $\mathrm{dep}(v_i)$ contain every $v_j$ for which $f_j$ depends on $x_i$, as for the [simple work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md). Write $\mathrm{dep}^{-1}(v) = \{w \mid v \in \mathrm{dep}(w)\}$, and suppose that $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ are at most a constant $c$ for every node $v$. Suppose that setting $x_i = \bot$, testing whether the work-list is empty, adding a node to it and removing one each take time at most $1$, and that computing $y = f_i(x_1, \dots, x_n)$, comparing $y$ with $x_i$ and assigning $x_i = y$ take time at most $k \ge 1$ together, for every $i$ and every $(x_1, \dots, x_n) \in L^n$.

**Theorem.** The simple work-list algorithm runs in time $O(n \cdot h \cdot k)$, whatever node each iteration removes, with a constant that depends only on $c$.

## Proof sketch

The initialization and the final test of the work-list take time at most $2n + 1$. Each iteration removes one node from the work-list, which initially holds $n$ nodes. Every time $x_i$ changes it moves strictly up in $L$, so it changes at most $h$ times, and each change adds at most $|\mathrm{dep}(v_i)|$ nodes. So every run performs at most $n + h \sum_{i=1}^{n} |\mathrm{dep}(v_i)| \le n(1 + c h)$ iterations, and an iteration that removes $v_i$ takes time at most $2 + k + |\mathrm{dep}(v_i)| \le (3 + c) k$.

## Comparison with the source

Møller and Schwartzbach state the bound for $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ bounded by a constant, with $k$ the worst-case time to compute a constraint function, and take adding to and removing from the work-list as constant time in Exercise 5.20. Here $k$ also covers comparing the computed value with $x_i$ and assigning it; setting the initial values and testing the work-list for emptiness take constant time too; and time is counted so that these constant-time operations take at most $1$ and $k \ge 1$. The conditions $n \ge 1$ and $h \ge 1$ are not in the source: for $h = 0$ the algorithm still performs $n$ iterations while $n \cdot h \cdot k = 0$. The proof uses only the bound on $|\mathrm{dep}(v)|$.

## Depends on

- [One iteration of the simple work-list algorithm](step.md)
- [Monotone frameworks and the work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>, Section 5.3, p. 61 (the bound $O(n \cdot h \cdot k)$ for bounded $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$, and Exercise 5.20 with constant-time work-list operations)
