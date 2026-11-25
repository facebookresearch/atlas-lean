# Monotone frameworks and the work-list algorithm

Let $L$ be a complete lattice of finite height $h$ and let a dataflow analysis of a control-flow graph with nodes $v_1, \dots, v_n$ be given by constraint functions $f_1, \dots, f_n : L^n \to L$, one per node, such that the combined function $f(x_1, \dots, x_n) = (f_1(x_1, \dots, x_n), \dots, f_n(x_1, \dots, x_n))$ is monotone on the product lattice $L^n$. The equation system $x_i = f_i(x_1, \dots, x_n)$ for $i = 1, \dots, n$ then has a unique least solution, the least fixed point $\mathrm{lfp}(f) = \bigsqcup_{i \ge 0} f^i(\bot)$: the chain $\bot \sqsubseteq f(\bot) \sqsubseteq f^2(\bot) \sqsubseteq \cdots$ is increasing because $f$ is monotone, it stabilizes because $L^n$ has finite height, and its limit lies below every fixed point.

Let $\mathrm{dep}(v_i)$ be a set of nodes containing every $v_j$ for which $f_j$ depends on $x_i$. The *simple work-list algorithm* starts from $x_i = \bot$ for all $i$ with a work-list holding all nodes; while the work-list is nonempty it removes some node $v_i$, computes $y = f_i(x_1, \dots, x_n)$, and if $y \ne x_i$ sets $x_i = y$ and adds every node of $\mathrm{dep}(v_i)$ to the work-list. For every order of removal it terminates, since each iteration either moves up in $L^n$ or shrinks the work-list, and it returns $\mathrm{lfp}(f)$. If $|\mathrm{dep}(v)|$ and $|\mathrm{dep}^{-1}(v)|$ are bounded by a constant for all nodes and the work-list operations take constant time, it runs in time $O(n \cdot h \cdot k)$, where $k$ is the worst-case time to compute one constraint function.

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, <https://cs.au.dk/~amoeller/spa/>, Sections 4.4 and 5.3
