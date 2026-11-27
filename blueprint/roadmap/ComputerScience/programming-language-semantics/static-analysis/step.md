# One iteration of the simple work-list algorithm

Let $L$ be a preordered set and $I$ a set of nodes, let $f : L^I \to L^I$ be monotone, the combined function of a monotone framework whose component $f_i(x) = f(x)_i$ is the constraint function of node $i$, and let $\mathrm{dep}(i)$ be a finite set of nodes for each node $i$. A state $(x, W)$ consists of values $x \in L^I$ and a finite set $W$ of nodes, the work-list. One iteration of the simple work-list algorithm removes some node $i \in W$ from the work-list and leads from $(x, W)$ to

- $(x, W \setminus \{i\})$ if $f_i(x) = x_i$, and
- $\bigl(x[i \mapsto f_i(x)], (W \setminus \{i\}) \cup \mathrm{dep}(i)\bigr)$ if $f_i(x) \ne x_i$,

where $x[i \mapsto y]$ agrees with $x$ except that its entry at $i$ is $y$. Every node of $W$ may be the one removed, so the sequences of iterations are the runs of the algorithm for all orders of removal.

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>, Section 5.3, p. 60 (the procedure SimpleWorkListAlgorithm, whose work-list removes an item nondeterministically)
