# Deterministic and randomized LOCAL complexity of an LCL problem

For an LCL problem $\Pi$ and a class of graphs $\mathcal{G}$ (for example bounded-degree trees or general bounded-degree graphs), assume $\Pi$ is totally solvable on $\mathcal{G}$: every input-labelled graph of $\mathcal{G}$ admits a solution (otherwise restrict $\mathcal{G}$ to the feasible inputs). In both models every vertex knows $n$, $\Delta$, its degree and a port numbering of its incident edges. The deterministic complexity $D_\Pi(n)$ is the least $t(n)$ such that some deterministic LOCAL algorithm solves $\Pi$ on every $n$-vertex graph of $\mathcal{G}$ with distinct identifiers in $\{1, \dots, n^{c}\}$ within $t(n)$ rounds. The randomized complexity $R_\Pi(n)$ is the least $t(n)$ such that some randomized LOCAL algorithm solves $\Pi$ on every $n$-vertex graph of $\mathcal{G}$ within $t(n)$ rounds with probability at least $1 - 1/n$; here vertices have no identifiers but unbounded private random bits, so they can generate random identifiers of $O(\log n)$ bits that are distinct with high probability, the failure probability being charged to the error allowance. Always $R_\Pi(n) \le D_\Pi(n)$, since generating identifiers costs no rounds, and $D_\Pi(n) = O(n)$ on connected graphs, since a vertex can gather the whole graph and all vertices then output their parts of the same canonical solution, determined by the identifiers, which exists by total solvability.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)

## Sources

- Y.-J. Chang, T. Kopelowitz, S. Pettie, "An Exponential Separation between Randomized and Deterministic Complexity in the LOCAL Model", FOCS 2016; SIAM Journal on Computing 48(1) (2019), arXiv:1602.08166, Section 1.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
