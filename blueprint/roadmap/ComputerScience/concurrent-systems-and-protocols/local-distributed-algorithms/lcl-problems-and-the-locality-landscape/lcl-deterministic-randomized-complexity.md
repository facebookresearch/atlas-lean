# Deterministic and randomized LOCAL complexity of an LCL problem

For an LCL problem $\Pi$ and a class of graphs $\mathcal{G}$ (for example bounded-degree trees or general bounded-degree graphs), the deterministic complexity $D_\Pi(n)$ is the least $t(n)$ such that some deterministic LOCAL algorithm solves $\Pi$ on every $n$-vertex graph of $\mathcal{G}$ with identifiers in $\{1, \dots, n^{c}\}$ within $t(n)$ rounds. The randomized complexity $R_\Pi(n)$ is the least $t(n)$ such that some randomized LOCAL algorithm (vertices have private random bits; identifiers need not be unique beyond what the model provides) solves $\Pi$ within $t(n)$ rounds with probability at least $1 - 1/n$. Always $R_\Pi(n) \le D_\Pi(n)$, and $D_\Pi(n) = O(n)$ on connected graphs.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)

## Sources

- Y.-J. Chang, T. Kopelowitz, S. Pettie, "An Exponential Separation between Randomized and Deterministic Complexity in the LOCAL Model", FOCS 2016; SIAM Journal on Computing 48(1) (2019), arXiv:1602.08166.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
