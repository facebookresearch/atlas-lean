# The SLOCAL model and its polylogarithmic class

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. An SLOCAL algorithm with locality $r$ processes the vertices one at a time in an arbitrary (adversarial) order; when vertex $v$ is processed it reads the current states (including outputs and auxiliary memory) of all vertices within distance $r$ of $v$ and writes its own output and state. The class $\mathrm{P}\text{-}\mathrm{SLOCAL}$ consists of the graph problems solvable by SLOCAL algorithms with locality $\mathrm{poly}(\log n)$; likewise $\mathrm{P}\text{-}\mathrm{LOCAL}$ and $\mathrm{P}\text{-}\mathrm{RLOCAL}$ denote problems solvable in $\mathrm{poly}(\log n)$ rounds by deterministic and by randomized (correct with high probability) LOCAL algorithms. Greedy maximal independent set and greedy $(\Delta+1)$-colouring have SLOCAL locality $1$.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- M. Ghaffari, F. Kuhn, Y. Maus, "On the Complexity of Local Distributed Graph Problems", STOC 2017, arXiv:1611.02663.
