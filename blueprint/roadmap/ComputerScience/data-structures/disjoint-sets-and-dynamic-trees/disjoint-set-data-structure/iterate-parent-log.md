# Find paths have at most $\lfloor \log_2 n \rfloor$ edges

In every union-find structure with $n$ nodes obtained from the empty one by make-set, find with
path compression and union by rank, following $\lfloor \log_2 n \rfloor$ parent pointers from any
node $i$ reaches the root of $i$: $\mathrm{parent}^{\lfloor \log_2 n \rfloor}(i) =
\mathrm{root}(i)$ (an index that is not a node is its own parent and root, and
$\lfloor \log_2 0 \rfloor$ is read as $0$). Ranks strictly increase along parent pointers and are at most
$\lfloor \log_2 n \rfloor$, so no find path has more than $\lfloor \log_2 n \rfloor$ edges.

## Informally uses

- [Ranks are at most $\lfloor \log_2 n \rfloor$](rank-le-log.md): bounds the rank of every node.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §2, Corollary 2 ("no path has length exceeding $\log n$"), stated there for
  the forest without compression.
