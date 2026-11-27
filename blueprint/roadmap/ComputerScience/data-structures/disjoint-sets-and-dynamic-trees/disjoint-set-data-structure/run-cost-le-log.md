# Cost bound $O(n + m \log n)$ for union by rank with path compression

Starting from any union-find structure obtained by make-set, find and union, a sequence of
operations with $n$ make-sets and $m$ finds, a union counting as two finds, has total
[cost](step.md) at most

$$n + m\,(\lfloor \log_2 N \rfloor + 2),$$

where $N$ is the number of nodes at the end and $\lfloor \log_2 0 \rfloor$ is read as $0$. A make-set costs $1$, a find at most
$\lfloor \log_2 N \rfloor + 1$ because [find paths have at most $\lfloor \log_2 n \rfloor$ edges](iterate-parent-log.md),
and a union at most two such finds plus a link.

## Informally uses

- [Find paths are short under union by rank](find-path-length-le-log.md): each find costs at most
  $\lfloor \log_2 N \rfloor + 1$.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §2, Theorem 2 (the upper bound $O(n + m \log n)$ with linking by rank, from
  Corollary 2); compression does not lengthen find paths.
