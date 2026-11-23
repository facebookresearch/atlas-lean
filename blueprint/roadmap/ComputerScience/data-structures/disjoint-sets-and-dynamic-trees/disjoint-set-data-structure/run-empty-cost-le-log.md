# Cost bound $O(n + m \log n)$ from the empty structure

A sequence of set-union operations with $n$ make-sets and $m$ finds (a union counting as two
finds), run from the empty union-find structure with linking by rank and path compression,
has total [cost](step.md) at most $n + m\,(\lfloor \log_2 n \rfloor + 2)$, where
$\lfloor \log_2 0 \rfloor$ is read as $0$.

## Informally uses

- [Cost bound $O(n + m \log n)$ for union by rank with path compression](run-cost-le-log.md): the
  case of the empty starting structure, where the final number of nodes is $n$.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §2, Theorem 2.
