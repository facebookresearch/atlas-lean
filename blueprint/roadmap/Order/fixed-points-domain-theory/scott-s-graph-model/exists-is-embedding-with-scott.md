# Scott's embedding theorem

Every $T_0$ space $X$ with a countable basis embeds topologically in $P(\omega)$ with its Scott topology (D. Scott, *Data types as lattices*, SIAM J. Comput. 5(3) (1976), Theorem 1.6). The proof applies [Scott's embedding map](is-embedding-set-of-mem.md) $x \mapsto \{n \mid x \in U_n\}$, for an enumeration $U_0, U_1, \ldots$ of a countable family of open sets generating the topology; that page states the theorem for this map.

With Scott's extension theorem (Theorem 1.5), this is why $P(\omega)$ is a universal space: every countably based $T_0$ space and every continuous map into $P(\omega)$ can be studied inside $P(\omega)$.

## Informally uses

- [Scott's embedding map](is-embedding-set-of-mem.md): the embedding.

## Background

- [Scott's extension theorem](exists-continuous-extend-with-scott.md): the companion theorem; together they make $P(\omega)$ universal.

## Sources

- D. Scott, *Data types as lattices*, SIAM Journal on Computing 5(3) (1976), 522–587, doi:10.1137/0205037.
