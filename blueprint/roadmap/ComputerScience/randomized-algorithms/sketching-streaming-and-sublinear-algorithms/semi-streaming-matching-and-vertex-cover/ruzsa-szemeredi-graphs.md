# Ruzsa-Szemerédi graphs: edge sets partitioned into large induced matchings

For integers $r, t \ge 1$, a simple graph $H = (V, E)$ is an *$(r, t)$-Ruzsa–Szemerédi graph* if $E$ is the disjoint union of $t$ matchings $M_1, \dots, M_t$, each of size $r$, such that every $M_i$ is an *induced* matching: the subgraph of $H$ induced by the $2r$ endpoints of $M_i$ has edge set exactly $M_i$. Dense Ruzsa–Szemerédi graphs, with $r$ and $t$ both close to $|V|$, are the standard source of hard instances for single-pass streaming matching lower bounds.

## Sources

- Imre Z. Ruzsa, Endre Szemerédi, "Triple systems with no six points carrying three triangles", Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely 1976), Colloq. Math. Soc. János Bolyai 18 (1978).
- Michael Kapralov, "Space Lower Bounds for Approximating Maximum Matching in the Edge Arrival Model", SODA (2021), arXiv:2103.11669.
