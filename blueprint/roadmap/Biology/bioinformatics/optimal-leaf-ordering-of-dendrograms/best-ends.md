# Bar-Joseph–Gifford–Jaakkola dynamic program for leaf ordering

For a similarity $S$, the table $M_t(i, j)$ of a dendrogram $t$ is defined recursively: for a leaf $a$, $M_t(i, j) = 0$ if $i = j = a$ and $-\infty$ otherwise; for a merge of $l$ and $r$, $M_t(i, j)$ is the maximum of the [join](join-ends.md) of $(M_l, M_r)$ over the leaves $(L_l, L_r)$ and the join of $(M_r, M_l)$ over $(L_r, L_l)$, at $(i, j)$, where $L_l, L_r$ are the [leaves](leaves.md) of $l$ and $r$.
