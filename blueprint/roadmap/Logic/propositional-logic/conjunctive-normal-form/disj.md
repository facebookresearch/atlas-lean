# Disjunction of two CNFs

For CNFs $\varphi = C_1 \land \dots \land C_m$ and
$\psi = D_1 \land \dots \land D_n$, their disjunction is the CNF with one clause $C_i \lor D_j$
(the literals of $C_i$ followed by those of $D_j$) for each pair $(i, j)$, listed with $i$ as the
outer and $j$ as the inner index. It expresses $(\bigwedge_i C_i) \lor (\bigwedge_j D_j)$ as
$\bigwedge_{i,j} (C_i \lor D_j)$.
