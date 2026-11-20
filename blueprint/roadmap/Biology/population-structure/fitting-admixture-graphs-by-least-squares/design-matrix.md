# qpGraph design matrix of basis f4 statistics

Let $w(X, e)$ be lineage weights of populations $X$ on edges $e$, and for each index $i$ of a basis let $A_i, B_i, C_i, D_i$ be populations. The design matrix has entries

$$B_{ie} = \bigl(w(A_i, e) - w(B_i, e)\bigr)\bigl(w(C_i, e) - w(D_i, e)\bigr).$$
