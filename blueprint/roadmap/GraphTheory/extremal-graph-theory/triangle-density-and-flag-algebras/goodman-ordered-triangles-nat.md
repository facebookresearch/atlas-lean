# Goodman's bound for ordered triangles

For a finite simple graph with $n$ vertices, $m$ edges and $T_0$ [ordered triangles](ordered-triangles.md),

$$8m^2 \le nT_0 + 2mn^2.$$

Summing the [common neighbourhood bound](degree-add-degree-le.md) over ordered edges gives $2\sum_v \deg(v)^2 \le T_0 + 2mn$, and Cauchy–Schwarz gives $(2m)^2 = (\sum_v \deg v)^2 \le n\sum_v \deg(v)^2$. With $T_0 = 6T$ this is [Goodman's inequality](goodman.md) $3nT \ge m(4m - n^2)$.
