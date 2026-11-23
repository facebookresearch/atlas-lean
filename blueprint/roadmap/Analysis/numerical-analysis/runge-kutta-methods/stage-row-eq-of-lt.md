# Partial stage rows agree with the stages

Let $E$ be a real normed vector space and
$f(t, y)$ a vector field $\mathbb{R} \times E \to E$, and fix an explicit Runge–Kutta method,
a time $t$, a state $y \in E$ and a step size $h \in \mathbb{R}$. Index the stages from $0$.
For every natural number $m$ and every stage index $i < m$, the $i$-th entry of the $m$-th
partial row for $f$, $t$, $y$ and $h$ (the row-by-row construction that fills in the stages
with index less than $m$ and sets the rest to $0$) equals the $i$-th stage $k_i$.
