# The defining equation of the stages

Let $E$ be a real normed vector space and $f(t, y)$
a vector field $\mathbb{R} \times E \to E$. For an explicit Runge–Kutta method with tableau $a$
and nodes $c_i = \sum_j a_{ij}$, a time $t$, a state $y \in E$ and a step size $h$, the
stages $k_i$ satisfy
$k_i = f\bigl(t + c_i h, \; y + h \sum_{j < i} a_{ij} k_j\bigr)$ for every stage index $i$.
