# Stages computed row by row

Let $E$ be a real normed space, fix an explicit Runge–Kutta
method with $s$ stages, strictly lower-triangular tableau $a$ and nodes $c_i = \sum_j a_{ij}$, a
vector field $f$ assigning a vector $f(t', x) \in E$ to each time $t' \in \mathbb{R}$ and state
$x \in E$, a time $t$, a state $y \in E$ and a step $h \in \mathbb{R}$. The rows $K^{(n)} \in E^s$,
indexed by $0 \le i < s$, are defined by recursion on $n$: $K^{(0)} = 0$, and $K^{(n+1)}_i$ equals
$f\bigl(t + c_i h,\ y + h \sum_{j < n} a_{ij} K^{(n)}_j\bigr)$ when $i = n$ and equals
$K^{(n)}_i$ when $i \ne n$. Only the entries of $K^{(n)}$ with index less than $n$ are filled in;
the others are $0$.
