# Dominated convergence theorem for nonnegative functions

Let $\mu$ be a measure on a set $\alpha$ with a σ-algebra, let $F_1, F_2, \ldots \colon \alpha \to [0, \infty]$ be
measurable, and let $f, g \colon \alpha \to [0, \infty]$ be functions with $\int g \, d\mu < \infty$. Suppose that for
every $n$, $F_n \le g$ almost everywhere, and that $F_n(x) \to f(x)$ for almost every $x \in \alpha$. Then

$$\int F_n \, d\mu \to \int f \, d\mu$$

in $[0, \infty]$. Here the integral of a function $h \colon \alpha \to [0, \infty]$, measurable or not, is the supremum
of $\sum_j c_j \mu(A_j)$ over the simple functions $\sum_j c_j \chi_{A_j} \le h$ with $A_j$ disjoint measurable sets and
$c_j \in [0, \infty]$, so neither $f$ nor $g$ is assumed measurable.
