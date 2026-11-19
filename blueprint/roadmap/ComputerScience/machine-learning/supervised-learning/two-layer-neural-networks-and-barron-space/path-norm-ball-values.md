# Path-norm ball on a sample

For a sample $x_1, \dots, x_n \in \mathbb{R}^d$ and $Q \in \mathbb{R}$, this is the set of value
vectors $(f(x_1), \dots, f(x_n))$ of the [two-layer ReLU networks](two-layer-re-lu.md)
$f(x) = \sum_k a_k \max(\langle w_k, x \rangle, 0)$ of any width with [path norm](path-norm.md) at
most $Q$: the set $\mathcal{F}_Q$ of E, Ma and Wu (*A priori estimates*, §5.1) restricted to the
sample.
