# Hausdorff positivity criterion

A real sequence $a$ indexed by $\mathbb{N}^d$ is a positive
moment configuration, that is, there is a finite measure $\mu$ on $\mathbb{R}^d$ with
$a_n = \int_{[0,1]^d} x^n \, d\mu(x)$ for every multi-index $n \in \mathbb{N}^d$, where
$x^n = \prod_i x_i^{n_i}$, if and only if $(\Delta^k a)_n \ge 0$ for all multi-indices $k, n$ with
$k \le n$ coordinatewise, where $\Delta^k a$ is the iterated backward difference of $a$.

The one-dimensional argument extends to the cube by taking products of the polynomials
$x_i^{n_i-k_i}(1-x_i)^{k_i}$. The moment functional takes the value $(\Delta^k a)_n$ on
each such product. Up to positive binomial factors these products form the tensor Bernstein
bases. Positivity on these bases in every degree gives a positive functional on polynomials.
Its positive extension to continuous functions on the cube is represented by a finite measure.

## Sources

- F. Hausdorff, *Summationsmethoden und Momentfolgen I, II*, Math. Z. 9 (1921), for the
  one-dimensional criterion.
- O. Knill, *Some fundamental theorems in mathematics*, §115 “Moments”, p. 52, describes
  positivity in several dimensions. [arXiv:1807.08416v4](https://arxiv.org/pdf/1807.08416v4#page=52)
- Problem `hausdorff_positivity_criterion` of the lean-eval benchmark.
