# Darboux normal form

Let $n$ be a natural number and let $e_0, \dots, e_{2n-1}$ be the
standard basis of $\mathbb{R}^{2n}$. A continuous alternating 2-form $\omega$ on $\mathbb{R}^{2n}$
is in Darboux normal form if for all $i, j \in \{0, \dots, n - 1\}$ we have
$\omega(e_i, e_{n+j}) = 1$ when $i = j$ and $0$ otherwise, $\omega(e_i, e_j) = 0$, and
$\omega(e_{n+i}, e_{n+j}) = 0$.

By antisymmetry these conditions determine the form uniquely: it is the standard symplectic form
$\omega_0 = \sum_i dx_i \wedge dx_{n+i}$.
