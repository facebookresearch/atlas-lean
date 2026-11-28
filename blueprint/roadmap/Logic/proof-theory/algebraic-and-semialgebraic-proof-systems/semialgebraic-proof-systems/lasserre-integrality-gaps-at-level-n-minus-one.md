# Integrality gaps of the 0/1 Lasserre hierarchy at level n−1

The Lasserre (Sum-of-Squares) relaxation of an $n$-variable 0/1 problem is exact at level $n$; a 0/1 integer linear program can still have an integrality gap at level $n-1$ only if every constraint cuts off a single vertex of the cube, and an unconstrained problem only if its objective has degree $n$.

Let $\mathbb{P}$ be the problem $\min\{f(x) : x \in \{0,1\}^n, \; g_\ell(x) \ge 0 \text{ for } \ell \in [m]\}$ with $f$ multilinear and every $g_\ell$ linear. For $y \in \mathbb{R}^{\mathcal{P}(N)}$, $N = [n]$, the $t$-moment matrix $M_t(y)$ has $(I, J)$-entry $y_{I \cup J}$ for $|I|, |J| \le t$, and the shift $g * y$ has entries $(g * y)_I = \sum_i g_i y_{I \cup \{i\}} + g_0 y_I$. The **Lasserre relaxation at level $t$** is

$$
\mathrm{LAS}_t(\mathbb{P}) : \quad \min\Big\{ \sum_{I \subseteq N} f_I y_I \;:\; y_\emptyset = 1, \; M_{t+d}(y) \succeq 0, \; M_t(g_\ell * y) \succeq 0 \text{ for } \ell \in [m] \Big\},
$$

with $d = 0$ if $m = 0$ and $d = 1$ otherwise; it has an integrality gap when its optimum is below the integral optimum. A constraint $g(x) \ge 0$ is **single vertex cutting** (SVC) if exactly one $I \subseteq N$ has $g(x_I) < 0$ and $g(x_J) > 0$ for every other $J$, where $x_I$ is the indicator vector of $I$.

**Theorem.**

1. If $\mathbb{P}$ is a 0/1 integer linear program and $\mathrm{LAS}_{n-1}(\mathbb{P})$ has an integrality gap, then all constraints of $\mathbb{P}$ (after removing those satisfied by every integral point) are SVC constraints. More precisely, a gap exists if and only if there are values $y^N_I > 0$ ($I \subseteq N$) with $\sum_I y^N_I = 1$ such that for each $\ell$ there is exactly one $K_\ell$ with $g_\ell(x_{K_\ell}) y^N_{K_\ell} < 0$, $g_\ell(x_J) y^N_J > 0$ for all $J \ne K_\ell$, $\sum_I 1/(g_\ell(x_I) y^N_I) \le 0$, and $\sum_I y^N_I f(x_I)$ is below the integral optimum.
2. If $\mathbb{P}$ is unconstrained and $f$ has an integrality gap at level $n-1$, then $f$ is a multivariate polynomial of degree $n$; in particular no $k$-ary Boolean CSP with $k < n$ has a gap at level $n-1$.

## Proof sketch

At level $n$ the moment matrix is congruent to the diagonal matrix of the values $y^N_I = \sum_{H \subseteq N \setminus I} (-1)^{|H|} y_{H \cup I}$, which then form a probability distribution on $\{0,1\}^n$; at level $n-1$ the relevant matrices differ from a diagonal matrix by a rank-one matrix, and an eigenvalue analysis of these almost diagonal matrices gives the conditions. Consequences: $n$ levels are needed to detect that a polytope given by exponentially many SVC constraints contains no integer point (the earlier example of Grigoriev needed $\lfloor n/2 \rfloor$ levels), and a simple Min Knapsack instance has an unbounded integrality gap at level $n-1$, improving Cheung's $1 + 1/n$. The degree-$n$ statement uses Fourier analysis on $\{-1,1\}^n$.

## Depends on

None.

## Proof depends on

None.

## Sources

- Adam Kurpisz, Samuli Leppänen, Monaldo Mastrolilli, "On the hardest problem formulations for the 0/1 Lasserre hierarchy", *Mathematics of Operations Research* 42(1), 2017, https://doi.org/10.1287/moor.2016.0797; numbering of arXiv:1510.01891v1 (Definitions 1 and 2, Theorem 6, Corollary 7, Corollary 9, Theorems 10 and 11).
