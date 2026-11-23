# Vanishing estimator variance under an LD-block model as M grows

Let $\mu$ be a finite measure and, along a filter on an index set, let $N_n$ and $M_n$ be natural
numbers, $\ell_n \in \mathbb{R}^{M_n}$ real vectors (for instance LD scores) and
$\chi_{n,1}, \dots, \chi_{n,M_n}$ statistics satisfying an [LD-block model](ldblock-model.md) with
block size $K$ and variance bound $V$, the same for every $n$. Suppose that $M_n \to \infty$ and
that $N_n \geq \kappa M_n$ and $S_{\ell_n \ell_n} \geq c M_n$ for all $n$, for some $\kappa > 0$ and
$c > 0$. Then the variance of the estimator $\hat h^2_n = \hat b_n M_n / N_n$, with $\hat b_n$ the
least-squares slope of $(\chi_{n,j})_j$ on $\ell_n$, tends to $0$.
