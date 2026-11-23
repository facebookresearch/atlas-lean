# Vanishing estimator variance under bounded covariance row sums

Let $\mu$ be a finite measure and, along a filter on an index set, let $N_n$ and $M_n$ be natural
numbers, $\ell_n \in \mathbb{R}^{M_n}$ real vectors (for instance LD scores) and
$\chi_{n,1}, \dots, \chi_{n,M_n}$ square-integrable statistics. Suppose that for some real $R$ all
absolute covariance row sums satisfy $\sum_k |\operatorname{Cov}(\chi_{n,j}, \chi_{n,k})| \leq R$,
that for some $c > 0$ the spread satisfies $S_{\ell_n \ell_n} \geq c M_n$ for all $n$, and that
$M_n / N_n^2 \to 0$. Then the variance of the estimator $\hat h^2_n = \hat b_n M_n / N_n$, with
$\hat b_n$ the least-squares slope of $(\chi_{n,j})_j$ on $\ell_n$, tends to $0$; variance and
covariances are taken with respect to $\mu$.
