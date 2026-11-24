# C-finite polynomial sequences

Let $\sigma$ be a type indexing variables, and write
$\mathbb{Z}[\sigma]$ for the multivariate polynomials with integer coefficients in the variables
$\sigma$. A sequence $a_0, a_1, a_2, \dots$ in $\mathbb{Z}[\sigma]$ is C-finite when there exist
natural numbers $k$ and $N$ and polynomials $p_1, \dots, p_k \in \mathbb{Z}[\sigma]$ such that
for every $n \ge N$

$$
a_{n+k+1} = \sum_{i=1}^{k} p_i \, a_{n+i}.
$$
