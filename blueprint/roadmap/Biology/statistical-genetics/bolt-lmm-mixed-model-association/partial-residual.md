# Partial residual of a SNP

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $q_1, \dots, q_m$ be measures on $\mathbb{R}$, and let $j \in \{1, \dots, m\}$. The partial residual of SNP $j$ is the vector $r_j \in \mathbb{R}^n$ with

$$(r_j)_i = y_i - \sum_{k \ne j} X_{ik}\, m(q_k),$$

where $m(q_k)$ is the [mean](mean.md) of $q_k$.
