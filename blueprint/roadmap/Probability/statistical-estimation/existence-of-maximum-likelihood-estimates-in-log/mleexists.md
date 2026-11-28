# Existence of the MLE in the no-3-way interaction model

Let $I, J, K \in \mathbb{N}$ and let $n = (n_{ijk})$ be an $I \times J \times K$ table of counts in $\mathbb{N}$. The maximum likelihood estimate of $n$ under the no-3-way interaction model exists if there is a table $m = (m_{ijk})$ of real numbers with $m_{ijk} > 0$ for all $i, j, k$ and the same two-way margins as $n$:

$$\sum_k m_{ijk} = \sum_k n_{ijk}, \qquad \sum_j m_{ijk} = \sum_j n_{ijk}, \qquad \sum_i m_{ijk} = \sum_i n_{ijk}$$

for all $i, j$, all $i, k$ and all $j, k$ respectively. This is Haberman's criterion: the observed margins lie in the relative interior of the marginal cone.
