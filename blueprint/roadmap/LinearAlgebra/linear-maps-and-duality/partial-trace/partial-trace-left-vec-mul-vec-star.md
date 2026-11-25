# Left partial trace of a rank-one matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $m$ and $n$ be finite index sets, and let
$u \in \mathbb{K}^{m \times n}$ be a vector indexed by pairs $(i, j)$. For each $i \in m$ let
$u_{i\cdot} = (u(i, j))_{j \in n}$ be the $i$-th slice of $u$. Then the partial trace over the first
factor of the rank-one positive semidefinite matrix $u u^*$ is

$$\operatorname{tr}_1(u u^*) = \sum_{i \in m} u_{i\cdot}\, u_{i\cdot}^*,$$

a sum of rank-one positive semidefinite $n \times n$ matrices. Here
$\operatorname{tr}_1(X)_{j j'} = \sum_{i} X_{(i, j), (i, j')}$.
