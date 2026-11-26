# Right partial trace of a rank-one matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $m$ and $n$ be finite index sets, and let
$u \in \mathbb{K}^{m \times n}$ be a vector indexed by pairs $(i, j)$. For each $j \in n$ let
$u_{\cdot j} = (u(i, j))_{i \in m}$ be the $j$-th slice of $u$. Then the partial trace over the
second factor of the rank-one positive semidefinite matrix $u u^*$ is

$$\operatorname{tr}_2(u u^*) = \sum_{j \in n} u_{\cdot j}\, u_{\cdot j}^*,$$

a sum of rank-one positive semidefinite $m \times m$ matrices. Here
$\operatorname{tr}_2(X)_{i i'} = \sum_{j} X_{(i, j), (i', j)}$.
