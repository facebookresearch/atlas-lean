# Weighted sum over nonintersecting path families

Let $R$ be a commutative semiring, let
$x = (x_j)_{j \in \mathbb{N}}$ be a family of elements of $R$, let $n \in \mathbb{N}$, and let
$p = (p_1, \dots, p_n)$ and $q = (q_1, \dots, q_n)$ be tuples of points of $\mathbb{N}^2$. The
nonintersecting path weight sum of type $(p, q)$ is
$W(p, q) = \sum_L \prod_{i=1}^{n} \operatorname{wt}(L_i)$, the sum taken over all nonintersecting
families $L = (L_1, \dots, L_n)$ in which $L_i$ is a southeast path from $p_i$ to $q_i$ for each
$i$, where $\operatorname{wt}(L_i)$ is the weight of $L_i$ with respect to $x$.

There are only finitely many such families. If for some $i$ there is no southeast path from
$p_i$ to $q_i$, then $W(p, q) = 0$. For $n = 0$ the empty family is the only one, and
$W(p, q) = 1$.
