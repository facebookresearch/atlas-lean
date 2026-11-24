# Decomposition of the EM objective for the Bernoulli mixture

Let
$x_1, \dots, x_N \in \{0, 1\}^d$ be data and let $\theta$ and $\theta'$ be valid parameters of a
mixture of $K$ products of $d$ Bernoulli distributions (positive mixing weights summing to one and
success probabilities in $(0, 1)$), where $\theta'$ has mixing weights $\pi'_k$ and success
probabilities $p'_{kj}$. Write $p_\theta(x, k)$ for the joint probability of $x$ and component $k$
under $\theta$ (the mixing weight of $k$ times the product Bernoulli probability of $x$),
$r_{nk} = p_\theta(k \mid x_n) = p_\theta(x_n, k) / \sum_l p_\theta(x_n, l)$ for the posterior
probability of component $k$ given $x_n$, $N_k = \sum_n r_{nk}$, and $A_{kj}$ and $B_{kj}$ for the
sums of $r_{nk}$ over the points $x_n$ whose $j$-th coordinate $x_{nj}$ is $1$ and is $0$
respectively. Then the EM objective
$Q(\theta' \mid \theta) = \sum_n \sum_k r_{nk} \log p_{\theta'}(x_n, k)$ equals

$$\sum_{k=1}^{K} \Big( N_k \log \pi'_k + \sum_{j=1}^{d} \big( A_{kj} \log p'_{kj} +
B_{kj} \log (1 - p'_{kj}) \big) \Big).$$

The first term depends only on the mixing weights and each remaining term on a single $p'_{kj}$.
