# The factored update in posterior form

For all $T$, sequences, valid parameters $\theta$, states $s$ and marks $j$,

$$m_1(s, j) = \sum_{n=1}^{N} \sum_{z} p_\theta(z \mid x^{(n)})\, \#\{t \le T : z_t = s,\ x^{(n)}_t(j) = 1\},$$

where $m_1$ is the [mark-present count](mark-ones.md) and $p_\theta(z \mid x) = p_\theta(x, z) / \sum_{z'} p_\theta(x, z')$ the posterior of the [joint weight](joint.md).
