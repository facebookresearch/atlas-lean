# The posterior-average step maximizes the EM objective over weights

Let $Z$ be a nonempty finite set, let $f(x, z)$ be positive real numbers indexed by observations $x$ and latent values $z \in Z$, and let $x_1, \dots, x_N$ be data. For strictly positive weights $w$ on $Z$ (with $w(z) > 0$ for every $z$ and $\sum_{z \in Z} w(z) = 1$) write $p_w(x, z) = w(z)\,f(x, z)$ for the weight-times-likelihood joint model and $p_w(z \mid x) = p_w(x, z) / \sum_{z' \in Z} p_w(x, z')$ for its posterior. Write $m_w(z) = \sum_{n=1}^N p_w(z \mid x_n)$ for the expected mass of $z$ under the posteriors. Let $Q(w' \mid w) = \sum_{n=1}^N \sum_{z \in Z} p_w(z \mid x_n) \log p_{w'}(x_n, z)$ be the [EM objective](em-q.md) of this model. If $N \ge 1$, then for all strictly positive weights $w$ and $w'$,

$$Q(w' \mid w) \le Q(w^+ \mid w), \qquad w^+(z) = \frac{m_w(z)}{N},$$

so the [posterior-average step](weight-step.md) maximizes $Q(\cdot \mid w)$ over strictly positive weights: it is an M-step for the mixture weights.
