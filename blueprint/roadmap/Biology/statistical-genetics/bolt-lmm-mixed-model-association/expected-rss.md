# Expected residual sum of squares under the variational factors

Let $X$ be a real $n \times m$ matrix with columns $x_j$, let $y \in \mathbb{R}^n$, and let $q_1, \dots, q_m$ be measures on $\mathbb{R}$. Their expected residual sum of squares is

$$\mathrm{RSS}(q) = \sum_{i=1}^{n} \Bigl(y_i - \sum_{j=1}^{m} X_{ij}\, m(q_j)\Bigr)^2 + \sum_{j=1}^{m} \|x_j\|^2\, v(q_j),$$

where $m(q_j)$ is the [mean](mean.md) of $q_j$, $\|x_j\|^2$ the [squared column norm](col-norm-sq.md), and $v(q_j) = \int (b - m(q_j))^2\, dq_j(b)$ the variance of $q_j$, taken to be $0$ when this integral is infinite. For probability factors with finite second moments it is the expectation of $\|y - X\beta\|^2$ under the product of the factors ([expected residual sum of squares of a product](integral-rss-pi.md)).
