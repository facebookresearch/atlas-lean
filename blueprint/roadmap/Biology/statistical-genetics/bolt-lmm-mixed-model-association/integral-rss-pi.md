# The expected residual sum of squares of a product of factors

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, and let $q_1, \dots, q_m$ be probability measures on $\mathbb{R}$ such that $b \mapsto b^2$ is $q_j$-integrable for every $j$. Then

$$\int \sum_{i=1}^{n} \Bigl(y_i - \sum_{j=1}^{m} X_{ij} \beta_j\Bigr)^2 \, d(q_1 \otimes \dots \otimes q_m)(\beta) = \mathrm{RSS}(q),$$

where $\mathrm{RSS}(q) = \|y - X\mu\|^2 + \sum_j \|x_j\|^2 v_j$ is the [expected residual sum of squares](expected-rss.md), with $\mu_j$ and $v_j$ the mean and variance of $q_j$.
