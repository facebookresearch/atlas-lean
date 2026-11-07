# Product Bernoulli probability mass function

For a vector $p \in \mathbb{R}^d$ of success
probabilities and a binary vector $x \in \{0, 1\}^d$, the probability of $x$ under the product of
$d$ independent Bernoulli distributions with parameters $p_1, \dots, p_d$ is

$$\prod_{j=1}^{d} p_j^{x_j} (1 - p_j)^{1 - x_j},$$

that is, the product over $j$ of $p_j$ when $x_j = 1$ and of $1 - p_j$ when $x_j = 0$.
