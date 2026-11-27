# Factorization of a Bayesian network

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a nonempty type
$\alpha$, with joint distribution $P$, and write $p_k(\cdot \mid z)$ for the table of node $k$ at
values $z$ of its parents. For every $x \in \alpha^n$,

$$P(x) = \prod_{k = 0}^{n - 1} p_k(x_k \mid x_{\mathrm{pa}(k)}),$$

the product over the nodes of the probability of the node's value given the values of its
parents.
