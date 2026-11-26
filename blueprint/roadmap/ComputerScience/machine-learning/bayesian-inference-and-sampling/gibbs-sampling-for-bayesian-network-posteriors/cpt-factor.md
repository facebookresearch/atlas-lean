# Table factor of a node

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$.

For a node $k$ and a full assignment $x \in \alpha^n$, the table factor of $k$ at $x$ is the table entry of the value of $k$ given the values of its parents:

$$f_k(x) = p_k\big(x_k \mid x_{\mathrm{pa}(k)}\big) \in \mathbb{R},$$

so that $P(x) = \prod_k f_k(x)$.
