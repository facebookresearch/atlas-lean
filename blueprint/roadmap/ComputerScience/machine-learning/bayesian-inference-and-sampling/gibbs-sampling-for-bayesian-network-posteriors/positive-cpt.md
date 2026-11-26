# Strictly positive conditional probability tables

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$.

The network has positive tables when every entry of every table is strictly positive: for every node $k$, every assignment $u$ of values to the parents of $k$ and every value $a \in \alpha$,

$$p_k(a \mid u) > 0 .$$
