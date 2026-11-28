# Blanket factor depends only on the Markov blanket

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ (in topological order) with values in a type $\alpha$, with conditional probability tables $p_k(\cdot \mid x_{\mathrm{pa}(k)})$ and joint distribution $P(x) = \prod_{k} p_k(x_k \mid x_{\mathrm{pa}(k)})$. For a node $i$, let $g_i(x) = p_i(x_i \mid x_{\mathrm{pa}(i)}) \prod_{k \in \mathrm{ch}(i)} p_k(x_k \mid x_{\mathrm{pa}(k)})$ be its blanket factor, and let the Markov blanket of $i$ be its parents, its children and the other parents of its children, excluding $i$. If two assignments $x, x'$ agree on the Markov blanket of $i$, then for every value $a \in \alpha$

$$g_i\big(x[i \mapsto a]\big) = g_i\big(x'[i \mapsto a]\big).$$
