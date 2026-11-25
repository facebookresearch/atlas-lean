# The ordered Markov property

Let $B$ be a Bayesian network on the nodes
$0, \dots, n - 1$ with values in a nonempty type $\alpha$, and let $P_m$ be the joint
distribution of the first $m$ nodes of $B$ viewed as a chain of conditional distributions. For
a node $k < n$, write $p_k(\cdot \mid z)$ for its conditional probability table at values $z$
of its parents. Let $y = (y_0, \dots, y_{k-1}) \in \alpha^k$ with $P_k(y) \ne 0$, and write
$y_{\mathrm{pa}(k)}$ for the values of $y$ at the parents of $k$. Then for every $a \in \alpha$,

$$P_{k+1}(y_0, \dots, y_{k-1}, a) / P_k(y) = p_k(a \mid y_{\mathrm{pa}(k)}).$$

In particular, the conditional distribution of node $k$ given all earlier nodes depends only on
the values of its parents.
