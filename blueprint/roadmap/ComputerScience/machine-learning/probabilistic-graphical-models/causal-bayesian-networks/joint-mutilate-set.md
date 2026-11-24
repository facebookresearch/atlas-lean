# The truncated factorization for a set of nodes

Let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a nonempty type
$\alpha$, write $p_j(\cdot \mid z)$ for the table of node $j$, let $W$ be a finite set of nodes and
$w \in \alpha^n$. The joint distribution of the [mutilated network](mutilate-set.md) of
$\mathrm{do}(X_W = w_W)$ is

$$P_W(x) = \prod_{j \in W} \mathbf{1}[x_j = w_j] \prod_{j \notin W} p_j(x_j \mid x_{\mathrm{pa}(j)}),$$

the product of the tables of the nodes outside $W$ on assignments agreeing with $w$ on $W$, and
$0$ elsewhere.
