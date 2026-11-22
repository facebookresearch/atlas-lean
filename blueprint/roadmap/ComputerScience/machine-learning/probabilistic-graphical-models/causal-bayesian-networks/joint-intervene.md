# The truncated factorization

**The truncated factorization** (Pearl 2009, eq. (3.10)): let $B$ be a Bayesian network on the
nodes $0, \dots, n - 1$ with values in a nonempty type $\alpha$, and write $p_j(\cdot \mid z)$ for
the table of node $j$. After $\mathrm{do}(X_k = a)$ the joint distribution is

$$P_{\mathrm{do}(X_k = a)}(x) = \begin{cases} \prod_{j \ne k} p_j(x_j \mid x_{\mathrm{pa}(j)}) & \text{if } x_k = a, \\ 0 & \text{otherwise}, \end{cases}$$

the product of the tables of all nodes other than $k$.
