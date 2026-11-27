# Conditional independence for finite sets of nodes

Let $\alpha$ be a finite type, $n \in \mathbb{N}$ and $P : \alpha^n \to \mathbb{R}$. For a set
$U$ of nodes and $x \in \alpha^n$, write $P(x_U) = \sum_{y \,:\, y_i = x_i \ (i \in U)} P(y)$ for
the (unnormalized) marginal of $P$ on $U$ at $x$. For finite sets $X, Y, Z$ of nodes, $X$ and
$Y$ are conditionally independent given $Z$ under $P$ if and only if

$$P(x_{X \cup Y \cup Z}) \, P(x_Z) = P(x_{X \cup Z}) \, P(x_{Y \cup Z}) \quad \text{for every } x \in \alpha^n.$$
