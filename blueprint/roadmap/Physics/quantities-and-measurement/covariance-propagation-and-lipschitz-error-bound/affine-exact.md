# For $x \mapsto Ax + b$ the output error is exactly $A\delta$

For a real $m \times n$ matrix $A$, a vector $b \in \mathbb{R}^m$ and vectors
$x, \delta \in \mathbb{R}^n$, the affine map $f(x) = Ax + b$ satisfies

$$f(x + \delta) - f(x) = A\,\delta$$

exactly: the output error depends only on the input error $\delta$, not on $x$, and involves no
approximation. In particular, for every norm on $\mathbb{R}^m$ the size of the output error is
$\|A\,\delta\|$ for every $x$.
