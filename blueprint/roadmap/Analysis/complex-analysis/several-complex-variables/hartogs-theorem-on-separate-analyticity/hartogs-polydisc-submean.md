# Sub-mean-value inequality on a polydisc

Let $n \in \mathbb{N}$, let
$u : \mathbb{C}^n \to \mathbb{R}$ be continuous, let $c \in \mathbb{C}^n$ and $R > 0$. Write
$\overline{P}(c, R) = \{x \in \mathbb{C}^n : |x_j - c_j| \le R \text{ for all } j\}$ for the
closed polydisc, and for $x \in \mathbb{C}^n$ and $w \in \mathbb{C}$ write $x_{j \leftarrow w}$
for $x$ with its $j$-th coordinate replaced by $w$. Suppose that for every
$x \in \overline{P}(c, R)$, every coordinate $j$ and every $r$ with $0 < r \le R$,

$$u(x) \le \frac{1}{2\pi} \int_0^{2\pi} u(x_{j \leftarrow x_j + r e^{i\theta}}) \, d\theta.$$

Then $(\pi R^2)^n \, u(c) \le I(u, c, R)$, where $\pi R^2$ is the area of a disc of radius $R$
and $I(u, c, R)$ is the iterated polydisc integral of $u$ about $c$ with radius $R$.
