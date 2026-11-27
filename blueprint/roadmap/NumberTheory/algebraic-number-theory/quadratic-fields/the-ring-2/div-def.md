# Rounding division on $\mathbb{Z}(\sqrt{-2})$

Let $x, y \in \mathbb{Z}[\sqrt{-2}]$ with
$y = c + d\sqrt{-2}$, let $\bar{y} = c - d\sqrt{-2}$ be its conjugate and $N(y) = c^2 + 2d^2$ its
norm, and write $x\bar{y} = u + v\sqrt{-2}$ with $u, v \in \mathbb{Z}$. The quotient is $x / y = \operatorname{round}(u / N(y)) +
\operatorname{round}(v / N(y))\sqrt{-2}$, where $u / N(y)$ and $v / N(y)$ are computed in
$\mathbb{Q}$ (division by $0$ gives $0$) and $\operatorname{round}$ sends a rational number to
the nearest integer, rounding halves up.
