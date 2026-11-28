# Sample covariance vanishes on $w$ iff samples project equally on it

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples, with
[sample covariance matrix](../principal-component-analysis/sample-cov.md)
$S$. For every $n$ and every $w \in \mathbb{R}^p$, $S w = 0$ exactly when all samples have the same
projection on $w$:

$$S w = 0 \iff \text{there is } c \in \mathbb{R} \text{ with }
x_i \cdot w = c \text{ for every } i.$$

Then all samples lie in the set $\{x : x \cdot w = c\}$, an affine hyperplane when $w \ne 0$. For
$w = 0$ both sides hold, with $c = 0$; for $n \le 1$ both sides hold for every $w$.
