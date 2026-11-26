# McDiarmid's inequality on a finite product space

Let $\alpha_1, \dots, \alpha_n$ be finite nonempty sets and, for each $i$, let $p_i : \alpha_i \to \mathbb{R}$ be a probability vector ($p_i(a) \ge 0$ and $\sum_{a} p_i(a) = 1$). Give $\prod_i \alpha_i$ the product weights $w(x) = \prod_{i} p_i(x_i)$. Let $f : \prod_i \alpha_i \to \mathbb{R}$ and $c_1, \dots, c_n \in \mathbb{R}$ satisfy the bounded-differences condition: $|f(x) - f(y)| \le c_i$ whenever $x$ and $y$ differ only in coordinate $i$. Write $\bar{f} = \sum_{y} w(y) f(y)$ for the mean. Assume $c_i \ge 0$ for all $i$. Then for every $t > 0$,

$$\sum_{x \,:\, f(x) - \bar{f} \ge t} w(x) \le \exp\Bigl( -\frac{2 t^2}{\sum_{i} c_i^2} \Bigr),$$

with the convention $x / 0 = 0$, so the right-hand side is $1$ when $\sum_i c_i^2 = 0$.
