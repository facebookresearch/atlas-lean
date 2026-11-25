# Csiszar kullback pinsker of support

Let $\alpha$ be a finite set and let $x, y : \alpha \to \mathbb{R}$ be probability vectors: $x_a \ge 0$, $y_a \ge 0$ for every $a$, and $\sum_a x_a = \sum_a y_a = 1$. Suppose $x_a = 0$ whenever $y_a = 0$. Then

$$\Big(\sum_{a \in \alpha} \lvert x_a - y_a \rvert\Big)^2 \le 2 \sum_{a \in \alpha} x_a \ln \frac{x_a}{y_a},$$

where terms with $x_a = 0$ contribute $0$. Zero coordinates are allowed; the support hypothesis rules out infinite divergence.
