# Bernstein's inequality

Let $(\Omega, P)$ be a probability space and let $X_1, \dots, X_n : \Omega \to \mathbb{R}$ be mutually independent measurable random variables with $\mathbb{E}[X_i] = 0$ and $|X_i| \le M$ almost surely for each $i$, where $M \ge 0$. Suppose $\sum_{i=1}^n \mathbb{E}[X_i^2] \le V$. Then for every $t \ge 0$,

$$P\Bigl( \Bigl| \sum_{i=1}^n X_i \Bigr| \ge t \Bigr) \le 2 \exp\Bigl( -\frac{t^2}{2 (V + M t / 3)} \Bigr),$$

with the convention $x / 0 = 0$ when $V + M t / 3 = 0$.
