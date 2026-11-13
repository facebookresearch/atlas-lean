# Efron–Stein inequality for a finite product weight

Let $\alpha$ be a finite nonempty set,
let $p : \alpha \to \mathbb{R}$ satisfy $p(a) \ge 0$ for every $a \in \alpha$ and
$\sum_{a \in \alpha} p(a) = 1$, let $n \in \mathbb{N}$ and let $f : \alpha^n \to \mathbb{R}$. For
$x = (x_1, \dots, x_n) \in \alpha^n$ write $w(x) = \prod_{j=1}^{n} p(x_j)$, and for a coordinate
$i \in \{1, \dots, n\}$ and $a \in \alpha$ let $x^{(i,a)}$ be $x$ with its $i$-th coordinate
replaced by $a$. Let $\mu = \sum_{x \in \alpha^n} w(x) f(x)$. Then

$$
\sum_{x \in \alpha^n} w(x) \bigl(f(x) - \mu\bigr)^2 \le \frac{1}{2} \sum_{i=1}^{n}
\sum_{x \in \alpha^n} \sum_{a \in \alpha} w(x)\, p(a) \bigl(f(x) - f(x^{(i,a)})\bigr)^2.
$$
