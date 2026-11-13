# McDiarmid's inequality when the sensitivities are not all zero

Let $n \in \mathbb{N}$,
let $\alpha$ be a finite nonempty set with weights $p : \alpha \to \mathbb{R}$ such that
$p(a) \ge 0$ for all $a$ and $\sum_{a \in \alpha} p(a) = 1$, and give each $x \in \alpha^n$ the
product weight $P(x) = \prod_{i\lt n} p(x_i)$. Let $f : \alpha^n \to \mathbb{R}$ and let
$c_0, \dots, c_{n-1} \ge 0$ be such that $|f(x) - f(y)| \le c_i$ whenever $x, y \in \alpha^n$
agree in every coordinate other than $i$, and suppose $\sum_{i\lt n} c_i^2 > 0$. Write
$\mu = \sum_{x \in \alpha^n} P(x) f(x)$ for the mean of $f$. Then for every real $t > 0$,

$$
\sum_{x \in \alpha^n,\ f(x) - \mu \ge t} P(x) \le \exp\Big(-\frac{2t^2}{\sum_{i\lt n} c_i^2}\Big).
$$
