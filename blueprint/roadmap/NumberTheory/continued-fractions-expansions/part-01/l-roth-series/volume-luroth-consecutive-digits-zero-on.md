# Zero-one law for functions of consecutive Lüroth digits

Let $m \in \mathbb{N}$, let $F$
be a real-valued function on $m$-tuples of natural numbers and let $(\Psi(n))_{n \ge 0}$ be a
real sequence. For $y \in \mathbb{R}$ put

$$H(y) = \sum_{a} \prod_{i=1}^{m} \frac{1}{a_i (a_i - 1)} \in [0, \infty],$$

the sum running over the $a = (a_1, \dots, a_m) \in \mathbb{N}^m$ with every $a_i \ge 2$ and
$F(a) \ge y$. Write $d_k(x)$ for the $k$-th Lüroth digit of $x$ and let $E$ be the set of
$x \in (0, 1]$ such that $F(d_{n+1}(x), \dots, d_{n+m}(x)) \ge \Psi(n)$ for infinitely many
$n$. If $\sum_{n \ge 0} H(\Psi(n)) < \infty$ then $E$ has Lebesgue measure $0$, and if
$\sum_{n \ge 0} H(\Psi(n)) = \infty$ then $E$ has Lebesgue measure $1$.

Unlike the paper, $F$ and $\Psi$ need not be positive.

## Sources

- Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 3, with `H` from (4) (`integers-2024-A67-thm-3`).
