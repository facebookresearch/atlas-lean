# Norm le of modulus

Let $f : [0,1] \to \mathbb{R}$ be continuous with $f(0) = 0$, and let $\delta > 0$. Suppose that $|f(s) - f(t)| \le 1$ whenever $s, t \in [0,1]$ satisfy $|s - t| \le \delta$. Then the sup norm of $f$ satisfies

$$\|f\|_\infty \le \lceil 1/\delta \rceil.$$

The proof chains $m = \lceil 1/\delta \rceil$ steps of length $t/m \le \delta$ from $0$ to $t$.
