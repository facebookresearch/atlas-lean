# Rising-factorial weighted sums via iterated antiderivatives

Let $N$ and $s$ be natural
numbers, $a_0, \dots, a_N$ real numbers and $f(y) = \sum_{k=0}^{N} a_k y^k$. Let
$I_0, I_1, I_2, \dots$ be functions $\mathbb{R} \to \mathbb{R}$ with $I_0 = f$ such that for every
$j \ge 0$ the function $I_{j+1}$ is differentiable on $\mathbb{R}$ with derivative $I_j$ (the
constants of integration are arbitrary). Write $m^{(i)} = m(m+1)\cdots(m+i-1)$ for the rising
factorial. Then for every real number $x$,

$$\sum_{k=0}^{N} \frac{a_k\, x^{k+s}}{(k+1)^{(s)}} =
I_s(x) - \sum_{j=1}^{s} \frac{I_j(0)\, x^{s-j}}{(s-j)!}.$$

The source assumes $s > 0$; for $s = 0$ the identity reads $f(x) = I_0(x)$.

## Sources

- Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.2).
