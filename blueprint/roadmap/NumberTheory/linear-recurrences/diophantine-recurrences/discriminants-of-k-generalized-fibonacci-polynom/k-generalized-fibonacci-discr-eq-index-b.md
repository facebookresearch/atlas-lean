# Bounds on the index in Luca's discriminant equation

Let $k > 100$ be a natural number
and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$ (the $k$-generalized Fibonacci sequence). Write
$L = (k \log k - 2 \log(k-1)) / \log 2$, where $\log$ is the natural logarithm. If a natural
number $n$ satisfies $F(n)\,(k-1)^2 = 2^{k+1} k^k - (k+1)^{k+1}$, then
$k + 1.99 + L < n < k + 3.01 + L$.

The equation is the paper's equation (7),
$F(n) = (2^{k+1} k^k - (k+1)^{k+1}) / (k-1)^2$, multiplied by $(k-1)^2$.

## Sources

- Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*, The Fibonacci Quarterly 62 (2024), no. 3, Lemma 1. Equation (7) is written after multiplying by `(k-1)^2`; `F^{(k)}` is given by its defining properties as in `abs_discr_kGeneralizedFibonacciPolynomial_mem_iff`. By Theorem 1 the equation has no solution with `k > 100`, so this intermediate bound is implied by that statement.
