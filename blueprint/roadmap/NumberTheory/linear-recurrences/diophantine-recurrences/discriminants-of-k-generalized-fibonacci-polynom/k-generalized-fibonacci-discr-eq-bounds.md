# Absolute bounds on solutions of Luca's discriminant equation

Let $k > 100$ be a natural
number and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for every integer $n$ with
$2 - k \le n \le 0$, $F(1) = 1$, and $F(n) = F(n-1) + F(n-2) + \cdots + F(n-k)$ for every
integer $n \ge 2$ (the $k$-generalized Fibonacci sequence). If a natural number $n$ satisfies
$F(n)\,(k-1)^2 = 2^{k+1} k^k - (k+1)^{k+1}$, then $k < 2 \cdot 10^{16}$ and
$n < 1.5 \cdot 10^{18}$.

The equation is the paper's equation (7) multiplied by $(k-1)^2$.

## Sources

- Florian Luca, *On the Discriminant of the k-Generalized Fibonacci Polynomial, II*, The Fibonacci Quarterly 62 (2024), no. 3, Lemma 2 (`fq-2024-luca02082024-lem-2`). Equation (7) is written after multiplying by `(k-1)^2`, as in `kGeneralizedFibonacci_discr_eq_index_bounds`; by Theorem 1 the hypotheses are never met.
