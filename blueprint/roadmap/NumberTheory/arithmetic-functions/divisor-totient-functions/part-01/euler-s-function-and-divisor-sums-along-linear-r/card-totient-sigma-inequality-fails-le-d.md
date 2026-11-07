# Euler's function and the sum of divisors along a linear recurrence

Let
$(U_n)_{n \ge 1}$ be a sequence of integers satisfying
$U_{m+k} = c_0 U_m + c_1 U_{m+1} + \dots + c_{k-1} U_{m+k-1}$ for all $m \ge 1$, with integer
coefficients $c_i$, where the order $k$ of this recurrence is minimal among all linear recurrences
with integer coefficients satisfied by $(U_n)_{n \ge 1}$. Suppose the recurrence is nondegenerate:
no complex root of its characteristic polynomial $X^k - c_{k-1} X^{k-1} - \dots - c_0$ is $0$, and
no quotient of two distinct complex roots is a root of unity. Suppose also that there is no
polynomial $P$ with rational coefficients such that $|U_n| = P(n)$ for all sufficiently large $n$.
Let $\varphi$ be Euler's totient function and $\sigma(m)$ the sum of the positive divisors of $m$,
with $\varphi(0) = \sigma(0) = 0$. Then there are real constants $x_0$ and $C$ such that for every
real $x \ge x_0$, the number of integers $1 \le n \le x$ with $\varphi(|U_n|) < |U_{\varphi(n)}|$
is at most $C x / \log x$, and the number of integers $1 \le n \le x$ with
$|U_{\sigma(n)}| < \sigma(|U_n|)$ is at most $C x / \log x$.

## Sources

- Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2, Theorem 1 (`fq-2024-luca09162024rev2-thm-1`).
