# Iterated factorials as base-$10$ power towers

Let $k \ge 3$ be a natural number, let
$F_n(k)$ be the $n$-fold iterated factorial of $k$, viewed as a real number, and for a real
number $c$ and $m \ge 0$ let $E_m(10, c)$ be the $m$-fold iterate of $x \mapsto 10^x$ starting
at $c$. Then there are an integer $\ell$, a natural number $N > 0$, a sequence $(c_n)$ of real
numbers and a real number $L$ with the following properties: for every $n \ge N$ we have
$n + \ell \ge 0$, $1 < c_n \le 10$ and $F_n(k) = E_{n+\ell}(10, c_n)$; the sequence
$(c_n)_{n \ge N}$ is strictly increasing and converges to $L$; and
$E_{n+\ell}(10, L) / (F_n(k) \ln F_n(k)) \to 1 / \ln 10$ as $n \to \infty$.

The paper leaves the condition $n + \ell \ge 0$ implicit.

## Sources

- Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer Sequences 28 (2025), Article 25.2.8, Theorem 5 (`jis-2025-25.2.8-thm-5`).
