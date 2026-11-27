# Iterated Gamma values as power towers

Let $z > 1$ be a real number with
$\Gamma(z) = z$, let $b > e^{1/e}$ and $x > z$ be real numbers, let $\Gamma^n$ be the $n$-fold
iterate of $\Gamma$, and for a real number $c$ and $m \ge 0$ let $E_m(b, c)$ be the $m$-fold
iterate of $y \mapsto b^y$ starting at $c$. Then there are an integer $\ell$, a natural number
$N > 0$, a sequence $(c_n)$ of real numbers and a real number $L$ with the following
properties: for every $n \ge N$ we have $n + \ell \ge 0$, $1 < c_n \le b$ and
$\Gamma^n(x) = E_{n+\ell}(b, c_n)$; the sequence $(c_n)_{n \ge N}$ is strictly increasing and
converges to $L$; and
$E_{n+\ell}(b, L) / ((\Gamma^n(x) - 1) \ln(\Gamma^n(x) - 1)) \to 1 / \ln b$ as $n \to \infty$.

This is a corrected reading of the printed statement: $x > z$ for the printed $x \ge z$ (at
$x = z$ the orbit is constant while $E_{n+\ell}(b, c_n)$ tends to infinity); $\Gamma^n(x)$ for
the printed $\Gamma^n(k)$ ($k$ is unbound); and $c_n \le b$, the bound of the proof and of its
restatement in the proof of Theorem 12, for the printed $c_n \le 10$ (copied from Theorem 5).

## Sources

- Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer Sequences 28 (2025), Article 25.2.8, Theorem 10 (`jis-2025-25.2.8-thm-10`).
