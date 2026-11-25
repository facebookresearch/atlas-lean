# Completing an incomplete exponential sum

Let $p$ be a prime, write
$e_p(t) = e^{2\pi i t/p}$, let $f$ be a polynomial with integer coefficients, and let $B$ be an
integer with $1 \le B \le p$. Put
$T_p(B) = \frac{1}{p} \sum_{y=1}^{p-1} \left|\frac{\sin(\pi B y/p)}{\sin(\pi y/p)}\right|$ and
$M = \max_{1 \le y \le p-1} \left|\sum_{x=1}^{p} e_p(f(x) + yx)\right|$. Then there is a complex
number $\theta$ with $|\theta| \le 1$ such that
$\sum_{x=1}^{B} e_p(f(x)) = \frac{B}{p} \sum_{x=1}^{p} e_p(f(x)) + \theta \, T_p(B) \, M$.

## Sources

- Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25 (2025), Article A48, Lemma 2.1.
