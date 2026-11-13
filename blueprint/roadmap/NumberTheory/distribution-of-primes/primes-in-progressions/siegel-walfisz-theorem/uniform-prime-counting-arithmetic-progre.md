# Siegel–Walfisz theorem for primes in arithmetic progressions

Let $\varphi$ be Euler's
totient function and let $\mathrm{Li}(x) = \int_2^x du / \log u$. For every real $B > 0$ there are
real constants $c > 0$, $C > 0$ and $X_0 \ge 2$ such that for every real $x \ge X_0$ and all
natural numbers $q > 0$ and $b$ with $\gcd(b, q) = 1$ and $q \le (\log x)^B$, the number
$\pi(x; q, b)$ of primes $p \le x$ with $p \equiv b \pmod q$ satisfies

$$\left|\pi(x; q, b) - \frac{\mathrm{Li}(x)}{\varphi(q)}\right| \le C x e^{-c \sqrt{\log x}}.$$

The constants may depend on $B$, but not on $x$, $q$, or $b$. The logarithmic integral is taken
from $2$, as in the source, rather than as the principal value from $0$.

## Sources

- A. Guo, *Exceptional sets for compositions involving Euler's function, the divisor-sum function and Dedekind's function*, arXiv:2608.19972v1, Lemma `siegel`, `main.tex` lines 289–295.
