# Powers of strictly primitive solutions

Let $d > 1$ be a square-free integer, $p$ an odd
prime, and $m, n > 0$ natural numbers. Write elements of $\mathbb{Z}[\sqrt{d}]$ as $u + v\sqrt{d}$
with integers $u, v$, and let $N(u + v\sqrt{d}) = u^2 - d v^2$ be the norm. If
$a = u + v\sqrt{d}$ satisfies $|N(a)| = p^m$ with $u$ and $d v$ coprime, then
$a^n = u' + v'\sqrt{d}$ satisfies $|N(a^n)| = p^{mn}$ with $u'$ and $d v'$ coprime; that is, $a^n$
gives a strictly primitive solution of $|x^2 - d y^2| = p^{mn}$.

The source states this without $p \ne 2$, and it fails for $p = 2$: for $d = 3$ and
$a = 1 + \sqrt{3}$ we have $N(a) = -2$, but $a^2 = 4 + 2\sqrt{3}$ and $\gcd(4, 6) = 2$. The sign
$\pm$ in the source's equation (14) is dropped.

## Sources

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 3(b) (`integers-2024-A111-prop-3`).
