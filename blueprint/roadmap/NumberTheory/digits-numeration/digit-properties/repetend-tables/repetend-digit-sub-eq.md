# Differences of repetend digits

Let $n \ge 1$ and $b$ be natural numbers with
$\gcd(b, n) = 1$. For $x, j \ge 0$ put $b_x = b^x \bmod n$ and
$r_{x,j} = \lfloor b_x^{j+1}/n \rfloor \bmod b_x$. Then for all natural numbers $y, m, d, e$,

$$n (r_{ym,e} - r_{y,d}) = b_{ym} b_{yme} - b_{ym(e+1)} - b_y b_{yd} + b_{y(d+1)}.$$

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Lemma 7.
