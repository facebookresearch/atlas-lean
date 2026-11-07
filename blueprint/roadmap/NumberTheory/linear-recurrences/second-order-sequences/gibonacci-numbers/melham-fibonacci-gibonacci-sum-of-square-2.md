# Melham's gibonacci sum-of-squares identity

Let $G : \mathbb{Z} \to \mathbb{Z}$ satisfy
$G(j+2) = G(j+1) + G(j)$ for every integer $j$, with $G(0) \ne 0$ or $G(1) \ne 0$, and let $F_m$
denote the $m$-th Fibonacci number. Then for every integer $k$ and every natural number $n \ge 1$,

$$6\Bigl(\sum_{j=0}^{2n-1} G(k+j)^2\Bigr)^2 =
F_{2n}^2\bigl(G(k+n-2)^4 + 4G(k+n-1)^4 + 4G(k+n)^4 + G(k+n+1)^4\bigr).$$

The hypotheses $G(0) \ne 0$ or $G(1) \ne 0$ and $n \ge 1$ are not needed; they keep the shape of
the source.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL27/Adegoke/adegoke12.tex>, lines 92–103, 877–880, and 1824–1828. Source hash `ebe2bfa5fe4599897b5f3944fbec475e37d8ef74af7d901116b07e8b81ba229b`.
