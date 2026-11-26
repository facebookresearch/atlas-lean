# Bridge and torch on star graphs

Consider the star model with $n \ge 2$ persons of crossing
times $1, \dots, n$, $k \ge 1$ edges and $t \ge 1$ torches, let $T(n, k, t)$ be its optimal time,
and let $m = \min(k, t)$ and $s = \lceil n/(2m) \rceil$. Let $T(n)$ be the optimal crossing time
of $n$ persons with crossing times $1, \dots, n$ on a bridge of capacity $2$ with one torch. Then

$$sn - ms(s-1) \le T(n, k, t) \le T(n),$$

and the left inequality is an equality whenever $t \ge \lceil n/2 \rceil$. Moreover, for all
natural numbers $q$ and $r$ with $n = 2mq + r$ and $r < 2m$,

$$sn - ms(s-1) = \frac{n^2}{4m} + \frac{n}{2} + \frac{r(2m-r)}{4m},$$

and this is at least $n^2/(4m) + n/2$.

For $n \ge 2$ the closed form $T(n) = n^2/4 + 3n - 5 + ((-1)^n - 1)/8$ is Theorem 1 of the same
paper.

## Sources

- Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6, Theorem 26 (`jis-2026-26.5.6-thm-26`).
