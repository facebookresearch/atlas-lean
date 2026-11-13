# Arithmetic billiards in a tilted rectangle

Let $p$ be a prime with $p \equiv 1 \pmod 4$
and let $l$ be an even natural number with $l + 3 \le p$. Put $m = l + 1$ if $2l + 5 \le p$ and
$m = p - (l + 1)$ otherwise, and let $R \subseteq \mathbb{R}^2$ be the convex hull of the four
points $(0, m)$, $(m, 0)$, $(p/2, p/2 - m)$ and $(p/2 - m, p/2)$. Let $L$ be the set of integer
points on the boundary of $R$ other than $(0, m)$ and $(m, 0)$. Call a sequence $P_0, P_1, \ldots$
of integer points a billiard path if $P_0 = (0, m)$ and, for every $i < p - 1$, the point
$P_{i+1}$ lies on the boundary of $R$, differs from $P_i$, and has the same second coordinate as
$P_i$ when $i$ is even and the same first coordinate as $P_i$ when $i$ is odd. Then a billiard
path exists, and every billiard path $P$ maps $\{1, \ldots, p - 2\}$ bijectively onto $L$,
satisfies $P_{p-1} = (m, 0)$, and satisfies $P_{p-1-i} = (y_i, x_i)$ for every $i \le p - 1$,
where $P_i = (x_i, y_i)$.

## Sources

- Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Lemma 16 (`lem:billiards`).
