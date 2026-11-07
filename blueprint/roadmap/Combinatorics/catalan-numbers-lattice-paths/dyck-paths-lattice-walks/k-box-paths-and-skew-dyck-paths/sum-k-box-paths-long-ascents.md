# Long ascents of box paths: sum and sum of squares

Let $k \ge 1$ and $n \ge 1$, let
$B_n^{(k)}$ be the set of $k$-box paths of size $n$, and for a path $w$ let $\mathrm{la}(w)$ be
its number of long ascents. Then

$$\sum_{w \in B_n^{(k)}} \mathrm{la}(w) = \binom{(k+2)n-3}{n-1}$$

and

$$\bigl((k+2)n-3\bigr) \sum_{w \in B_n^{(k)}} \mathrm{la}(w)^2 =
\bigl((k+1)n^2-n-1\bigr) \binom{(k+2)n-3}{n-1}.$$

The source states the second identity divided by $(k+2)n-3$, that is, with the sum of
$\mathrm{la}(w)^2$ equal to $\frac{(k+1)n^2-n-1}{(k+2)n-3}\binom{(k+2)n-3}{n-1}$; at $k = n = 1$
the cleared form reads $0 = 0$.

## Sources

- Zhang and Zhuang, *A Subfamily of Skew Dyck Paths Related to `k`-ary Trees*, Journal of Integer Sequences 27 (2024), Article 24.2.4, Lemma 17 (`jis-2024-24.2.4-lem-17`).
