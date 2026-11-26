# Step sums along a Riordan array

Let $K$ be a field, let $g, h \in K[[x]]$ with
$h(0) = 0$, and write $d(n, m) = [x^n]\, g(x) h(x)^m$. Then for all natural numbers $k > 1$,
$p < k$ and $n$,
$\sum_{j=0}^{n} d(n, kj + p) = [x^n]\, g(x) h(x)^p (1 - h(x)^k)^{-1}$.

Since $h(0) = 0$, $d(n, m) = 0$ for $m > n$, so the left side is the full sum over all
$j \ge 0$.

## Sources

- Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and Some Generalizations*, J. Integer Seq. 27 (2024), Article 24.3.4, Proposition 5, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Brietzke/bri3.html>.
