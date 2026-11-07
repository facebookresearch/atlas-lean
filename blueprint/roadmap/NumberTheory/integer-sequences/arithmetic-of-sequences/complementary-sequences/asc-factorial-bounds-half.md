# Rising factorial between consecutive $k$-th powers

Let $k$ and $n$ be natural numbers,
write $n^{\overline{k}} = n (n + 1) \cdots (n + k - 1)$ for the rising factorial, and let
$r = \lfloor (k^2 - 4k + 6)/4 \rfloor$ if $k$ is even and $r = \lfloor (k^2 - 6k + 11)/4 \rfloor$
if $k$ is odd. If $n \ge r$, then
$(n + \lfloor k/2 \rfloor - 1)^k \le n^{\overline{k}} \le (n + \lfloor k/2 \rfloor)^k$.

Both numerators are positive: $k^2 - 4k + 6 = (k - 2)^2 + 2$ and $k^2 - 6k + 11 = (k - 3)^2 + 2$.

## Sources

- Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95, Lemma 1, Equation (8).
