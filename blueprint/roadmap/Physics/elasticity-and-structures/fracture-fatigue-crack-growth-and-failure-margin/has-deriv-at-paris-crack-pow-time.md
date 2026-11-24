# Up to failure the event path $a(f t)$ solves $da/dt = f K a^{1-r}$

Let $K > 0$, $r \ne 0$, $f > 0$ and $0 < a_0 < a_c$, with $a_c$ the [critical crack
length](critical-crack-length.md), and let $a(N) = (a_0^r + r K N)^{1/r}$ be the [power-branch
solution](paris-crack-pow.md) and $N_f = (a_c^r - a_0^r)/(r K)$ its [Paris life](paris-life-pow.md).
For every time $t$ with $0 \le t \le N_f / f$, the [event path](saturated-crack-path.md) at $t$ is
the crack after $f t$ cycles, $a(\min(f t, N_f)) = a(f t)$, and the crack in time $s \mapsto a(f s)$
(for real $s$) has at $t$ the derivative

$$\frac{d}{ds}\, a(f s) \Big|_{s = t} = f K\, a(f t)^{1 - r} ,$$

the Paris law $da/dN = K a^{m/2}$, with $1 - r = m/2$, at $f$ cycles per unit time. The derivative
is that of $s \mapsto a(f s)$; the event path equals it up to the failure time $N_f / f$ and is
constant afterwards.
