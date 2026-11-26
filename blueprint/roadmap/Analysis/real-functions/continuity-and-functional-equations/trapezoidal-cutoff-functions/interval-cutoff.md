# Interval cutoff

For real numbers $a$, $b$ and $\delta$, the interval cutoff is the
function $\chi_{a,b,\delta} \colon \mathbb{R} \to \mathbb{R}$ defined by

$$
\chi_{a,b,\delta}(x) = \max\{0, \min\{1, (x - a)/\delta, (b - x)/\delta\}\},
$$

where division by zero is taken to give $0$.

It vanishes at $a$ and at $b$. For $\delta > 0$ it equals $1$ on $[a + \delta, b - \delta]$, which
is nonempty when $2\delta \le b - a$; for $\delta = 0$ it is identically zero.
