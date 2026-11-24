# Addition and doubling formulas for the negative Pell sequences

Let $d$ be a natural
number such that $x^2 - dy^2 = -1$ has an integral solution, let $(X, Y)$ be the solution of
$x^2 - dy^2 = -1$ in natural numbers with the least positive $Y$, and let $f_n$ and $g_n$ be the
integers defined by $f_0 = 1$, $g_0 = 0$, $f_{n+1} = X f_n + dY g_n$ and
$g_{n+1} = Y f_n + X g_n$, so that $(X + Y\sqrt d)^n = f_n + g_n \sqrt d$. Then for all natural
numbers $n \le m$,

$$
\begin{aligned}
f_{m+n} &= f_m f_n + d g_m g_n, & g_{m+n} &= f_m g_n + g_m f_n, \\
f_{m-n} &= (-1)^n (f_m f_n - d g_m g_n), & g_{m-n} &= (-1)^{n+1} (f_m g_n - g_m f_n), \\
f_{2n} &= f_n^2 + d g_n^2, & g_{2n} &= 2 f_n g_n.
\end{aligned}
$$

The paper also assumes $d > 1$; this is not needed.

## Sources

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24 (2024), Article A111, Proposition 6.
