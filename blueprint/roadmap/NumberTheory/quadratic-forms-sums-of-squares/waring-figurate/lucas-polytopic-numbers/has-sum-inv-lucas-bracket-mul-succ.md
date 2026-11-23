# Sum of reciprocals of products of consecutive Lucas brackets

Let $(s, t)$ be
nondegenerate Lucas parameters with $s > 0$, $s^2 + 4t > 0$ and $|t| > 1$, write $\{n\}_{s,t}$
for the Lucas brackets and let $\varphi = (s + \sqrt{s^2 + 4t})/2$. Then the series
$\sum_{n \ge 1} 1/(\{n\}_{s,t}\{n+1\}_{s,t})$ converges absolutely, and its sum is
$\varphi - (1 + t)\ln_{s,t}(1 + \varphi/t)$, where
$\ln_{s,t}(1 + \varphi/t) = -\sum_{n \ge 1} (-\varphi/t)^n/\{n\}_{s,t}$ is the Lucas logarithm.

The hypotheses $s > 0$ and $s^2 + 4t > 0$ make $\varphi$ real with $0 < |q| < 1$, where
$q = \varphi'/\varphi$ and $\varphi' = (s - \sqrt{s^2 + 4t})/2$; and $|t| > 1$ puts $-\varphi/t$ in
the paper's convergence range $(-|\varphi|, |\varphi|)$ of the Lucas logarithm. Without
$|t| > 1$ the logarithm series diverges: for $s = t = 1$ its terms $(-\varphi)^n/F_n$, with $F_n$
the Fibonacci numbers, do not tend to $0$.

## Sources

- Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 13 (`jis-2025-25.5.6-thm-13`).
