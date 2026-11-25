# Closed form of the shifted Alzer–Richards binomial sum

Let $m \ge 1$ be an integer and
$x$ a complex number, write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex $z$, and assume
$\binom{k-m+1/2-x}{k} \ne 0$ for $0 \le k \le \lfloor m/2 \rfloor$. Put

$$
S(x) = \sum_{k=0}^{\lfloor m/2 \rfloor}
\frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k-m+1/2-x}{k}}.
$$

If $x \ne -m/2$ and $x \ne (1-m)/2$, then
$S(x) = \frac{x (x+m-1/2)}{(x+m/2)(x+(m-1)/2)} \binom{x+m}{m}$. If $m$ is even and
$x = -m/2$, then $S(x) = \frac{(-1)^{m/2}}{2^m \binom{(m-3)/2}{m/2}}$. If $m$ is odd and
$x = (1-m)/2$, then $S(x) = \frac{(-1)^{(m-1)/2} (m+1)}{2^m \binom{m/2-1}{(m-1)/2}}$.

## Sources

- Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 2 (iii), Equation (21).
