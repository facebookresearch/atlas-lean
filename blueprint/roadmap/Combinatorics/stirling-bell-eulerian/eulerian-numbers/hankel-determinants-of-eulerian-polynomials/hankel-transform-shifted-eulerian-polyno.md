# Hankel determinants of the shifted Eulerian polynomials

Let $n \in \mathbb{N}$ and
$x \in \mathbb{R}$. For natural numbers $k \le m$ let
$W_{m,k} = \sum_{i=0}^{m-k} (-1)^i \binom{m+1}{i} (m-k-i)^m$, with $0^0 = 1$, and let
$P_m(X) = \sum_{k=0}^{m} W_{m,k} X^k$ be the corresponding Eulerian polynomial. Then the
$(n+1) \times (n+1)$ Hankel determinant of the shifted sequence $P_1(x), P_2(x), \dots$ is

$$\det\bigl(P_{i+j+1}(x)\bigr)_{0 \le i, j \le n} =
(2x)^{\binom{n+1}{2}} \prod_{k=0}^{n-1} \binom{k+3}{2}^{n-k-1}.$$

## Sources

- Paul Barry, "Eulerian Polynomials as Moments, via Exponential Riordan Arrays," Journal of Integer Sequences 14 (2011), Article 11.9.5, corollary lines 312–315, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry7/barry172.tex>. Eulerian closed form `W_{n,k}` at lines 93–94.
