# Factorial moments of the number of lucky cars

Let $n \ge 1$ and $\ell \in \mathbb{N}$, let
$X(f)$ be the number of lucky cars of a parking function $f$ of length $n$, and let
$P_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)x + i\bigr) \in \mathbb{Q}[x]$. Then

$$\frac{1}{(n+1)^{n-1}} \sum_f X(f)\bigl(X(f)-1\bigr)\cdots\bigl(X(f)-\ell+1\bigr) =
\frac{P_n^{(\ell)}(1)}{(n+1)^{n-1}},$$

where $f$ runs over the parking functions of length $n$ and $P_n^{(\ell)}$ is the $\ell$-th
derivative of $P_n$. Since there are $(n+1)^{n-1}$ parking functions of length $n$, the left side
is the $\ell$-th falling-factorial moment of $X$ for a uniformly random parking function.

## Sources

- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Proposition 6.
