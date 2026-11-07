# Limiting area between cosine powers via double factorials

For natural numbers $n$ and
$k$, let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. As $k \to \infty$ through the natural
numbers: if $n$ is odd, then

$$A_n(k) \to \frac{8 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-1)/2} \frac{(2j-1)!!}{(2j)!! (2j+1)},$$

and if $n \ge 2$ is even, then

$$A_n(k) \to \frac{16 \, n!}{\pi (n!!)^2} \sum_{j=0}^{(n-2)/2} \frac{(2j)!!}{(2j+1)!! (2j+2)}.$$

Here $(-1)!! = 1$ and $0!! = 1$.

## Sources

- Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4 (`jis-2025-25.2.3-thm-4`).
