# Entry 14 of Chapter 9: the integral of $u^n / (2 \sin u)$

For an integer $m \ge 2$ write
$\lambda(m) = \sum_{k \ge 0} (2k+1)^{-m}$. For real $x$ let
$C_1(x) = -\tfrac{1}{2} \log|\tan(x/2)|$, and for an integer $m \ge 2$ let $s_m = \sin$ if $m$ is
even and $s_m = \cos$ if $m$ is odd, and let $C_m(x) = \sum_{k \ge 0} s_m((2k+1)x)/(2k+1)^m$. Let
$n \ge 1$ be an integer and $x$ a real number with $x \ne 0$ and $|x| < \pi$. Then
$u \mapsto u^n / (2 \sin u)$ is integrable on the interval between $0$ and $x$; the series
defining $\lambda(n+1)$ is summable; the partial sums $\sum_{k < N} \cos((2k+1)x)/(2k+1)$ tend
to $C_1(x)$ as $N \to \infty$; for every integer $m$ with $2 \le m \le n+1$ the series defining
$C_m(x)$ is summable; and

$$\int_0^x \frac{u^n}{2 \sin u}\,du = \cos\frac{n\pi}{2}\, n!\, \lambda(n+1) -
\sum_{j=0}^{n} (-1)^{j(j+1)/2} \frac{n!}{(n-j)!}\, x^{n-j}\, C_{j+1}(x).$$

The proof subtracts a scaled copy of Entry 13 at $2x$ from Entry 13 at $x$ and splits the zeta and
Clausen series into even and odd frequencies, following Berndt and Lewin, *Polylogarithms and
Associated Functions*, Chapter 4.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
