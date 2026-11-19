# Mean square of the error term for gcd-sum moments under RH

Let
$A(n) = \frac{1}{n} \sum_{m=1}^{n} \gcd(m, n)$ be the mean gcd-sum function. Assume the Riemann
Hypothesis and let $k \ge 2$ be an integer. Then there is a real polynomial $P$ with the following
property. Write $E(u) = \sum_{1 \le n \le u} A(n)^k - u P(\log u)$ for real $u$. For every real
$\eta$ with $\frac{1}{2^k}\left(4^k - 3^k - \binom{2^k}{2}\right) + \frac{1}{2^{k+1}} + 1 \le \eta$
there are real constants $C$ and $T_0$ such that for all real $T \ge T_0$,

$$\int_1^T E(u)^2 \, du \le C \, T^{2 - 1/2^k} \exp\left(\frac{2 \eta \log T}{\log \log T}\right).$$

## Sources

- Isao Kiuchi and Yuki Tsuruta, *Mean Square Estimates for GCD-Sum Functions*, INTEGERS 25 (2025), Article A53, Theorem 1.
