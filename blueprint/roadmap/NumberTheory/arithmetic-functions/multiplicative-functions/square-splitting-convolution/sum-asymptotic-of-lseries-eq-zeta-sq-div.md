# Partial-sum asymptotics for a Riemann zeta quotient times a Dirichlet series

Let
$f, g : \mathbb{N} \to \mathbb{C}$ and let $\sigma_0 < 1/2$ be a real number. Suppose that the
Dirichlet series $G(s) = \sum_{n \ge 1} g(n) n^{-s}$ converges absolutely for
$\operatorname{Re} s > \sigma_0$, that $G(1) \ne 0$, and that for every complex $s$ with
$\operatorname{Re} s > 1$ the Dirichlet series $F(s) = \sum_{n \ge 1} f(n) n^{-s}$ converges
absolutely and $F(s) = \zeta(s)^2 G(s) / \zeta(2s)$, where $\zeta$ is the Riemann zeta
function. Then, as the real number $x$ tends to infinity,

$$
\sum_{1 \le n \le x} f(n) = \frac{G(1)}{\zeta(2)}\, x \log x +
\frac{G(1)}{\zeta(2)} \left(2\gamma - 1 + \frac{G'(1)}{G(1)} -
\frac{2\zeta'(2)}{\zeta(2)}\right) x + O\big(x^{1/2} (\log x)^3\big),
$$

where $\gamma$ is the Euler–Mascheroni constant and $G'$, $\zeta'$ are complex derivatives.

The hypothesis $G(1) \ne 0$ is added so that the quotient $G'(1)/G(1)$ is meaningful.

## Sources

- Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Lemma 1.
