# Single-formula mod-mod representation of C-recursive sequences

Let
$t_0, t_1, t_2, \dots$ be natural numbers, let $c$ be a natural number, and let $A$ and $B$ be
polynomials with integer coefficients such that $A \ne 0$, $B(0) = 1$ and
$k = \deg A < d = \deg B$. Suppose that $\bigl(\sum_{n \ge 0} t_n z^n\bigr) B(z) = A(z)$ as
formal power series. Let $\tilde A(x) = x^k A(1/x)$ and $\tilde B(x) = x^d B(1/x)$ be the
reversed polynomials, let $\alpha$ be the constant term of $\tilde B$, that is, the leading
coefficient of $B$, and for an integer $x$ put $P_x(n) = x^{n^2} x^{n(d-k)} \tilde A(x^n)$. For
integers $X$ and $M \ne 0$, write $X \bmod M$ for the remainder of $X$ modulo $M$ in
$\{0, 1, \dots, |M| - 1\}$, and set $X \bmod 0 = X$. Suppose that for every $n \ge 1$,

$$t_n = \bigl\lfloor P_c(n) / \tilde B(c^n) \bigr\rfloor \bmod c^n,$$

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. Put
$\sigma = \operatorname{sgn} \alpha$; note $\alpha \ne 0$ because $B \ne 0$. Then there is a
natural number $r \ge c$ such that for every $n \ge 1$, writing
$\rho_n = \bigl( (-\sigma P_r(n)) \bmod \tilde B(r^n) \bigr) \bmod r^n$, the rational numbers
satisfy

$$t_n = \frac{-1 - \sigma}{2} + \frac{\rho_n}{|\alpha|}.$$

The hypothesis $A \ne 0$ excludes the zero sequence: for $A = 0$ and $B(z) = 1 + z$ the right
side is $-1$.

## Sources

- M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 9.
