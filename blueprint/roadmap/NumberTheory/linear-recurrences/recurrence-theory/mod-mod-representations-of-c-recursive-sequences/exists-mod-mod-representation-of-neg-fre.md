# Mod-mod representation of C-recursive sequences, negative free term

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

where the quotient is taken in $\mathbb{Q}$ and is $0$ when $\tilde B(c^n) = 0$. If $\alpha < 0$,
then there is a natural number $r$ such that for every $n \ge 1$,

$$|\alpha| \, t_n = \bigl( P_r(n) \bmod \tilde B(r^n) \bigr) \bmod r^n.$$

## Sources

- M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*, Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 8, negative free term.
