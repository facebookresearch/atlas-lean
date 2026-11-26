# High-rate line-parity codes in characteristic two

Let $K$ be a field of characteristic two with $2^{hm}$ elements and $\ell \le 2^h$. Write each exponent below $|K|$ with $m$ digits in base $2^h$; the code spanned by the monomials $\prod_i X_i^{e_i}$ on $K^\ell$ whose digit matrix (digits of $e_1, \dots, e_\ell$) has an all-zero digit position is a line-parity code with exactly

$$A^m - (A - 1)^m, \qquad A = 2^{h\ell},$$

information symbols out of $|K|^\ell = A^m$ points. Its rate $1 - (1 - 1/A)^m$ tends to $1$ as $m$ grows; it is at least $P/(P+1)$ once $m \ge P(A - 1)$.

## Proof sketch

On an affine line a monomial restricts to a univariate polynomial; in characteristic two a Frobenius substitution rotates the binary digits of the exponents, and rotating the zero digit to the top makes the total degree less than $|K| - 1$. The values of such a polynomial sum to zero over $K$, which is exactly line parity. Linearly independent line-parity functions span a systematic code (choose points whose evaluation rows form a basis), and counting digit matrices with a zero column gives the dimension.

## Depends on

- [Line-parity codes and universal recovery menus](line-parity-code.md)

## Sources

- S. Schlesinger, "Boolean circuit mass production", 2026.
