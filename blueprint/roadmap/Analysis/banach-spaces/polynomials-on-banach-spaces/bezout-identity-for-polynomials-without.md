# Bezout identity for polynomials without a common zero

Let $E$ be a complex Banach space
and let $F, G : E \to \mathbb{C}$ be continuous polynomial functions with no common zero, that
is, $G(x) \neq 0$ whenever $F(x) = 0$. Then there are continuous polynomial functions
$\varphi, \psi : E \to \mathbb{C}$ such that $F(x) \varphi(x) + G(x) \psi(x) = 1$ for every
$x \in E$.

This is the identity recorded in the addendum to Problem 27 of the Scottish Book (Mazur-Orlicz,
4 April 1939). The problem asks whether two complex polynomials on a complex Banach space that
both tend to $0$ along a sequence $(x_n)$ in the unit ball must have a common zero. The answer
is positive and follows from the identity by contradiction: continuous polynomials are bounded
on the unit ball, so $F(x_n) \varphi(x_n) + G(x_n) \psi(x_n)$ would tend to $0$, yet it equals
$1$.

## Sources

- S. Mazur and W. Orlicz, Problem 27 of the Scottish Book, with the positive answer via the Bezout identity in the addendum; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
