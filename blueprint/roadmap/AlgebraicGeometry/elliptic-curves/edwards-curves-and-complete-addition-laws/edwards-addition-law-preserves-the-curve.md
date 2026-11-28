# The twisted Edwards addition law preserves the curve

Whenever its denominators are nonzero, the twisted Edwards addition law sends two points of $ax^2+y^2=1+dx^2y^2$ to a point of the same curve.

**Theorem.** Let $k$ be a field with $\operatorname{char}k\ne2$, $a,d\in k$ distinct and nonzero, and $(x_1,y_1),(x_2,y_2)\in k^2$ points of $E_{a,d}:ax^2+y^2=1+dx^2y^2$ with $dx_1x_2y_1y_2\notin\{1,-1\}$. Then

$$
x_3=\frac{x_1y_2+y_1x_2}{1+dx_1x_2y_1y_2},\qquad y_3=\frac{y_1y_2-ax_1x_2}{1-dx_1x_2y_1y_2}
$$

satisfy $ax_3^2+y_3^2=1+dx_3^2y_3^2$.

## Depends on

- [Twisted Edwards curve](twisted-edwards-curve.md)

## Proof depends on

None.

## Expansion

For $a=1$ and Bernstein–Lange's parameter $c$ this is their Theorem 3.1, proved from the polynomial identity $T=(x_1^2+y_1^2-(x_2^2+y_2^2)dx_1^2y_1^2)(x_2^2+y_2^2-(x_1^2+y_1^2)dx_2^2y_2^2)$ for $T=(x_1y_2+y_1x_2)^2(1-\epsilon)^2+(y_1y_2-x_1x_2)^2(1+\epsilon)^2-d(x_1y_2+y_1x_2)^2(y_1y_2-x_1x_2)^2$, $\epsilon=dx_1x_2y_1y_2$, together with the curve equations. The twisted case reduces to $a=1$ over $k(\sqrt a)$: with $\bar x_i=\sqrt a\,x_i$ the points lie on $\bar x^2+y^2=1+(d/a)\bar x^2y^2$, the quantity $(d/a)\bar x_1\bar x_2y_1y_2$ equals $\epsilon$, and the Edwards law there returns $(\sqrt a\,x_3,y_3)$; the identity for $(x_3,y_3)$ then holds in $k(\sqrt a)$ and hence in $k$ (Bernstein et al., Section 6).

## Sources

- D. J. Bernstein and T. Lange, "Faster addition and doubling on elliptic curves", *Advances in Cryptology (ASIACRYPT 2007)*, LNCS 4833, Springer, 2007, pp. 29–50, doi:10.1007/978-3-540-76900-2_3; numbering from the authors' version of 2007-09-06, <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>, Theorem 3.1 and its proof.
- D. J. Bernstein, P. Birkner, M. Joye, T. Lange and C. Peters, "Twisted Edwards curves", *Progress in Cryptology (AFRICACRYPT 2008)*, LNCS 5023, Springer, 2008, pp. 389–405, doi:10.1007/978-3-540-68164-9_26; numbering from the authors' version of 2008-03-13, <https://cr.yp.to/newelliptic/twisted-20080313.pdf>, Section 6 ("The twisted Edwards addition law").
