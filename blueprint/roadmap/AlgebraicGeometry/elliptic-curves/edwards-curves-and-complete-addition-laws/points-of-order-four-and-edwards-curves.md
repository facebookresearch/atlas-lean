# An elliptic curve is birational to an Edwards curve iff it has a point of order 4

An elliptic curve $E$ over a field $k$ of characteristic not $2$ is birationally equivalent over $k$ to an Edwards curve $x^2+y^2=1+dx^2y^2$ if and only if $E(k)$ has an element of order $4$.

**Theorem.** Let $k$ be a field with $\operatorname{char}k\ne2$ and $E$ an elliptic curve over $k$. Then $E(k)$ has an element of order $4$ if and only if $E$ is birationally equivalent over $k$ to an Edwards curve $E_{1,d}:x^2+y^2=1+dx^2y^2$ for some $d\in k\setminus\{0,1\}$. Explicitly, if $(u_4,v_4)$ has order $4$ and $E$ is written as $v^2=u^3+(v_4^2/u_4^2-2u_4)u^2+u_4^2u$ (so that $[2]\,(u_4,v_4)=(0,0)$), then with $d=1-4u_4^3/v_4^2$ the maps

$$
(u,v)\mapsto\left(\frac{v_4u}{u_4v},\ \frac{u-u_4}{u+u_4}\right),\qquad (x,y)\mapsto\left(\frac{u_4(1+y)}{1-y},\ \frac{v_4(1+y)}{(1-y)x}\right)
$$

are inverse birational equivalences between $E$ and $E_{1,d}$.

## Depends on

- [Twisted Edwards curve](twisted-edwards-curve.md)

## Proof depends on

- [The Edwards addition law is the group law of an elliptic curve](edwards-addition-agrees-with-the-weierstrass-group-law.md)
- [Variable changes give additive equivalences of points](../weierstrass-curves/variable-change-add-equiv.md)

## Expansion

If $E$ is birational to $E_{1,d}$, the group laws correspond, and $(1,0)$ has order $4$ on $E_{1,d}$. Conversely $u_4\ne0$ and $v_4\ne0$ for a point of order $4$; after completing the square and translating $[2]\,(u_4,v_4)$ to $(0,0)$, both origin-preserving variable changes, the curve takes the stated form, $d\notin\{0,1\}$, and the identity $x^2+y^2=1+dx^2y^2$ for the image is checked in the function field of $E$ (the source gives a computer-algebra verification). The exceptional sets $u_4v=0$, $u=-u_4$ and $y=1$, $x=0$ are finite; for the converse the birational map is read on the smooth projective models, composed with a translation if it does not send origin to origin. Twisted Edwards curves cover more: every elliptic curve with three rational points of order $2$ is $2$-isogenous to a twisted Edwards curve (Bernstein et al., Theorem 5.1).

## Sources

- D. J. Bernstein, P. Birkner, M. Joye, T. Lange and C. Peters, "Twisted Edwards curves", *Progress in Cryptology (AFRICACRYPT 2008)*, LNCS 5023, Springer, 2008, pp. 389–405, doi:10.1007/978-3-540-68164-9_26; numbering from the authors' version of 2008-03-13, <https://cr.yp.to/newelliptic/twisted-20080313.pdf>, Theorem 3.3 with proof, and Theorem 5.1.
- D. J. Bernstein and T. Lange, "Faster addition and doubling on elliptic curves", *Advances in Cryptology (ASIACRYPT 2007)*, LNCS 4833, Springer, 2007, pp. 29–50, doi:10.1007/978-3-540-76900-2_3; numbering from the authors' version of 2007-09-06, <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>, Theorem 2.1.
