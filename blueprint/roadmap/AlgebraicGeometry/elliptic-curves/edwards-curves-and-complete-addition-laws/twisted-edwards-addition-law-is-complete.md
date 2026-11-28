# The twisted Edwards addition law is complete when $a$ is a square and $d$ is not

If $a$ is a square and $d$ a non-square in $k$, then $1\pm dx_1x_2y_1y_2\ne0$ for all $k$-points of $ax^2+y^2=1+dx^2y^2$, so the twisted Edwards addition law is defined for every pair of $k$-rational affine points, doubling and inverses included.

**Theorem.** Let $k$ be a field with $\operatorname{char}k\ne2$, $a,d\in k$ with $a\ne0$, $d\ne0$, $a\ne d$, $a$ a square in $k^*$ and $d$ not a square in $k$. For all $(x_1,y_1),(x_2,y_2)\in k^2$ on $E_{a,d}$,

$$
dx_1x_2y_1y_2\ne1\qquad\text{and}\qquad dx_1x_2y_1y_2\ne-1 .
$$

For $a=1$ this is Bernstein and Lange's completeness of the Edwards addition law for non-square $d$, stated for $x^2+y^2=c^2(1+dx^2y^2)$; that curve reduces to the case $c=1$ by the scaling $(x,y)\mapsto(x/c,y/c)$, which replaces $d$ by $dc^4$, a non-square exactly when $d$ is.

## Depends on

- [Twisted Edwards curve](twisted-edwards-curve.md)

## Proof depends on

None.

## Expansion

Galbraith's proof: let $\epsilon=dx_1x_2y_1y_2$ and suppose $\epsilon=\pm1$; then $x_1,x_2,y_1,y_2\ne0$. Using $ax_2^2+y_2^2=1+dx_2^2y_2^2$ one obtains $dx_1^2y_1^2(ax_2^2+y_2^2)=ax_1^2+y_1^2$, and adding $\pm2\sqrt a\,\epsilon x_1y_1$ to both sides gives

$$
(\sqrt a\,x_1\pm\epsilon y_1)^2=dx_1^2y_1^2(\sqrt a\,x_2\pm y_2)^2 .
$$

If $\sqrt a\,x_2+y_2\ne0$ or $\sqrt a\,x_2-y_2\ne0$, then $d$ is a square, a contradiction; if both vanish then $x_2=0$, also a contradiction. Completeness here concerns $k$-rational points; over an algebraic closure the denominators do vanish for some pairs, and Bosma and Lenstra show that on a Weierstrass model a complete system for all points over all extensions needs two addition laws.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Lemma 9.12.19.
- D. J. Bernstein and T. Lange, "Faster addition and doubling on elliptic curves", *Advances in Cryptology (ASIACRYPT 2007)*, LNCS 4833, Springer, 2007, pp. 29–50, doi:10.1007/978-3-540-76900-2_3; numbering from the authors' version of 2007-09-06, <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>, Theorem 3.3 and the discussion after it.
- D. J. Bernstein, P. Birkner, M. Joye, T. Lange and C. Peters, "Twisted Edwards curves", *Progress in Cryptology (AFRICACRYPT 2008)*, LNCS 5023, Springer, 2008, pp. 389–405, doi:10.1007/978-3-540-68164-9_26; numbering from the authors' version of 2008-03-13, <https://cr.yp.to/newelliptic/twisted-20080313.pdf>, Section 6.
- L. Chen, D. Moody, K. Randall, A. Regenscheid and A. Robinson, *Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve Domain Parameters*, NIST SP 800-186, 2023, doi:10.6028/NIST.SP.800-186, Section 2.1.3.
