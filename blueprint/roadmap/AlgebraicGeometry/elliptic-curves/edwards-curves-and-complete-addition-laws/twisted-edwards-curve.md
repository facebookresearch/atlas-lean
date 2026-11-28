# Twisted Edwards curve

For distinct nonzero $a,d$ in a field of characteristic not $2$, the twisted Edwards curve is $ax^2+y^2=1+dx^2y^2$; its addition law, defined when $1\pm dx_1x_2y_1y_2\ne0$, is $(x_1,y_1)+(x_2,y_2)=\bigl((x_1y_2+y_1x_2)/(1+dx_1x_2y_1y_2),\,(y_1y_2-ax_1x_2)/(1-dx_1x_2y_1y_2)\bigr)$, with neutral element $(0,1)$.

Let $k$ be a field with $\operatorname{char}k\ne2$ and let $a,d\in k$ with $a\ne0$, $d\ne0$, $a\ne d$. The *twisted Edwards curve* with coefficients $a,d$ is the affine curve

$$
E_{a,d}:\ ax^2+y^2=1+dx^2y^2 .
$$

Under these conditions the affine curve is nonsingular. An *Edwards curve* is a twisted Edwards curve with $a=1$. The *twisted Edwards addition law* sends points $(x_1,y_1),(x_2,y_2)$ of $E_{a,d}$ with $dx_1x_2y_1y_2\ne\pm1$ to

$$
\left(\frac{x_1y_2+y_1x_2}{1+dx_1x_2y_1y_2},\ \frac{y_1y_2-ax_1x_2}{1-dx_1x_2y_1y_2}\right).
$$

The point $(0,1)$ is neutral, the negative of $(x,y)$ is $(-x,y)$, $(0,-1)$ has order $2$, and when $a$ is a square, $(\pm1/\sqrt a,0)$ have order $4$. The same formula serves for doubling. $E_{a,d}$ is a quadratic twist of the Edwards curve $\bar x^2+y^2=1+(d/a)\bar x^2y^2$ via $\bar x=\sqrt a\,x$, an isomorphism over $k(\sqrt a)$, and over $k$ when $a$ is a square. Bernstein and Lange use the Edwards curves $x^2+y^2=c^2(1+dx^2y^2)$ with $c,d\ne0$, $dc^4\ne1$, whose addition law has denominators $c(1\pm dx_1x_2y_1y_2)$; the case $c=1$ is $E_{1,d}$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Non-singularity of the affine curve is Galbraith's Exercise 9.12.15. The excluded values are those for which the equation is not a model of an elliptic curve; for instance $a=d\ne0$ gives $(1-y^2)(1-ax^2)=0$, a union of four lines over $k(\sqrt a)$, and $a=d=0$ gives the two lines $y=\pm1$, while $a\ne0$ and $d=0$ give the smooth conic $ax^2+y^2=1$. The closure in the projective plane has two singular points at infinity; a smooth projective model in $\mathbb{P}^3$ has four points at infinity, defined over $k(\sqrt{d/a},\sqrt d)$ and of order dividing $4$ (Galbraith, Lemma 9.12.18). That the addition law corresponds to the group law of an elliptic curve is a separate theorem.

## Sources

- D. J. Bernstein, P. Birkner, M. Joye, T. Lange and C. Peters, "Twisted Edwards curves", *Progress in Cryptology (AFRICACRYPT 2008)*, LNCS 5023, Springer, 2008, pp. 389–405, doi:10.1007/978-3-540-68164-9_26; numbering from the authors' version of 2008-03-13, <https://cr.yp.to/newelliptic/twisted-20080313.pdf>, Definition 2.1, Section 2 (twists) and Section 6 (addition law).
- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 9.12.14, equation (9.14), Exercises 9.12.15–9.12.17 and Lemma 9.12.18.
- L. Chen, D. Moody, K. Randall, A. Regenscheid and A. Robinson, *Recommendations for Discrete Logarithm-based Cryptography: Elliptic Curve Domain Parameters*, NIST SP 800-186, 2023, doi:10.6028/NIST.SP.800-186, Section 2.1.3.
- D. J. Bernstein and T. Lange, "Faster addition and doubling on elliptic curves", *Advances in Cryptology (ASIACRYPT 2007)*, LNCS 4833, Springer, 2007, pp. 29–50, doi:10.1007/978-3-540-76900-2_3; numbering from the authors' version of 2007-09-06, <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>, Section 3, opening (the curves $x^2+y^2=c^2(1+dx^2y^2)$ with $c,d\ne0$, $dc^4\ne1$, and the addition law with denominators $c(1\pm dx_1x_2y_1y_2)$).
