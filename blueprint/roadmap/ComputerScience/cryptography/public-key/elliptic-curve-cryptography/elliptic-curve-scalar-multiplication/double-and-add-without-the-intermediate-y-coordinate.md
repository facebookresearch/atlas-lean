# Computing $2P+Q$ without the $y$-coordinate of $P+Q$

On $y^2=x^3+ax+b$, for $P=(x_1,y_1)$ and $Q=(x_2,y_2)$ with $x_1\ne x_2$ and $x(P+Q)\ne x_1$, the slope of the line through $P$ and $P+Q$ is $-\lambda_1-2y_1/(x(P+Q)-x_1)$, so $2P+Q=(P+Q)+P$ can be computed without $y(P+Q)$ (Eisenträger–Lauter–Montgomery).

**Lemma.** Let $F$ be a field of characteristic different from $2$ and $3$, let $E:y^2=x^3+ax+b$ be an elliptic curve over $F$, and let $P=(x_1,y_1)$, $Q=(x_2,y_2)\in E(F)$ with $x_1\ne x_2$. Put

$$
\lambda_1=\frac{y_2-y_1}{x_2-x_1},\qquad x_3=\lambda_1^2-x_1-x_2,\qquad y_3=(x_1-x_3)\lambda_1-y_1,
$$

so that $P+Q=(x_3,y_3)$. If $x_3\ne x_1$, then $(P+Q)+P=2P+Q=(x_4,y_4)$ with

$$
\lambda_2=\frac{y_3-y_1}{x_3-x_1}=-\lambda_1-\frac{2y_1}{x_3-x_1},\qquad x_4=\lambda_2^2-x_1-x_3,\qquad y_4=(x_1-x_4)\lambda_2-y_1 .
$$

Under these two inequalities, $2P+Q$ is computed from $P,Q$ with one multiplication, two squarings and two divisions in $F$, whereas a doubling followed by an addition, when both take their generic branch, uses two multiplications, three squarings and two divisions.

## Depends on

None.

## Proof depends on

None.

## Expansion

Substituting $y_3=(x_1-x_3)\lambda_1-y_1$ gives $y_3-y_1=-(x_3-x_1)\lambda_1-2y_1$, and dividing by $x_3-x_1$ gives the second expression for $\lambda_2$. The formulas for $x_3,y_3,x_4,y_4$ are the chord addition law, valid because $x_1\ne x_2$ and $x_3\ne x_1$; the operation counts read off the formulas, not counting multiplication by small constants. The cases $x_1=x_2$ or $x_3=x_1$ (that is $P=\pm Q$ or $P+Q=\pm P$), inputs at infinity and characteristic $2$ need separate formulas. Eisenträger, Lauter and Montgomery apply the same substitution to tripling and to $3P+Q$ on the corresponding generic paths, and to Miller's algorithm for pairings.

## Sources

- K. Eisenträger, K. Lauter and P. L. Montgomery, "Fast elliptic curve arithmetic and improved Weil pairing evaluation", *Topics in Cryptology (CT-RSA 2003)*, LNCS 2612, Springer, 2003, doi:10.1007/3-540-36563-X_24; numbering from arXiv:math/0208038v2, Sections 2–3, Section 3.1 and Table 1.
