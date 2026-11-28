# The Edwards addition law is the group law of an elliptic curve

The explicit map $(x,y)\mapsto\bigl((c+y)/(c-y),\,2c(c+y)/((c-y)x)\bigr)$ carries the Edwards addition law on $x^2+y^2=c^2(1+dx^2y^2)$ to the chord-and-tangent law on the elliptic curve $(1/e)v^2=u^3+(4/e-2)u^2+u$, $e=1-dc^4$.

**Theorem.** Let $k$ be a field with $\operatorname{char}k\ne2$ and $c,d\in k$ nonzero with $dc^4\ne1$; put $e=1-dc^4$ and let $E$ be the elliptic curve $(1/e)v^2=u^3+(4/e-2)u^2+u$. Let $(x_1,y_1),(x_2,y_2)$ be points of $x^2+y^2=c^2(1+dx^2y^2)$ over $k$ with $dx_1x_2y_1y_2\ne\pm1$, and let $(x_3,y_3)$ be their Edwards sum

$$
x_3=\frac{x_1y_2+y_1x_2}{c(1+dx_1x_2y_1y_2)},\qquad y_3=\frac{y_1y_2-x_1x_2}{c(1-dx_1x_2y_1y_2)} .
$$

For $i\in\{1,2,3\}$ let $P_i=\infty$ if $(x_i,y_i)=(0,c)$, $P_i=(0,0)$ if $(x_i,y_i)=(0,-c)$, and $P_i=(u_i,v_i)$ with $u_i=(c+y_i)/(c-y_i)$, $v_i=2c(c+y_i)/((c-y_i)x_i)$ if $x_i\ne0$. Then $P_i\in E(k)$ and $P_1+P_2=P_3$ in the group $E(k)$.

When $d$ is not a square the Edwards law is complete, and the set of $k$-points of the Edwards curve with this law is a group isomorphic to $E(k)$.

## Depends on

- [Twisted Edwards curve](twisted-edwards-curve.md)

## Proof depends on

- [The twisted Edwards addition law preserves the curve](edwards-addition-law-preserves-the-curve.md)
- [The twisted Edwards addition law is complete when $a$ is a square and $d$ is not](twisted-edwards-addition-law-is-complete.md)

## Expansion

$x_i\ne0$ implies $y_i\ne c$, so $u_i,v_i$ are defined. Bernstein and Lange verify the correspondence by case analysis on whether the inputs are $(0,\pm c)$ and by comparing with the chord-and-tangent formulas on $E$, using the closure theorem for the output. The elliptic curve $E$ is in Montgomery form; the linear substitution $(u,v)\mapsto(eu,ev)$ takes it to the Weierstrass equation $V^2=U^3+(4-2e)U^2+e^2U$ and preserves lines and the point at infinity, hence the chord-and-tangent law. The step still to supply is the verification that the explicit map carries the Edwards law to the chord-and-tangent law, case by case as in Bernstein and Lange's proof.

## Sources

- D. J. Bernstein and T. Lange, "Faster addition and doubling on elliptic curves", *Advances in Cryptology (ASIACRYPT 2007)*, LNCS 4833, Springer, 2007, pp. 29–50, doi:10.1007/978-3-540-76900-2_3; numbering from the authors' version of 2007-09-06, <https://cr.yp.to/newelliptic/newelliptic-20070906.pdf>, Theorem 3.2 and the discussion after Theorem 3.3.
