# Exceptional pairs of addition laws of bidegree (2,2)

Nonzero addition laws of bidegree $(2,2)$ on a Weierstrass curve correspond, up to scaling, to points $(a:b:c)$ of the projective plane, and a pair $(P_1,P_2)$ is exceptional for the law of $(a:b:c)$ exactly when $P_1-P_2$ lies on the line $ax+by+cz=0$.

**Theorem.** Let $E$ be an elliptic curve over a field $k$ given by a Weierstrass equation. There is a bijection between $\mathbb{P}^2(k)$ and the set of equivalence classes of nonzero addition laws of bidegree $(2,2)$ on $E$ with the following property: if $(a:b:c)\in\mathbb{P}^2(k)$ and $P_1,P_2\in E(K)$ for an extension field $K$ of $k$, then $(P_1,P_2)$ is exceptional for the law corresponding to $(a:b:c)$ if and only if $P_1-P_2$ lies on the intersection of $E(K)$ with the line $ax+by+cz=0$ in $\mathbb{P}^2(K)$.

Consequently, two laws whose lines are distinct and meet in a point of $\mathbb{P}^2(k)$ not on $E$ form a complete system, for instance the laws of the lines $y=0$ and $z=0$, which meet at $(1:0:0)$, or of $by+cz=0$ and $b'y+c'z=0$ with $bc'-b'c\ne0$.

## Depends on

- [Addition laws and complete systems on a Weierstrass curve](addition-laws-on-a-weierstrass-curve.md)

## Proof depends on

None.

## Expansion

Section 4: let $s:E\times E\to E$ be subtraction and $\Delta=s^{-1}O$ the diagonal. The function $h_0=X_1/Z_1-X_2/Z_2$ has divisor $\Delta+\nabla-2V-2H$, and $Z_0=h_0^3Z_1^2Z_2^2$ is the $Z$-coordinate of a law of bidegree $(2,2)$. Dividing by $h_0^3$ and applying the Lemma of Section 2 identifies the laws of bidegree $(2,2)$ with $\{h:h=0\text{ or }(h)\ge-3\Delta\}$, and pulling back along $s$, an isomorphism onto this space because $s$ has connected fibers, identifies this with $\{h\in k(E):h=0\text{ or }(h)\ge-3O\}$, the space with basis $X/Z$, $Y/Z$, $1$. The law for $(a,b,c)$ has $Z_3=(as^*(X/Z)+bs^*(Y/Z)+c)Z_0$, and its exceptional divisor is the pullback under $s$ of $\operatorname{div}((aX+bY+cZ)/Z)+3O$, whose support is the inverse image under $s$ of $E\cap\{ax+by+cz=0\}$. For the consequence: a pair exceptional for both laws would have $P_1-P_2$ on both lines, hence at their intersection point, which is not on $E$ over any extension. Prerequisites still to add: divisors and pullbacks on $E\times E$, the subtraction map and the diagonal divisor.

## Sources

- W. Bosma and H. W. Lenstra, Jr., "Complete systems of two addition laws for elliptic curves", *Journal of Number Theory* 53(2):229–240, 1995, doi:10.1006/jnth.1995.1088, author-hosted scan of the printed article, <https://www.math.ru.nl/~bosma/pubs/JNT1995.pdf>, Theorem 2 (p. 230), the paragraph following it (p. 231), and Section 4 (pp. 234–235).
