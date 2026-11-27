# Vélu's formulas for the quotient by a finite subgroup

Vélu's formulas give, for a finite subgroup $G$ of an elliptic curve in Weierstrass form, an explicit Weierstrass equation for a curve $E/G$ and explicit rational functions for a separable isogeny $E\to E/G$ with kernel $G$, in every characteristic.

Let $E$ be an elliptic curve over a field $k$ given by $F(x,y)=x^3+a_2x^2+a_4x+a_6-y^2-a_1xy-a_3y=0$, and let $G\subseteq E(\bar k)$ be a finite subgroup. Let $G_2$ be the set of points of order $2$ in $G$, and choose $G_1$ so that $G=\{O\}\cup G_2\cup G_1\cup\{-Q:Q\in G_1\}$ is a disjoint union, so $\#G=1+\#G_2+2\#G_1$. Put $F_x=3x^2+2a_2x+a_4-a_1y$ and $F_y=-2y-a_1x-a_3$, and for $Q=(x_Q,y_Q)\in G_1\cup G_2$

$$
u(Q)=F_y(Q)^2,\qquad t(Q)=\begin{cases}F_x(Q)&Q\in G_2,\\ 2F_x(Q)-a_1F_y(Q)&Q\in G_1,\end{cases}
$$

$$
t(G)=\sum_{Q\in G_1\cup G_2}t(Q),\qquad w(G)=\sum_{Q\in G_1\cup G_2}\bigl(u(Q)+x_Qt(Q)\bigr).
$$

Let $\tilde E\colon Y^2+A_1XY+A_3Y=X^3+A_2X^2+A_4X+A_6$ with $A_1=a_1$, $A_2=a_2$, $A_3=a_3$, $A_4=a_4-5t(G)$ and $A_6=a_6-(a_1^2+4a_2)t(G)-7w(G)$. Then the map $(x,y)\mapsto(X,Y)$ with

$$
X=x+\sum_{Q\in G_1\cup G_2}\left(\frac{t(Q)}{x-x_Q}+\frac{u(Q)}{(x-x_Q)^2}\right),
$$

$$
Y=y-\sum_{Q\in G_1\cup G_2}\left(u(Q)\frac{2y+a_1x+a_3}{(x-x_Q)^3}+t(Q)\frac{a_1(x-x_Q)+y-y_Q}{(x-x_Q)^2}+\frac{a_1u(Q)-F_x(Q)F_y(Q)}{(x-x_Q)^2}\right)
$$

is a separable [isogeny](isogeny-of-elliptic-curves.md) $E\to\tilde E$ with kernel $G$, and it is normalized: it pulls back $dX/(2Y+A_1X+A_3)$ to $dx/(2y+a_1x+a_3)$. If $k$ is perfect and $G$ is stable under $\operatorname{Gal}(\bar k/k)$, then $\tilde E$ and the isogeny are defined over $k$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

- [Every finite subgroup is the kernel of a separable isogeny](separable-isogeny-with-prescribed-kernel.md)

## Expansion

The function $X(P)=x(P)+\sum_{Q\in G\setminus\{O\}}\bigl(x(P+Q)-x(Q)\bigr)$ is invariant under translation by $G$, and similarly for $Y$, so $(X,Y)$ factors through the quotient by $G$. Expanding in the uniformizer $-x/y$ at $O$ gives the stated rational functions and shows that they satisfy the equation of $\tilde E$ and preserve the invariant differential. For the field of definition, $t(G)$, $w(G)$, $X$ and $Y$ are fixed by $\operatorname{Gal}(\bar k/k)$ when $G$ is. For $y^2=x^3+Ax+B$ and $\#G$ odd or $\#G=2$ this specializes to Sutherland's form $A'=A-5t$, $B'=B-7w$ (his Theorems 5.13 and 5.15, with sums over all nonzero points of $G$); Charles, Goren and Lauter, Section 4.2, give the order-$2$ case on short Weierstrass models. Galbraith's Theorem 25.1.6 is the authority for the general formulas above. The quotient by $G$ that these formulas make explicit is the separable isogeny with kernel $G$ of the page on prescribed kernels. A good expansion adds pages for the uniformizer expansions of $x$, $y$ and the invariant differential at the origin.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Theorem 25.1.6, Corollary 25.1.7 and Definition 25.1.10.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Theorems 5.13 and 5.15 and Remark 5.16 (short Weierstrass models, $\#G=2$ or odd).
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 4.2 (order $2$).
