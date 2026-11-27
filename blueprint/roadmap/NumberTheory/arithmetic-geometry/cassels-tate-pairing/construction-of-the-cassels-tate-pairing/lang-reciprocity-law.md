# Lang's reciprocity law for divisors on a product

Let $k$ be a field with algebraic closure $\bar k$, and let $V$ and $W$ each be an
[abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $k$ or a principal homogeneous
space over $k$ of one. For such a $V$, with abelian variety $B$, let $Z^0(V_{\bar k})$ be the group of $0$-cycles of
degree $0$ on $V_{\bar k}$ and $Y^0(V_{\bar k})$ the kernel of the summation map $Z^0(V_{\bar k}) \to B(\bar k)$: on an
abelian variety it is the sum in the group law, and on a principal homogeneous space it sends $\sum_i n_i P_i$ to
$\sum_i n_i (P_i - P_0)$, where $P_i - P_0 \in B(\bar k)$ is the point taking $P_0$ to $P_i$, which does not depend on
$P_0 \in V(\bar k)$ as $\sum_i n_i = 0$.

Let $D$ be a divisor on $V \times W$. For $x \in V(\bar k)$ let $D(x) \in \operatorname{Div}(W_{\bar k})$ be the pull-back of
$D$ along $W \to V \times W$, $w \mapsto (x, w)$, defined when $\{x\} \times W$ is not contained in the support of $D$, and
extend linearly to $0$-cycles $\mathfrak{a}$ on
$V_{\bar k}$. For $\mathfrak{a} \in Y^0(V_{\bar k})$ with $D(\mathfrak{a})$ defined, $D(\mathfrak{a})$ is the divisor of a
function $f$ on $W_{\bar k}$, determined up to a constant; for $\mathfrak{a}' = \sum_j n_j y_j \in Z^0(W_{\bar k})$ avoiding
the zeros and poles of $f$, put

$$D(\mathfrak{a}, \mathfrak{a}') = f(\mathfrak{a}') = \prod_j f(y_j)^{n_j},$$

which does not depend on the constant. Write ${}^tD$ for the transpose of $D$ on $W \times V$.

**Theorem.** If $\mathfrak{a} \in Y^0(V_{\bar k})$ and $\mathfrak{a}' \in Y^0(W_{\bar k})$, and the support of
$\mathfrak{a} \times \mathfrak{a}'$ in $V \times W$ is disjoint from the support of $D$, then $D(\mathfrak{a}, \mathfrak{a}')$ and
${}^tD(\mathfrak{a}', \mathfrak{a})$ are defined and

$$D(\mathfrak{a}, \mathfrak{a}') = {}^tD(\mathfrak{a}', \mathfrak{a}).$$

This is the case of Lang's law that the Cassels–Tate pairing uses. Poonen and Stoll state it for any two varieties in
their sense, geometrically integral, smooth and projective (§2, p. 1113), with $Y^0$ the kernel of the map to the
Albanese variety; for such a curve $C$, $V = W = C$ and $D$ the diagonal, that general form is Weil's reciprocity law
$f(\operatorname{div} g) = g(\operatorname{div} f)$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- that $D(\mathfrak{a})$ is principal for $\mathfrak{a} \in Y^0(V_{\bar k})$, by the theorem of the square, through which the
  class of $D(x)$ in $\operatorname{Pic}(W_{\bar k})$ depends on $x$ through a homomorphism to $\operatorname{Pic}^0$ plus a
  constant (Poonen and Stoll refer to the proof of Lang's Theorem 10 for this);
- the reciprocity itself, Lang, *Abelian Varieties*, Chapter VI, §4, Theorem 10;
- [Weil reciprocity](../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/evaluation-at-rational-places/weil-reciprocity.md),
  for the case of curves, with the comparison of the two formulations.

## Depends on

- [Abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over a field and their group law

## Proof depends on

- [Theorem of the cube, theorem of the square and the seesaw principle](../../../../AlgebraicGeometry/abelian-varieties/theorem-of-the-cube.md), for the theorem of the square (its item 4), through which $D(\mathfrak{a})$ is principal for $\mathfrak{a} \in Y^0(V_{\bar k})$

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §2, pp. 1113–1114 (the standing assumption that varieties are geometrically integral,
  smooth and projective, p. 1113, the groups $Z^0$ and $Y^0$, the definitions of $D(\mathfrak{a})$ and
  $D(\mathfrak{a}, \mathfrak{a}')$, and the statement: "Lang's reciprocity law (p. 171 of [La1] again) states that
  $D(\mathfrak{a}, \mathfrak{a}')$ and ${}^tD(\mathfrak{a}', \mathfrak{a})$ are defined and equal, provided that
  $\mathfrak{a} \times \mathfrak{a}'$ and $D$ have disjoint supports").
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 3.5, p. 44 (the law for a Poincaré divisor on $A^t \times A$, citing Lang 1959, VI 4, Thm 10).
- S. Lang, *Abelian Varieties*, Chapter VI, §4, Theorem 10, p. 171 of the Springer-Verlag edition of 1983, as cited
  by Poonen and Stoll, §2, p. 1114; not read.
