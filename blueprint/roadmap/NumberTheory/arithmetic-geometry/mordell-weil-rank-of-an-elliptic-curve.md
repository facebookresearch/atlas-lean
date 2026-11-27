# Mordell–Weil rank of an elliptic curve

For an elliptic curve $E$ over a number field $K$, the group $E(K)$ of $K$-rational points is a finitely generated abelian group by the Mordell–Weil theorem; its rank $\operatorname{rk} E(K)$ is the number of infinite cyclic factors in a decomposition of $E(K)$.

Let $K$ be a number field and let $E$ be an elliptic curve over $K$: a smooth projective curve of genus one over $K$ with a distinguished $K$-rational point $O$, for example the projective closure of a nonsingular Weierstrass equation with $O$ the point at infinity. The set $E(K)$ of points of $E$ with coordinates in $K$ is an abelian group, written additively, under the chord-and-tangent law with identity $O$. By the Mordell–Weil theorem it is finitely generated, so

$$
E(K) \cong E(K)_{\mathrm{tors}} \oplus \mathbb{Z}^{r}
$$

with $E(K)_{\mathrm{tors}}$ the finite torsion subgroup and a unique integer $r \ge 0$. The *Mordell–Weil rank* of $E$ over $K$ is

$$
\operatorname{rk} E(K) = r = \dim_{\mathbb{Q}} \bigl( E(K) \otimes_{\mathbb{Z}} \mathbb{Q} \bigr) .
$$

Conventions:

- The rank depends on the field: for a finite extension $K'/K$ the inclusion $E(K) \subseteq E(K')$ gives $\operatorname{rk} E(K) \le \operatorname{rk} E(K')$, and the inequality can be strict.
- $\operatorname{rk} E(K) = 0$ exactly when $E(K)$ is finite, and $\operatorname{rk} E(K) \ge 1$ exactly when $E(K)$ contains a point of infinite order.
- For an elliptic curve $E$ over a subfield $F \subseteq K$, $\operatorname{rk} E(K)$ means the rank of the base change of $E$ to $K$.

## Depends on

- [Abelian group](../../GroupTheory/group-basics/abelian-group.md)

## Proof depends on

- [Fundamental theorem of finitely generated abelian groups, invariant factor form](../../GroupTheory/abelian-groups/structure-of-finitely-generated-abelian-groups/equiv-free-prod-direct-sum-invariant-fac.md)

## Expansion

The decomposition is the structure theorem for finitely generated abelian groups applied to $E(K)$. The integer $r$ equals the dimension of $E(K) \otimes_{\mathbb{Z}} \mathbb{Q}$ because tensoring with $\mathbb{Q}$ kills the torsion subgroup and turns $\mathbb{Z}^r$ into $\mathbb{Q}^r$. Monotonicity in the field follows because a subgroup of a finitely generated abelian group has rank at most that of the group.

## Sources

- Jochen Koenigsmann, *Undecidability in number theory*, in: Model Theory in Algebra, Analysis and Arithmetic, Lecture Notes in Mathematics 2111, Springer, 2014, pp. 159–195, https://doi.org/10.1007/978-3-642-54936-6_5; the footnote to Theorem 5.1 of arXiv:1309.0441v1 states the decomposition of $E(K)$ into its torsion subgroup and a free abelian group of rank $\operatorname{rk} E(K)$.
- Bjorn Poonen, *Using elliptic curves of rank one towards the undecidability of Hilbert's tenth problem over rings of algebraic integers*, in: Algorithmic Number Theory (ANTS-V, Sydney, 2002), Lecture Notes in Computer Science 2369, Springer, 2002, pp. 33–42, https://doi.org/10.1007/3-540-45455-1_4, read as arXiv:math/0204001v1 (the only arXiv version), which recalls the Mordell–Weil theorem and the notation $\operatorname{rk} E(F)$ before its main theorem.
