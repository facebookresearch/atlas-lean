# Property R∞

A group has property $R_\infty$ when, for every automorphism $\varphi$, it has infinitely many $\varphi$-twisted conjugacy classes, the classes of the relation $x \sim_\varphi y$ iff $y = (w\varphi)\, x\, w^{-1}$ for some $w$.

Let $G$ be a [group](../../../group-basics/group.md) and $\varphi$ an automorphism of $G$, written on the right, so $w\varphi$ is the image of $w$. Elements $x, y \in G$ are *$\varphi$-twisted conjugate*, $x \sim_\varphi y$, if $(w\varphi)\, x\, w^{-1} = y$ for some $w \in G$; this is an equivalence relation, and the class of the identity is the [twisted conjugacy class of the identity](twisted-unit-class.md) up to the side convention. $G$ has *property $R_\infty(\varphi)$* if $\sim_\varphi$ has infinitely many classes, and *property $R_\infty$* if it has $R_\infty(\varphi)$ for every automorphism $\varphi$. Composing $\varphi$ with an inner automorphism does not change whether $R_\infty(\varphi)$ holds.

For example, $\mathbb{Z}$ does not have property $R_\infty$: for the automorphism $n \mapsto -n$ there are exactly two twisted conjugacy classes. Non-elementary hyperbolic groups and accessible groups with infinitely many ends have property $R_\infty$.

## Depends on

- [Group](../../../group-basics/group.md)
- [Twisted conjugacy class of the identity (Kourovka 18.15)](twisted-unit-class.md)
- [Twisted conjugacy problem](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/conjugacy-problem-in-group-extensions/twisted-conjugacy-problem.md)

## Proof depends on

None.

## Sources

- Francesco Fournier-Facio, Harry Iveson, Armando Martino, Wagner Sgobbi and Peter Wong, "Property $R_\infty$ for groups with infinitely many ends", *Geometriae Dedicata* 220(3):25, 2026, doi:[10.1007/s10711-026-01078-x](https://doi.org/10.1007/s10711-026-01078-x). Numbering of the version read, arXiv:2504.12002v3: Definitions 2.1, 2.5 and 2.7, Lemmas 2.4 and 2.6, and the proof of the undecidability corollary in Section 4.
