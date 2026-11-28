# Some extensions of Thompson's group F by free groups have unsolvable conjugacy problem

There are groups $G$ with a normal subgroup isomorphic to Thompson's group $F$ and quotient a finitely generated free group whose conjugacy problem is unsolvable.

**Theorem (Burillo, Matucci and Ventura).** There are extensions of [Thompson's group $F$](thompson-f.md) by finitely generated free groups, that is, groups $G$ with a [normal subgroup](../../../group-basics/normal-subgroup.md) $N \cong F$ and [quotient](../../../group-basics/quotient-group.md) $G/N$ a finitely generated free group, with unsolvable conjugacy problem: no algorithm decides, for two words in a finite generating set of $G$, whether they represent conjugate elements (Theorem 1.4 of the source).

The source also shows that $\mathrm{Aut}(F)$ contains orbit undecidable subgroups (finitely generated subgroups $A$ such that no algorithm decides, for $u, v \in F$, whether $v$ is conjugate to $u\alpha$ for some $\alpha \in A$), and that $F$ itself has solvable twisted conjugacy problem (Theorem 1.2).

## Depends on

- [Thompson's group F by its standard presentation](thompson-f.md)
- [Normal subgroup](../../../group-basics/normal-subgroup.md)
- [Quotient group](../../../group-basics/quotient-group.md)

## Proof depends on

- [The membership problem for finitely generated subgroups of F₂ × F₂ is unsolvable](../../../presentations-and-decision-problems/membership-and-equation-problems/subgroup-membership-problem/membership-problem-in-f2-times-f2-unsolvable.md)

## Expansion

Bogopolski, Martino and Ventura showed that for an algorithmic short exact sequence $1 \to F \to G \to H \to 1$ with $H$ torsion-free hyperbolic, $G$ has solvable conjugacy problem if and only if $F$ has solvable twisted conjugacy problem and the action subgroup $A_G \le \mathrm{Aut}(F)$ is orbit decidable (Theorem 1.3 of the source applies this to $F$), and that $\mathrm{Aut}(F)$ has an orbit undecidable subgroup whenever $F_2 \times F_2$ embeds in $\mathrm{Aut}(F)$ meeting the stabilizer of the conjugacy class of some element trivially; this uses Mihailova's unsolvable membership problem in $F_2 \times F_2$. The source embeds $F_2 \times F_2$ in $\mathrm{Aut}^+(F)$ through germs at $\pm\infty$ of periodic piecewise linear maps (Corollary 3.3), checks the stabilizer condition, and takes the extension of $F$ by a free group realizing the resulting orbit undecidable subgroup. A complete expansion also links the Bogopolski–Martino–Ventura criteria for the conjugacy problem in extensions and for orbit undecidability, which have no pages here.

## Sources

- José Burillo, Francesco Matucci and Enric Ventura, "The conjugacy problem in extensions of Thompson's group $F$", *Israel Journal of Mathematics* 216(1):15–59, 2016, doi:[10.1007/s11856-016-1403-9](https://doi.org/10.1007/s11856-016-1403-9). Numbering of the version read, arXiv:1307.6750v2: Theorems 1.2, 1.3 and 1.4, Theorem 3.1 and Corollary 3.3.
