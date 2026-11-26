# Grand-product permutation argument with random linear combinations

Let $f_1,\dots,f_k$ and $g_1,\dots,g_k$ be vectors indexed by $H$ (so $kn$ positions), and $\sigma$ a permutation of the positions with $\mathrm{id}$ an injective labeling. For $\beta,\gamma\in\mathbb{F}$ define $z$ on $H$ by $z(1)=1$ and

$$
z(\omega^{i+1})=z(\omega^{i})\prod_{j=1}^{k}\frac{f_j(\omega^{i})+\beta\,\mathrm{id}_j(\omega^{i})+\gamma}{g_j(\omega^{i})+\beta\,\sigma_j(\omega^{i})+\gamma}.
$$

If the multisets $\{(f_j(x),\mathrm{id}_j(x))\}$ and $\{(g_j(x),\sigma_j(x))\}$ differ, then for uniformly random $\beta,\gamma$ the grand product $\prod_{j,x}(f_j(x)+\beta\mathrm{id}_j(x)+\gamma)/(g_j(x)+\beta\sigma_j(x)+\gamma)$ equals $1$ (equivalently $z(\omega^{n})=z(1)$ and the recurrence holds on $H$) with probability at most $kn/|\mathbb{F}|$. With $g_j=f_j$, this certifies that $f$ is invariant under $\sigma$, i.e., the copy constraints.

## Proof sketch

Multiset equality of pairs is equivalent to equality of the bivariate polynomials $\prod(f+\beta\,\mathrm{id}+Y)$ and $\prod(g+\beta\sigma+Y)$ in $\mathbb{F}[\beta,Y]$; if they differ, their difference has total degree at most $kn$, so by Schwartz–Zippel it vanishes at random $(\beta,\gamma)$ with probability at most $kn/|\mathbb{F}|$. The recurrence telescopes to the full product.

## Depends on

- [PLONK gate equations with copy constraints](plonk-constraint-system.md)
- [Vanishing on a multiplicative subgroup and the quotient test](subgroup-vanishing-quotient.md)

## Proof depends on

- [Vanishing on a multiplicative subgroup and the quotient test](subgroup-vanishing-quotient.md)

## Sources

- Ariel Gabizon, Zachary J. Williamson, Oana Ciobotaru, "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge", IACR ePrint 2019/953 (2019).
