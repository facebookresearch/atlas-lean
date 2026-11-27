# Smoothness of the BHV Fréchet variance and convergence of the inductive mean

Let $\mathcal{T}_n$ be BHV tree space with geodesic metric $d$ and let $T^1,\dots,T^r \in \mathcal{T}_n$. The **Fréchet variance function** and **mean** are

$$

S(X) = \frac1r \sum_{\ell=1}^r d(X,T^\ell)^2, \qquad \overline{T} = \arg\min_{X \in \mathcal{T}_n} S(X).

$$

**Theorem.**

1. $S$ is strictly convex along geodesics of $\mathcal{T}_n$; consequently the mean $\overline{T}$ exists, is unique, and is the unique local minimum of $S$.
2. $S$ is continuously differentiable on the interior of every maximal orthant $\mathcal{O}$ of $\mathcal{T}_n$. On each multivistal cell for $\{T^1,\dots,T^r\}$, $S$ has a fixed $C^\infty$ algebraic formula in the squared edge lengths, and the squared-coordinate function $S^2$ is continuously differentiable on the interior of each maximal orthant.
3. (First-order condition.) The squared image $\overline{\mathcal{X}}$ of the mean satisfies $\nabla S^2(\overline{\mathcal{X}}) = 0$ on its orthant; if $\overline{\mathcal{X}}$ lies in the interior of a maximal orthant, this condition is also sufficient.
4. (Inductive mean.) Let $X^1,X^2,\dots$ be drawn independently and uniformly from $\{T^1,\dots,T^r\}$. Set $\mu_1 = X^1$ and let $\mu_\ell$ be the point at fraction $1/\ell$ along the geodesic from $\mu_{\ell-1}$ to $X^\ell$. Then $\mu_\ell \to \overline{T}$ almost surely.

## Expansion

Item 1 holds in any CAT(0) space: $d(\cdot,T)^2$ is $2$-uniformly convex along geodesics. Item 4 is Sturm's law of large numbers for barycentres in global NPC spaces, made effective by the polynomial-time geodesic algorithm. For item 2, on a multivistal cell each $d(X,T^\ell)$ equals the norm of a vector of $\|A_i\|+\|B_i\|$ terms whose combinatorial type is fixed, so $S$ is a fixed algebraic function; adjacent cells agree to first order along common faces inside an orthant interior. This enables a descent method that moves within cells and across their faces, alongside Sturm's stochastic algorithm.

## Sources

- Ezra Miller, Megan Owen, J. Scott Provan, "Polyhedral computational geometry for averaging metric phylogenetic trees", arXiv (2012); Advances in Applied Mathematics (2015). Proposition 2.1, Theorem 2.2, Definition 2.3, Theorem 2.4, Corollaries 4.1–4.2. <https://doi.org/10.48550/arXiv.1211.7046>. Published version: Advances in Applied Mathematics 68 (2015), 51–91, <https://doi.org/10.1016/j.aam.2015.04.002>; locators above refer to the arXiv version.
