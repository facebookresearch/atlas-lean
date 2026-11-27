# Asymptotic order of four convex-body covering-density suprema

For a convex body $K\subset\mathbb R^n$ define $\theta_L(K)=\inf_L |K|/\operatorname{covol}(L)$ over discrete full-rank lattices with $K+L=\mathbb R^n$. Define $\theta_T(K)$ by taking the infimum of

$$|K|\limsup_{R\to\infty}\frac{\#(X\cap[-R,R]^n)}{(2R)^n}$$

over locally finite sets $X$ of centers with $K+X=\mathbb R^n$. Densities and extrema are in the extended nonnegative reals. Form four suprema by using each of $\theta_T$ and $\theta_L$ over all convex bodies, and over centrally symmetric convex bodies (center arbitrary). There exist common $c,C>0$ and an integer $n_0$ such that, for every $n\ge n_0$, each of the four suprema belongs to $[cn\log n,Cn\log n]$.

## Depends on

- [Convex body](../hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Locally finite center intensity by a cube limsup, lattice covolume, and both exact covering predicates.

## Proof depends on

- [Single-lattice covering upper bound](single-lattice-covering-upper-bound.md)
- Matching lower bound witnessed already in the centrally symmetric class; comparison of lattice and translative densities.

## Expansion

Prove the comparison from density of lattice centers and pass to the four suprema without totalizing infinity. Separate common lower and upper bounds, with the single-lattice estimate available for the latter.

## Sources

- OpenAI Math, [`optimal_order`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoveringDensity.lean#L111-L115) (statement and local definitions).
