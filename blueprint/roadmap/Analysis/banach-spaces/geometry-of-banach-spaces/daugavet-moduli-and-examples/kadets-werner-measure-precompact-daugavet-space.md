# A measure-precompact Daugavet space on the product unit interval

For countable product probability $\mu$ of uniform measures on $[0,1]$, there is a norm-closed infinite-dimensional real subspace $E\subset L^1(\mu)$ whose whole unit ball is precompact for $d(f,g)=\inf\{a>0:\mu(|f-g|>a)<a\}$, with finite covers by centers in $L^1(\mu)$. It has the Daugavet rank-one equation. It also has this unit-slice property: for every unit $w\in E$, every continuous real linear functional $\ell$, every real $a$ with $\ell(u)>a$ for some $\|u\|\le1$, and every $\rho>0$, there is a unit $y$ with $\ell(y)>a$ and $\|w+y\|\ge2-\rho$.

## Depends on

- Countable product measure, measure-distance finite covers and the rank-one and slice properties above.

## Proof depends on

- Construction of the closed subspace, compactness in measure of its entire unit ball, and the unit-slice estimate giving Daugavet behavior.

## Expansion

Track the underlying product probability and prove measure-cover and slice properties on the same subspace. Ordinary norm-precompactness would be incompatible with its infinite dimension.

## Sources

- OpenAI, [DaugavetModuli comparator, kadets_werner_existence](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DaugavetModuli.lean#L85-L90).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
