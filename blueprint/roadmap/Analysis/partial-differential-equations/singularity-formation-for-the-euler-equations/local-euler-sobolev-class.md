# All-orders Sobolev Euler solutions on a time interval

For a time interval $I$ containing $0$, a Sobolev-smooth path $v$ is spatially smooth for every $t\in I$, with $v(\cdot,t)$ and every actual spatial derivative tensor $D_x^m v(\cdot,t)$ in $L^2(\mathbb R^3)$. All these $L^2$ classes are continuous in $t$ on $I$.

A solution for $u_0$ consists of such a path $v$ and a scalar pressure $p$. For all $t\in I$, $v$ is divergence-free, and $v(x,0)=u_0(x)$. At interior times only, the spatial function $p(\cdot,t)$ is differentiable. There must exist a Sobolev-smooth path $w$ on $I$ such that at each interior time the strong time derivative of the $L^2$ class of $v$ is the class of $w$, and $w+D_xv\,v=-\nabla_xp$ holds pointwise. There is no endpoint time-derivative condition, no time regularity imposed on pressure and no pressure normalization.

## Depends on

- [Divergence](div.md)

## Expansion

Construct the continuous paths of actual derivative tensors in the appropriate L² spaces. Match the source strong derivative on interior times and distinguish the half-open lifespan from closed comparison intervals.

## Sources

- [Pinned Sobolev path and scalar-pressure definitions](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/ComparatorChallenges/Euler.lean#L111-L147)
