# Mixed Gaussian moments of smoothed and exact projection densities

Use the unit sphere in $\mathbb R^d$ with normalized surface measure $\sigma_d$. For $G$ an array of $k$ rows, write $G s=(\langle G_i,s\rangle)_i$. For a finite measure $\rho$ on the sphere and $\delta>0$, put

$$
D_\delta(\rho;G,y)=(2\delta)^{-k}\,\rho\{s:\ |(Gs)_i-y_i|\le\delta\text{ for every }i\}.
$$

The exact density candidate $D_0$ takes the limit of the real projections of $D_{1/j}$ if that real limit exists, embeds it into the extended nonnegative reals, and otherwise uses zero. There is an absolute constant $C>0$ such that the following two bounds hold for all natural dimensions and row and moment counts $d,m,r,q$ satisfying $m,r,q\ge1$, $k=m+r<d-1$ and $r\ge q$. Let $\rho$ be any finite measure on the sphere, and let $B,D>0$ be any constants such that every ambient closed ball of radius $t>0$ has $\rho$-mass at most $Bt^k$ and also at most $Dt^{d-1}$. Let $X,Z$ denote independent arrays of $m,r$ standard Gaussian rows. Then for every sphere point $s$ and $\delta>0$,

$$
\mathbb E_X\Big(\mathbb E_Z D_\delta(\rho;(X,Z),(X,Z)s)\Big)^q
\le[e^{Cd}B(1+\max(0,\log(D/B)))]^q.
$$

If $\rho\ll\sigma_d$, there is a measurable $\rho$-null exception set of points $s$ such that outside it the full positive-radius limit $D_\delta\to D_0$ holds for almost every Gaussian array at $y=Gs$, the same mixed-moment bound, with the same absolute $C$, holds for $D_0$, and if $\rho\ne0$ this exact density is positive and finite at $Gs$ for almost every array.

**Conventions.** Use exact and smoothed projections of finite spherical measures, the two growth exponents, rectangular tubes, and conditional mixed moments in independent Gaussian row blocks.

## Depends on

- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

A two-scale spherical small-ball moment comparison for the concatenated rows and a coarea/differentiation theorem at a projected typical label.

## Expansion

Separate the mixed-moment estimate for every smoothing radius from almost-everywhere exact-density identification. Use a single null set of sphere points, handle the empty exception of zero measure, and preserve the order of the two Gaussian expectations and the power.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L433-L435)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
