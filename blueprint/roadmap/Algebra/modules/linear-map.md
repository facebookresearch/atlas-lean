# Linear map

Let $R$ be a semiring and let $M$ and $N$ be $R$-modules, with $M$ and $N$ commutative monoids under addition; for example $R$ can be a field $F$ and $M$, $N$ vector spaces over $F$. A function $f\colon M \to N$ is *linear*, or $R$-linear, if $f(x + y) = f(x) + f(y)$ and $f(c x) = c f(x)$ for all $x, y \in M$ and all $c \in R$; between vector spaces, linear maps are also called *linear transformations*. The same scalars $R$ act on $M$ and on $N$. A linear map from $M$ to itself is a *linear operator* on $M$, also called an endomorphism of $M$. Mathlib usually handles linear maps bundled with their linearity, as elements of the type written `M →ₗ[R] N`; these are the semilinear maps, which satisfy $f(c x) = \sigma(c) f(x)$ for a ring homomorphism $\sigma$, in the case where $\sigma$ is the identity of $R$.

## Sources

- Stephen H. Friedberg, Arnold J. Insel and Lawrence E. Spence, Linear Algebra, 4th ed., Prentice Hall, 2003.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the predicate that a function between modules over a semiring preserves addition and multiplication by scalars: `IsLinearMap`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/LinearMap/Defs.lean#L65-L74.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for bundled semilinear maps and the notation M →ₗ[R] N for linear maps: `LinearMap`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Module/LinearMap/Defs.lean#L78-L86.
