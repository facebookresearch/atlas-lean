# Averaged asymptotic midpoint modulus for a forest coordinate space

Let $V$ be a countably infinite partially ordered set in which every principal lower set is a finite chain. Give the [segment coordinate space](segment-coordinate-space.md) $X(V)$ its inherited norm $N(z)=\|z\|$, and use the [unit-direction averaged modulus](unit-direction-asymptotic-moduli.md) of that norm. For every real $t>0$,

$$\widetilde\delta_N(t)\ge\sqrt{1+t^2/12}-1.$$

This is a lower bound, not a formula for equality, and uses the closed coordinate span even when it has not been identified with the full dual.

## Depends on

- [Coordinate space of a segment-norm completion](segment-coordinate-space.md).
- [Unit-direction asymptotic moduli](unit-direction-asymptotic-moduli.md).

## Proof depends on

- [Finite lower-head projections](finite-lower-head-projections.md) and the [paired midpoint estimate](paired-midpoint-estimate.md).

## Proof outline

A finite linear combination of coordinate functionals has a finite support, and the union of its principal lower sets is still finite. Tail contractivity transfers this approximation to $P_H x$ for a norm-one center $x$. In the kernel of restriction to $H$, apply the paired bound to $P_Hx$ and $ty$ for every unit $y$. The error in replacing $P_Hx$ by $x$ goes to zero with the head-approximation error, uniformly in $y$. Take the infimum over the unit directions, then the supremum over the closed finite-codimensional subspaces, and finally the infimum over the centers. Unit directions are available since the coordinate functionals are linearly independent and $V$ is infinite.

## Sources

- OpenAI, [general-forest statement, third conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Main.lean#L32-L41), [finite-head approximation and coordinate kernel](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/Projections.lean#L165-L212), [perturbation and passage to the modulus](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/ForestSpace/ModulusProofs.lean#L98-L158).
- OpenAI, [*Asymptotic midpoint uniform convexity and unbounded diamond distortion in a reflexive tree space*, §4.1, (4.4)](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf); [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
