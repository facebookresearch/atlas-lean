# Generalized outer radii for neutral Coulomb ground states

For each integer $Z\geq1$, choose any normalized ground wavefunction of the neutral $Z$-electron Coulomb form for one fixed nucleus of charge $Z$: two spin states per electron, antisymmetry in simultaneous spin/position permutations, square-integrable weak partial derivatives, and integrable Coulomb terms with kinetic coefficient $1/2$. A ground state minimizes this form over normalized wavefunctions in that domain. Its spatial density $\rho_Z(x)$ is $Z$ times the sum over all spins and integral over the other $Z-1$ positions of the squared modulus with first position $x$. Put $R_m(Z)=\inf\{r\geq0:\int_{|x|>r}\rho_Z(x)\,dx\leq m\}$. For each $m$ take the extended-real upper and lower limits of $R_m(Z)$ as integers $Z>m$ tend to infinity. Multiplying each by $m^{1/3}$ and taking $m\to\infty$ gives the same limit $(81\pi^2/2)^{1/3}$. The family of ground states is an input, not an asserted existence result.

## Depends on
The full two-spin neutral form domain, normalization, the one-particle marginal and its strict-exterior threshold, and extended-real limits.

## Proof depends on
Control of the exterior charge distribution compared to its Thomas–Fermi profile with a uniform radius error for the iterated regime.

## Expansion
Derive the normalization and monotonicity of the exterior mass function and characterize the radius infimum. Use both sides of the exterior mass comparison for each ground-state choice, preserving the order of the charge and exterior-mass limits.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoulombRadii.lean#L77-L85) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/263.md).
