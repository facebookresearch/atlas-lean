# Generalized ionization-energy asymptotics of Coulomb atoms

Let $E_Z(N)$ be the infimum for a fixed nucleus of charge $Z$ of the form with kinetic coefficient $1/2$, attraction $-Z\sum_i|x_i|^{-1}$ and repulsion $\sum_{i<j}|x_i-x_j|^{-1}$. For $N>0$ the domain consists of normalized complex wavefunctions on $(\mathbb R^3)^N$ with two spin values per particle, antisymmetric under simultaneous permutations of space and spin, with $L^2$ weak partial derivatives and integrable Coulomb form terms. Use $E_Z(0)=0$ and the Lebesgue integrals with inverse norms totalized by zero at coincidence. For integers $m,Z$ put $I_m(Z)=E_Z(Z-m)-E_Z(Z)$, with natural subtraction.

There is $a>0$ such that $I_m(Z)/m^{7/3}\to a$ along every integer sequence with $1\leq m<Z$, $m\to\infty$ and $Z/m\to\infty$. Also both $\limsup_{Z\to\infty}I_m(Z)/m^{7/3}$ and $\liminf_{Z\to\infty}I_m(Z)/m^{7/3}$, with the normalization applied after the inner limit, converge to $a$ as $m\to\infty$. These are the source’s real-valued filter limsup and liminf along the natural $Z$-tail, not extended-real limits: the real supremum and infimum use their totalized values when the defining set is empty or unbounded in the relevant direction. No boundedness hypothesis is added. For the variational coefficient, use $E_Z^{\rm TF}(M)$ as the infimum over nonnegative integrable densities $\rho$ of mass $M$ and finite kinetic and Coulomb integrals, with energy $(3/10)(3\pi^2)^{2/3}\int\rho^{5/3}-Z\int \rho(x)/|x|+\tfrac12\iint \rho(x)\rho(y)/|x-y|$. For every real $m>0$, $E_Z^{\rm TF}(Z-m)-E_Z^{\rm TF}(Z)\to a m^{7/3}$ as real $Z\to\infty$.

## Depends on
Spin-resolved antisymmetric Sobolev forms, fixed-charge atomic and density infima, and the specified joint and iterated limit regimes.

## Proof depends on
The Thomas–Fermi asymptotic coefficient and a comparison of Coulomb energy differences with the Thomas–Fermi differences at the $m^{7/3}$ scale.

## Expansion
First show the infima are meaningful and stable under null-set changes. Separate the Thomas–Fermi limit from the many-body comparison; prove error control for the joint regime and keep both of the distinct iterated limits. There is no molecular binding-count statement.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoulombIonization.lean#L92-L94) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/263.md).
