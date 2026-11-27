# Phase transition in the number of irreducible blocks of energy-weighted RNA secondary structures

**Setting.** An RNA secondary structure on $n$ vertices is a noncrossing diagram of arcs $(i,j)$ with $j - i \ge 4$ in the upper half-plane. It is **irreducible** if it contains the arc $(1,n)$. Every structure is uniquely a sequence of single unpaired vertices and irreducible blocks. Weight each structure by $p^{\#\text{arcs}}\, v^{\text{energy}}$, where the energy is a loop-based additive model (hairpin, interior/bulge/stack and multiloop contributions with parameters $\alpha_k, \beta_k, \gamma_k$), $p = 6/16$ is the probability that two random nucleotides can pair, and $v = e^{1/RT}$. Let $\mathbf{C}^*(z) = \sum_n c^*(n) z^n$ and $\mathbf{S}^*(z) = \sum_n s^*(n) z^n$ be the weighted generating functions of irreducible structures and of all structures.

**Generating functions.** The trivariate generating function $\mathbf{C}(z,v,p)$ (length, energy, arcs) satisfies a closed recursion obtained by the symbolic method, so $\mathbf{C}^*$ is the unique root with positive coefficients of a quadratic $w_2^*(z)\mathbf{C}^2 + w_1^*(z)\mathbf{C} + w_0^*(z) = 0$ with polynomial coefficients, and

$$\mathbf{S}^*(z,t) = \frac{1}{1 - \big(z + t\,\mathbf{C}^*(z)\big)},$$

where $t$ marks irreducible blocks. Let $X_n$ be the number of irreducible blocks of a random structure of length $n$ drawn with probability proportional to its weight, so $\mathbb{P}(X_n = t) = s^*(n,t)/s^*(n)$.

**Theorem.** Let $\rho_{c^*}$ and $\rho_{s^*}$ be the dominant singularities of $\mathbf{C}^*$ and $\mathbf{S}^*$ (both unique; $\rho_{c^*}$ is a square-root branch point).

1. *(Subcritical.)* If $\rho_{s^*}$ is also exclusively a branch point ($\rho_{s^*} = \rho_{c^*}$), then $X_n$ has a discrete limit law and $c^*(n)/s^*(n) \to \chi > 0$.
2. *(Supercritical.)* If $\rho_{s^*} < \rho_{c^*}$ is a simple pole (the root of $1 - z - \mathbf{C}^*(z) = 0$), then $X_n$ is asymptotically Gaussian after standardization and $c^*(n)/s^*(n) \to 0$.
3. *(Critical.)* If $\rho_{s^*} = \rho_{c^*}$ is simultaneously a branch point and a simple pole, then $X_n$ satisfies a local limit law with Rayleigh density and $c^*(n)/s^*(n) \sim \chi'/n$ with $\chi' > 0$.

Which regime occurs is decided by the energy parameters through the location of $\rho_r$ relative to $\rho_p$.

## Depends on

- [Waterman's recursion](../../mccaskill-partition-function-for-rna-folding/waterman-number.md)

## Expansion

$\mathbf{S}^*(z,t) = g(t\,h(z))$ is a sequence composition scheme with outer function $g(u) = 1/(1 - z - u)$ and inner function $h = \mathbf{C}^*$. By Pringsheim's theorem the dominant singularities are real and positive. $\mathbf{C}^*$ inherits a square-root singularity at the smallest odd-order positive root $\rho_r$ of the discriminant $w_1^{*2} - 4 w_2^* w_0^*$; $\mathbf{S}^*$ is singular either there or at the first root $\rho_p$ of $z + \mathbf{C}^*(z) = 1$, which is a simple root. The three cases are exactly the subcritical, supercritical and critical composition schemes of analytic combinatorics: a dominant inner singularity gives a discrete limit law, a dominant outer pole gives a Gaussian law via quasi-powers, and coalescence of the two gives the Rayleigh law. The coefficient ratios follow from transfer theorems at the respective singularities.

## Sources

- Hillary S.W. Han, Christian M. Reidys, "A Phase Transition in Energy-Filtered RNA Secondary Structures", Journal of Computational Biology 19 (2012), 1105–1119, <https://doi.org/10.1089/cmb.2012.0151>. Published version of arXiv:1205.3664, cited next; locators there refer to the arXiv version.
- Hillary S. W. Han, Christian M. Reidys, "A phase transition in energy-filtered RNA secondary structures", arXiv (2012). Theorems 1, 2 and 4, Lemmas 1–3, Definition 1. <https://doi.org/10.48550/arXiv.1205.3664>
