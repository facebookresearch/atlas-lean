# Sign-pattern and Lotka–Volterra inference from steady-state samples

**Model.** Abundances $x = (x_1, \dots, x_N) \in \mathbb R_{\ge 0}^N$ of $N$ taxa follow

$$\dot x_i = x_i\, f_i(x), \qquad i = 1, \dots, N,$$

with $f_i$ continuously differentiable and no immigration. A steady-state sample is a non-trivial equilibrium $x^I$ whose set of present taxa is $I \subseteq \{1, \dots, N\}$, so $f_i(x^I) = 0$ for every $i \in I$. The interaction types are the signs of the Jacobian $J_{ij}(x) = \partial f_i / \partial x_j$: $J_{ij} > 0$ ($< 0$, $= 0$) means taxon $j$ promotes (inhibits, does not affect) the growth of taxon $i$. Assume $\operatorname{sign} J(x)$ is constant on $\mathbb R_{\ge 0}^N$.

**Orthogonality constraint.** Let $\mathcal I_i$ be the collection of observed samples containing taxon $i$. For any $I, K \in \mathcal I_i$,

$$0 = f_i(x^K) - f_i(x^I) = y^{\mathsf T} (x^K - x^I), \qquad y = \int_0^1 J_{i\cdot}\bigl(x^I + \sigma (x^K - x^I)\bigr)^{\mathsf T}\, d\sigma,$$

and $y$ has the same sign pattern $s_i \in \{-, 0, +\}^N$ as the $i$-th row of $J$. Hence $s_i$ lies in the set $\hat S_i$ of sign patterns realized by vectors orthogonal to all differences $x^K - x^I$, $I, K \in \mathcal I_i$. With enough independent samples, $\hat S_i$ shrinks to $\{-a, 0, a\}$ for a single pattern $a$, and knowing the sign of one nonzero entry (for example $J_{ii} < 0$, self-limitation) fixes $s_i$. If more patterns remain, the data cannot distinguish them, whatever the algorithm.

**Generalized Lotka–Volterra case.** If $f_i(x) = r_i + \sum_{j} a_{ij} x_j$, every steady-state sample containing taxon $i$ satisfies

$$r_i + \sum_{j=1}^{N} a_{ij}\, x^I_j = 0, \qquad I \in \mathcal I_i,$$

so these samples lie on a hyperplane in $\mathbb R^N$. Given at least as many affinely independent samples in $\mathcal I_i$ as unknowns, the row $(a_{i1}, \dots, a_{iN})$ and growth rate $r_i$ are determined up to a common scale factor, fixed by one known value (for example the self-interaction $a_{ii}$ or the carrying capacity of taxon $i$ in monoculture). The coefficient of determination of the hyperplane fit measures how far the dynamics of taxon $i$ departs from the Lotka–Volterra form.

## Depends on

- [Generalized Lotka–Volterra vector field](../../replicator-and-lotka-volterra-equivalence/lv-field.md)

## Expansion

The orthogonality relation is the fundamental theorem of calculus applied to $f_i$ along the segment joining two equilibria at which taxon $i$ is present; the line segment lies in the nonnegative orthant, where the sign assumption holds. Geometrically each difference vector defines a hyperplane through the origin, and the admissible sign patterns are the orthants (including lower-dimensional faces) that every such hyperplane crosses; intersecting over all sample pairs is a finite combinatorial computation, exhaustive for small communities and heuristic for larger ones. In the Lotka–Volterra case the constraint is linear and exact, so the parameters follow from a regression of zero on the abundances of samples containing taxon $i$; sparsity-promoting regularization, with false-discovery control, is used when samples are fewer than unknowns. Applied to an eight-species synthetic soil community, 50 of 64 interaction signs matched the pairwise-culture ground truth.

## Sources

- Y. Xiao, M. T. Angulo, J. Friedman, M. K. Waldor, S. T. Weiss, Y.-Y. Liu, "Mapping the ecological networks of microbial communities", Nature Communications (2017), Results, model (Eq. 1) and assumption $\operatorname{sign} J = \text{const}$; "Inferring the sign-pattern" (orthogonality of $s_i$ and $x^I - x^K$, Figure 1); inference of GLV parameters by hyperplane fitting; Supplementary Note 1, Proposition 1 and Theorem 2. <https://doi.org/10.1038/s41467-017-02090-2> (PMC5725606).
