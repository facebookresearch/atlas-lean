# Injectivity precludes multiple equilibria (Craciun–Feinberg)

For a reaction network $\mathcal N$ in a continuous-flow stirred-tank reactor, with an outflow reaction for every species, let $p_{\mathcal N}(c, k)$ be the mass-action species-formation rate, a function of positive concentrations $c$ and positive rate constants $k$. The network is injective if $c \mapsto p_{\mathcal N}(c, k)$ is injective on the positive orthant for every $k$. Craciun and Feinberg (2005) prove: $\mathcal N$ is injective if and only if $\det(\partial p_{\mathcal N}/\partial c\,(c, k)) \ne 0$ for all positive $c$ and $k$ (Theorem 3.1). The coefficient test concerns a sign, not only nonvanishing, so it is stated for $-\partial p_{\mathcal N}/\partial c$, the negative of the Jacobian of the species-formation rate $p_{\mathcal N}$ (the map of Definition 2.7): $\mathcal N$ is injective if and only if all coefficients in the polynomial expansion of $\det(-\partial p_{\mathcal N}/\partial c)$ are nonnegative (Theorem 3.3). For a single species with only an outflow at rate $k$, $p_{\mathcal N}(c, k) = -kc$ is injective and $\det(-\partial p_{\mathcal N}/\partial c) = k$, while $\det(\partial p_{\mathcal N}/\partial c) = -k$ has a negative coefficient. An injective network cannot have two distinct positive equilibria for any rate constants.

## Depends on

- [Mass-action vector field](../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

1. The model: CFSTR networks with outflow of every species, mass-action rates, and the species-formation function.
2. Theorem 3.1: the equivalence of injectivity with nonvanishing of the Jacobian determinant, via a monomial change of variables that makes the determinant polynomial in $k$.
3. Theorem 3.3: the coefficient-sign criterion for $\det(-\partial p_{\mathcal N}/\partial c)$, the determinant of the negated Jacobian of $p_{\mathcal N}$.
4. The consequence for multiple equilibria, and the extension to networks without full outflow (restricted to compatibility classes) as a separate statement.

## Sources

- G. Craciun and M. Feinberg, Multiple equilibria in complex chemical reaction networks: I. The injectivity property, SIAM J. Appl. Math. 65 (2005), 1526–1546, Theorems 3.1 and 3.3. <https://doi.org/10.1137/s0036139904440278>
