# Mixed moments of two path functionals

With $X$, $T^*$ and $G$ as in the moment recursion for additive path functionals, and continuous $g, h \ge 0$ with $Gg$ and $Gh$ bounded, the functionals $A_g = \int_0^{T^*}g(X_t)\,dt$ and $A_h = \int_0^{T^*}h(X_t)\,dt$ satisfy

$$E_p[A_gA_h] = G\bigl(g\,Gh + h\,Gg\bigr)(p),$$

so $\mathrm{Cov}_p(A_g, A_h) = G(g\,Gh + h\,Gg)(p) - (Gg)(p)\,(Gh)(p)$. Derivation: $A_gA_h = \int_0^{T^*}g(X_s)\int_s^{T^*}h(X_t)\,dt\,ds + \int_0^{T^*}h(X_s)\int_s^{T^*}g(X_t)\,dt\,ds$; the Markov property at the earlier time $s$ replaces the inner integrals by $(Gh)(X_s)$ and $(Gg)(X_s)$, and the occupation formula (Karlin and Taylor 1981, Chapter 15) integrates the result. For $g = h$ this is $E_p[A_g^2] = 2G(g\,Gg)$, the case $n = 2$ of the moment recursion. Nagylaki (1974, abstract) expresses moments of such path integrals through sojourn times.

## Depends on

- [Green function, occupation times and mean exit times of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md)
- [Moment recursion for additive path functionals](../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)

## Expansion

1. The split of $A_gA_h$ into the two time orderings.
2. The Markov property at the earlier time and the occupation formula.
3. The covariance formula and the case $g = h$.
4. Higher mixed moments as sums over orderings of the factors.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (the Green's function and the occupation formula).
- T. Nagylaki, The moments of stochastic integrals and the distribution of sojourn times, Proc. Natl. Acad. Sci. USA 71 (1974), 746–749, abstract. <https://doi.org/10.1073/pnas.71.3.746>
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, New York (2008), Chapter 7, Sections 7.3–7.7 (the diffusion facts cited above from Karlin and Taylor, Chapter 15). <https://doi.org/10.1007/978-0-387-78168-6>
