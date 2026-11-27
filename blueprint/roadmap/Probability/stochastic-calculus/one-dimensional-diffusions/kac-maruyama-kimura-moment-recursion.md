# Moment recursion for additive path functionals

Let $X$ be a regular diffusion on $[0, 1]$ with infinitesimal mean $\mu$ and variance $\sigma^2$, let $T^*$ be its exit time from $(0, 1)$ and $G(p, \xi)$ its Green's function, so that $E_p[\int_0^{T^*}g(X_s)\,ds] = \int_0^1G(p, \xi)g(\xi)\,d\xi$ for continuous $g$ (Karlin and Taylor 1981, Chapter 15; the [Green-function occupation formula](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md) with $[l, r] = [0, 1]$); write $(Gg)(p)$ for the right side. For continuous $g \ge 0$ let $A = \int_0^{T^*}g(X_s)\,ds$ and $M_n(p) = E_p[A^n]$. Then $M_0 = 1$ and

$$M_n = n\,G(g\,M_{n-1}), \qquad n \ge 1.$$

Derivation: $A^n = n\int_0^{T^*}g(X_t)\bigl(\int_t^{T^*}g(X_s)\,ds\bigr)^{n-1}dt$; by the Markov property at time $t$, the conditional expectation of the inner power on $\{t < T^*\}$ is $M_{n-1}(X_t)$, so $M_n(p) = nE_p\int_0^{T^*}g(X_t)M_{n-1}(X_t)\,dt$, which is the occupation formula applied to $gM_{n-1}$. If $\sup_p(Gg)(p) = c < \infty$, induction gives $M_n \le n!\,c^n$, so $E_p[e^{\lambda A}] < \infty$ for $\lambda < 1/c$. Nagylaki (1974, abstract) derives, for a diallelic locus under the diffusion approximation with any time-independent selection scheme, a formula for the moments of the integral of an arbitrary function of gene frequency along sample paths in terms of sojourn times, and from it the differential equation the moments satisfy; Maruyama and Kimura (1975, abstract) compute any moment of such a sum between two specified frequencies.

## Depends on

- [Green function, occupation times and mean exit times of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Green's representation for a regular diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/diffusion-generator-integral-green-funct.md)
- [Expected occupation integral until absorption, from L₀u = −g](../../../Biology/population-genetics/diffusion-theory/absorption-of-the-neutral-wright-fisher-martinga/integral-absorption-time-of-generator-eq.md)

## Expansion

1. The identity $A^n = n\int_0^{T^*}g(X_t)(\int_t^{T^*}g)^{n-1}\,dt$ for nonnegative $g$.
2. The Markov property at time $t$ and the occupation formula, giving the recursion.
3. Finiteness, the bound $M_n \le n!\,c^n$ by induction, and the exponential moments.
4. The equivalent boundary-value problems $LM_n = -n\,g\,M_{n-1}$ with $M_n(0) = M_n(1) = 0$, and uniqueness of their bounded solutions.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (the Green's function and the occupation formula).
- T. Nagylaki, The moments of stochastic integrals and the distribution of sojourn times, Proc. Natl. Acad. Sci. USA 71 (1974), 746–749, abstract. <https://doi.org/10.1073/pnas.71.3.746>
- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
