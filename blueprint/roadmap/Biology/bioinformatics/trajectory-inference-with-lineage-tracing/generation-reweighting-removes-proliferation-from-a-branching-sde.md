# Generation reweighting removes proliferation from a branching SDE

**Setting.** In a branching SDE with gradient drift $-\nabla\Psi$, diffusivity $\tau$, division rate
$b$ and death rate $d$ (with $\|b+d\|_\infty<\infty$), let $\rho_t(m)$ be the intensity of cells of
generation $m$, which solves the generation-structured master equation.

**Corollary 6.** The **reweighted distribution**

$$\bar\rho = \sum_{m\ge0} 2^{-m}\rho(m)$$

solves in the weak sense

$$\partial_t \bar\rho = L^*_{\Psi,\tau}\bar\rho - d\,\bar\rho .$$

In particular, if the death rate is zero and the initial measure $\mu_0$ is a probability measure,
$\bar\rho_t$ equals the law $p_t$ of the underlying non-branching SDE
$dX_t = -\nabla\Psi\,dt + \sqrt\tau\,dB_t$ for all $t$: weighting each observed cell by $2^{-m}$, where $m$
is its number of recorded divisions, deconvolves proliferation exactly, whatever the (unknown) division
rate $b(t,x)$.

## Depends on

- [Generation-structured master equation of a branching SDE](generation-structured-master-equation-of-a-branching-sde.md)

## Expansion

Multiplying the equation for $\rho(m)$ by $2^{-m}$ and summing to $M$, the gain term
$2b\,2^{-m}\rho(m-1) = b\,2^{-(m-1)}\rho(m-1)$ telescopes against the division loss, leaving

$$\partial_t \sum_{m\le M} 2^{-m}\rho(m) = L^*_{\Psi,\tau}\sum_{m\le M}2^{-m}\rho(m) - d\sum_{m\le M}2^{-m}\rho(m) - b\,2^{-M}\rho(M),$$

and the remainder vanishes as $M\to\infty$ because each $\rho_t(m)$ has finite mass. Intuitively, a cell
of generation $m$ is one of $2^m$ descendant lineages of an ancestor, so the weight $2^{-m}$ restores
one unit of mass per ancestral lineage. With deaths or subsampling, the observable generation numbers
undercount divisions and the reweighted measure follows an SDE with a biased drift that depends on
branch survival probabilities.

## Sources

- E. Ventre, A. Forrow, N. Gadhiwala, P. Chakraborty, O. Angel, G. Schiebinger, "Trajectory inference for a branching SDE model of cell differentiation via lineage tracing", Journal of Mathematical Biology 92(5) (2026) 68, <https://doi.org/10.1007/s00285-026-02375-5> (PMC13090286). Section 3.2, Corollary 6 and its proof, Section 5 (bias under death and subsampling, Proposition 9).
