# Sign-compatible internal cycle of a flux

A sign-compatible internal cycle of a flux is a nonzero steady combination of internal reactions, each active in the flux and run in the same direction, with no net conversion of any species.

Let $M,R$ be finite, $S\in\mathbb{R}^{M\times R}$, and $R=I\sqcup E$ an internal/exchange split as for [thermodynamically feasible fluxes](thermodynamically-feasible-flux.md). For a flux $v\in\mathbb{R}^R$, a **sign-compatible internal cycle** of $v$ is a vector $k\in\mathbb{R}^R$ with

- $k\ne0$ and $k_r=0$ for every $r\in E$;
- $Sk=0$, that is $\sum_{r\in I}S_{mr}k_r=0$ for every species $m\in M$;
- for every $r\in I$ with $k_r\ne0$: $v_r\ne0$ and $k_rv_r>0$.

The flux $v$ is **loopless** when it admits no sign-compatible internal cycle. Every positive multiple of a sign-compatible internal cycle is one, and whether $v$ is loopless depends only on the sign vector $(\operatorname{sign}v_r)_{r\in I}$.

The balance $Sk=0$ is over all species, including species exchanged with the environment: a cycle of internal reactions that converts an exchanged species (for instance ATP to ADP) is not an internal cycle, and an exchange-driven cycle can therefore be feasible.

## Depends on

- [Thermodynamically feasible flux for given chemical potentials](thermodynamically-feasible-flux.md)

## Proof depends on

None.

## Expansion

With $\Omega_{mr}=-\operatorname{sign}(v_r)S_{mr}$ on the active internal reactions, De Martino et al. describe cycles as nonzero solutions $\kappa\ge0$ of $\Omega\kappa=0$; the correspondence is $k_r=\operatorname{sign}(v_r)\kappa_r$, stated in their Section 2.2.4 as $n_r=\operatorname{sign}(v_r)k_r$. Dependence on signs only: the three conditions mention $v$ only through which $v_r$ vanish and their signs.

In the two-metabolite network of De Martino et al. (internal $A\to B$ and $B\to A$, an intake of $A$ and an outtake of $B$), $k=(1,1,0,0)$ is a sign-compatible internal cycle of $v$ exactly when the two internal fluxes are both positive; with opposite signs neither $k$ nor $-k$ qualifies.

## Sources

- D. De Martino, F. Capuani, M. Mori, A. De Martino and E. Marinari, Counting and correcting thermodynamically infeasible flux cycles in genome-scale metabolic networks, *Metabolites* 3 (2013), 946–966, [doi:10.3390/metabo3040946](https://doi.org/10.3390/metabo3040946): Section 1, Equation (3), and Section 2.2.4, Figure 2 and Equations (8)–(11).
