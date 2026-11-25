# Flux connectivity theorem

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, and let $\sigma$ be a [regular steady state](is-regular-steady-state.md) at enzyme levels $e_0$ for a stoichiometric matrix $N$ and rate laws $f$. If every steady-state flux $J_i(e_0)$, $i \in R$, is nonzero,
then for every reaction $j$ and metabolite $m$,

$$\sum_{i \in R} C^{J_j}_{e_i}\, \varepsilon^{v_i}_{s_m} = 0,$$

with the [flux control coefficients](flux-control.md) at $e_0$ and the [elasticities](elasticity.md)
at $(e_0, \sigma(e_0))$ (Kacser & Burns 1973).
