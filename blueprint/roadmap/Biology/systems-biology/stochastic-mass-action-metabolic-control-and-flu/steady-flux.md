# Steady-state fluxes along a steady-state map

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, let $f_i \colon \mathbb{R}^M \to \mathbb{R}$ be rate laws and $\sigma \colon \mathbb{R}^R \to \mathbb{R}^M$
a steady-state map. The steady-state fluxes at enzyme levels $e \in \mathbb{R}^R$ are
$J(e) = v(e, \sigma(e))$, that is $J_i(e) = e_i f_i(\sigma(e))$, with $v$ the [fluxes](flux.md).
