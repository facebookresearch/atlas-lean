# Flux control coefficient

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, let $f_i \colon \mathbb{R}^M \to \mathbb{R}$ be rate laws, $\sigma \colon \mathbb{R}^R \to \mathbb{R}^M$
a steady-state map, $J(e) = v(e, \sigma(e))$ the [steady-state fluxes](steady-flux.md), $e \in \mathbb{R}^R$
and $i, j \in R$. The flux control coefficient is

$$C^{J_j}_{e_i} = \frac{e_i}{J_j(e)}\, \frac{\partial J_j}{\partial e_i}(e),$$

with quotients by $0$ read as $0$ and the derivative of a map that is not differentiable at the point taken to be $0$. It is meaningful when $J_j(e) \ne 0$ and the steady-state flux is differentiable at
$e$.
