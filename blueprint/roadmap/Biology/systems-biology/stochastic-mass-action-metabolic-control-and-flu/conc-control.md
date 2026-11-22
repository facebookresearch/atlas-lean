# Concentration control coefficient

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, let $\sigma \colon \mathbb{R}^R \to \mathbb{R}^M$ be a steady-state map from enzyme levels to
concentrations, $e \in \mathbb{R}^R$, $m \in M$ and $i \in R$. The concentration control coefficient is

$$C^{s_m}_{e_i} = \frac{e_i}{\sigma_m(e)}\, \frac{\partial \sigma_m}{\partial e_i}(e),$$

with quotients by $0$ read as $0$ and the derivative of a map that is not differentiable at the point taken to be $0$. It is meaningful for a positive concentration $\sigma_m(e)$ and a steady state
differentiable at $e$.
