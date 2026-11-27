# Elasticity of a reaction rate

Let $M$ (metabolites) and $R$ (reactions) be index sets with $R$ finite, let $f_i \colon \mathbb{R}^M \to \mathbb{R}$ be rate laws, $e \in \mathbb{R}^R$ enzyme levels,
$s \in \mathbb{R}^M$ concentrations, $i \in R$ and $m \in M$, and let $v_i(e, s) = e_i f_i(s)$ be the
[fluxes](flux.md). The elasticity of $v_i$ with respect to $s_m$ is

$$\varepsilon^{v_i}_{s_m} = \frac{s_m}{v_i(e, s)}\, \frac{\partial v_i}{\partial s_m}(e, s),$$

with quotients by $0$ read as $0$ and the derivative of a map that is not differentiable at the point taken to be $0$. It is meaningful for a nonzero rate and a rate law differentiable at $s$.
